// SPDX-License-Identifier: (Apache-2.0 OR MIT)
// Derived from uBPF <https://github.com/iovisor/ubpf>
// Copyright 2016 6WIND S.A. <quentin.monnet@6wind.com>
// Copyright 2023 Isovalent, Inc. <quentin@isovalent.com>

//! Virtual machine and JIT compiler for eBPF programs.
#![no_std]
#![doc(
    html_logo_url = "https://raw.githubusercontent.com/qmonnet/rbpf/main/misc/rbpf.png",
    html_favicon_url = "https://raw.githubusercontent.com/qmonnet/rbpf/main/misc/rbpf.ico"
)]
// Test examples from README.md as part as doc tests.
#![doc = core::include_str!("../README.md")]
#![warn(missing_docs)]
// There are unused mut warnings due to unsafe code.
#![allow(unused_mut)]
// Allows old-style clippy
#![allow(renamed_and_removed_lints)]
#![cfg_attr(
    feature = "cargo-clippy",
    allow(
        redundant_field_names,
        single_match,
        cast_lossless,
        doc_markdown,
        match_same_arms,
        unreadable_literal
    )
)]

pub mod ebpf;
mod interpreter;

use heapless::{FnvIndexMap, Vec};
use interpreter::Error;

/// eBPF helper function.
pub type Helper = fn(u64, u64, u64, u64, u64) -> u64;

// A metadata buffer with two offset indications. It can be used in one kind of eBPF VM to simulate
// the use of a metadata buffer each time the program is executed, without the user having to
// actually handle it. The offsets are used to tell the VM where in the buffer the pointers to
// packet data start and end should be stored each time the program is run on a new packet.
struct MetaBuff {
    data_offset: usize,
    data_end_offset: usize,
    buffer: Vec<u8, 1024>,
}

/// A virtual machine to run eBPF program. This kind of VM is used for programs expecting to work
/// on a metadata buffer containing pointers to packet data.
///
/// # Examples
///
/// ```
/// let prog = &[
///     0x79, 0x11, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, // Load mem from mbuff at offset 8 into R1.
///     0x69, 0x10, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, // ldhx r1[2], r0
///     0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00  // exit
/// ];
/// let mem = &mut [
///     0xaa, 0xbb, 0x11, 0x22, 0xcc, 0xdd
/// ];
///
/// // Just for the example we create our metadata buffer from scratch, and we store the pointers
/// // to packet data start and end in it.
/// let mut mbuff = [0u8; 32];
/// unsafe {
///     let mut data     = mbuff.as_ptr().offset(8)  as *mut u64;
///     let mut data_end = mbuff.as_ptr().offset(24) as *mut u64;
///     *data     = mem.as_ptr() as u64;
///     *data_end = mem.as_ptr() as u64 + mem.len() as u64;
/// }
///
/// // Instantiate a VM.
/// let mut vm = rbpf::EbpfVmMbuff::new(Some(prog)).unwrap();
///
/// // Provide both a reference to the packet data, and to the metadata buffer.
/// let res = vm.execute_program(mem, &mut mbuff).unwrap();
/// assert_eq!(res, 0x2211);
/// ```
pub struct EbpfVmMbuff<'a> {
    prog: Option<&'a [u8]>,
    helpers: FnvIndexMap<u32, ebpf::Helper, 128>,
}

impl<'a> EbpfVmMbuff<'a> {
    /// Create a new virtual machine instance, and load an eBPF program into that instance.
    /// When attempting to load the program, it passes through a simple verifier.
    ///
    /// # Examples
    ///
    /// ```
    /// let prog = &[
    ///     0x79, 0x11, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, // Load mem from mbuff into R1.
    ///     0x69, 0x10, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, // ldhx r1[2], r0
    ///     0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00  // exit
    /// ];
    ///
    /// // Instantiate a VM.
    /// let mut vm = rbpf::EbpfVmMbuff::new(Some(prog)).unwrap();
    /// ```
    pub fn new(prog: Option<&'a [u8]>) -> EbpfVmMbuff<'a> {
        EbpfVmMbuff {
            prog,
            helpers: FnvIndexMap::new(),
        }
    }

    /// Load a new eBPF program into the virtual machine instance.
    ///
    /// # Examples
    ///
    /// ```
    /// let prog1 = &[
    ///     0xb7, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // mov r0, 0
    ///     0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00  // exit
    /// ];
    /// let prog2 = &[
    ///     0x79, 0x11, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, // Load mem from mbuff into R1.
    ///     0x69, 0x10, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, // ldhx r1[2], r0
    ///     0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00  // exit
    /// ];
    ///
    /// // Instantiate a VM.
    /// let mut vm = rbpf::EbpfVmMbuff::new(Some(prog1)).unwrap();
    /// vm.set_program(prog2).unwrap();
    /// ```
    pub fn set_program(&mut self, prog: &'a [u8]) {
        self.prog = Some(prog);
    }


    /// Register a built-in or user-defined helper function in order to use it later from within
    /// the eBPF program. The helper is registered into a hashmap, so the `key` can be any `u32`.
    ///
    /// If using JIT-compiled eBPF programs, be sure to register all helpers before compiling the
    /// program. You should be able to change registered helpers after compiling, but not to add
    /// new ones (i.e. with new keys).
    ///
    /// # Examples
    ///
    /// ```
    /// use rbpf::helpers;
    ///
    /// // This program was compiled with clang, from a C program containing the following single
    /// // instruction: `return bpf_trace_printk("foo %c %c %c\n", 10, 1, 2, 3);`
    /// let prog = &[
    ///     0x18, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // load 0 as u64 into r1 (That would be
    ///     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // replaced by tc by the address of
    ///                                                     // the format string, in the .map
    ///                                                     // section of the ELF file).
    ///     0xb7, 0x02, 0x00, 0x00, 0x0a, 0x00, 0x00, 0x00, // mov r2, 10
    ///     0xb7, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, // mov r3, 1
    ///     0xb7, 0x04, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, // mov r4, 2
    ///     0xb7, 0x05, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, // mov r5, 3
    ///     0x85, 0x00, 0x00, 0x00, 0x06, 0x00, 0x00, 0x00, // call helper with key 6
    ///     0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00  // exit
    /// ];
    ///
    /// // Instantiate a VM.
    /// let mut vm = rbpf::EbpfVmMbuff::new(Some(prog)).unwrap();
    ///
    /// // Register a helper.
    /// // On running the program this helper will print the content of registers r3, r4 and r5 to
    /// // standard output.
    /// vm.register_helper(6, helpers::bpf_trace_printf).unwrap();
    /// ```
    pub fn register_helper(&mut self, key: u32, function: Helper) {
        self.helpers.insert(key, function);
    }

    /// Execute the program loaded, with the given packet data and metadata buffer.
    ///
    /// If the program is made to be compatible with Linux kernel, it is expected to load the
    /// address of the beginning and of the end of the memory area used for packet data from the
    /// metadata buffer, at some appointed offsets. It is up to the user to ensure that these
    /// pointers are correctly stored in the buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// let prog = &[
    ///     0x79, 0x11, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, // Load mem from mbuff into R1.
    ///     0x69, 0x10, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, // ldhx r1[2], r0
    ///     0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00  // exit
    /// ];
    /// let mem = &mut [
    ///     0xaa, 0xbb, 0x11, 0x22, 0xcc, 0xdd
    /// ];
    ///
    /// // Just for the example we create our metadata buffer from scratch, and we store the
    /// // pointers to packet data start and end in it.
    /// let mut mbuff = [0u8; 32];
    /// unsafe {
    ///     let mut data     = mbuff.as_ptr().offset(8)  as *mut u64;
    ///     let mut data_end = mbuff.as_ptr().offset(24) as *mut u64;
    ///     *data     = mem.as_ptr() as u64;
    ///     *data_end = mem.as_ptr() as u64 + mem.len() as u64;
    /// }
    ///
    /// // Instantiate a VM.
    /// let mut vm = rbpf::EbpfVmMbuff::new(Some(prog)).unwrap();
    ///
    /// // Provide both a reference to the packet data, and to the metadata buffer.
    /// let res = vm.execute_program(mem, &mut mbuff).unwrap();
    /// assert_eq!(res, 0x2211);
    /// ```
    pub fn execute_program(&self, mem: &[u8], mbuff: &[u8]) -> u64 {
        interpreter::execute_program(self.prog, mem, mbuff, &self.helpers)
    }
}

/// A virtual machine to run eBPF program. This kind of VM is used for programs expecting to work
/// on a metadata buffer containing pointers to packet data, but it internally handles the buffer
/// so as to save the effort to manually handle the metadata buffer for the user.
///
/// This struct implements a static internal buffer that is passed to the program. The user has to
/// indicate the offset values at which the eBPF program expects to find the start and the end of
/// packet data in the buffer. On calling the `execute_program()` or `execute_program_jit()` functions, the
/// struct automatically updates the addresses in this static buffer, at the appointed offsets, for
/// the start and the end of the packet data the program is called upon.
///
/// # Examples
///
/// This was compiled with clang from the following program, in C:
///
/// ```c
/// #include <linux/bpf.h>
/// #include "path/to/linux/samples/bpf/bpf_helpers.h"
///
/// SEC(".classifier")
/// int classifier(struct __sk_buff *skb)
/// {
///   void *data = (void *)(long)skb->data;
///   void *data_end = (void *)(long)skb->data_end;
///
///   // Check program is long enough.
///   if (data + 5 > data_end)
///     return 0;
///
///   return *((char *)data + 5);
/// }
/// ```
///
/// Some small modifications have been brought to have it work, see comments.
///
/// ```
/// let prog = &[
///     0xb7, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // mov r0, 0
///     // Here opcode 0x61 had to be replace by 0x79 so as to load a 8-bytes long address.
///     // Also, offset 0x4c had to be replace with e.g. 0x40 so as to prevent the two pointers
///     // from overlapping in the buffer.
///     0x79, 0x12, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, // load pointer to mem from r1[0x40] to r2
///     0x07, 0x02, 0x00, 0x00, 0x05, 0x00, 0x00, 0x00, // add r2, 5
///     // Here opcode 0x61 had to be replace by 0x79 so as to load a 8-bytes long address.
///     0x79, 0x11, 0x50, 0x00, 0x00, 0x00, 0x00, 0x00, // load ptr to mem_end from r1[0x50] to r1
///     0x2d, 0x12, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, // if r2 > r1 skip 3 instructions
///     0x71, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // load r2 (= *(mem + 5)) into r0
///     0x67, 0x00, 0x00, 0x00, 0x38, 0x00, 0x00, 0x00, // r0 >>= 56
///     0xc7, 0x00, 0x00, 0x00, 0x38, 0x00, 0x00, 0x00, // r0 <<= 56 (arsh) extend byte sign to u64
///     0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00  // exit
/// ];
/// let mem1 = &mut [
///     0xaa, 0xbb, 0x11, 0x22, 0xcc, 0xdd
/// ];
/// let mem2 = &mut [
///     0xaa, 0xbb, 0x11, 0x22, 0xcc, 0x27
/// ];
///
/// // Instantiate a VM. Note that we provide the start and end offsets for mem pointers.
/// let mut vm = rbpf::EbpfVmFixedMbuff::new(Some(prog), 0x40, 0x50).unwrap();
///
/// // Provide only a reference to the packet data. We do not manage the metadata buffer.
/// let res = vm.execute_program(mem1).unwrap();
/// assert_eq!(res, 0xffffffffffffffdd);
///
/// let res = vm.execute_program(mem2).unwrap();
/// assert_eq!(res, 0x27);
/// ```

/// A virtual machine to run eBPF program. This kind of VM is used for programs expecting to work
/// directly on the memory area representing packet data.
///
/// # Examples
///
/// ```
/// let prog = &[
///     0x71, 0x11, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, // ldxb r1[0x04], r1
///     0x07, 0x01, 0x00, 0x00, 0x00, 0x22, 0x00, 0x00, // add r1, 0x22
///     0xbf, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // mov r0, r1
///     0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00  // exit
/// ];
/// let mem = &mut [
///     0xaa, 0xbb, 0x11, 0x22, 0xcc, 0xdd
/// ];
///
/// // Instantiate a VM.
/// let vm = rbpf::EbpfVmRaw::new(Some(prog)).unwrap();
///
/// // Provide only a reference to the packet data.
/// let res = vm.execute_program(mem).unwrap();
/// assert_eq!(res, 0x22cc);
/// ```
pub struct EbpfVmRaw<'a> {
    parent: EbpfVmMbuff<'a>,
}

impl<'a> EbpfVmRaw<'a> {
    /// Create a new virtual machine instance, and load an eBPF program into that instance.
    /// When attempting to load the program, it passes through a simple verifier.
    ///
    /// # Examples
    ///
    /// ```
    /// let prog = &[
    ///     0x71, 0x11, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, // ldxb r1[0x04], r1
    ///     0x07, 0x01, 0x00, 0x00, 0x00, 0x22, 0x00, 0x00, // add r1, 0x22
    ///     0xbf, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // mov r0, r1
    ///     0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00  // exit
    /// ];
    ///
    /// // Instantiate a VM.
    /// let vm = rbpf::EbpfVmRaw::new(Some(prog)).unwrap();
    /// ```
    pub fn new(prog: Option<&'a [u8]>) -> Result<EbpfVmRaw<'a>, Error> {
        let parent = EbpfVmMbuff::new(prog)?;
        Ok(EbpfVmRaw { parent })
    }

    /// Load a new eBPF program into the virtual machine instance.
    ///
    /// # Examples
    ///
    /// ```
    /// let prog1 = &[
    ///     0xb7, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // mov r0, 0
    ///     0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00  // exit
    /// ];
    /// let prog2 = &[
    ///     0x71, 0x11, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, // ldxb r1[0x04], r1
    ///     0x07, 0x01, 0x00, 0x00, 0x00, 0x22, 0x00, 0x00, // add r1, 0x22
    ///     0xbf, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // mov r0, r1
    ///     0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00  // exit
    /// ];
    ///
    /// let mem = &mut [
    ///     0xaa, 0xbb, 0x11, 0x22, 0xcc, 0x27,
    /// ];
    ///
    /// let mut vm = rbpf::EbpfVmRaw::new(Some(prog1)).unwrap();
    /// vm.set_program(prog2);
    ///
    /// let res = vm.execute_program(mem).unwrap();
    /// assert_eq!(res, 0x22cc);
    /// ```
    pub fn set_program(&mut self, prog: &'a [u8]) -> Result<(), Error> {
        self.parent.set_program(prog)?;
        Ok(())
    }

    /// Set a new verifier function. The function should return an `Error` if the program should be
    /// rejected by the virtual machine. If a program has been loaded to the VM already, the
    /// verifier is immediately run.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::io::{Error, ErrorKind};
    /// use rbpf::ebpf;
    ///
    /// // Define a simple verifier function.
    /// fn verifier(prog: &[u8]) -> Result<(), Error> {
    ///     let last_insn = ebpf::get_insn(prog, (prog.len() / ebpf::INSN_SIZE) - 1);
    ///     if last_insn.opc != ebpf::EXIT {
    ///         return Err(Error::new(ErrorKind::Other,
    ///                    "[Verifier] Error: program does not end with “EXIT” instruction"));
    ///     }
    ///     Ok(())
    /// }
    ///
    /// let prog1 = &[
    ///     0xb7, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // mov r0, 0
    ///     0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00  // exit
    /// ];
    ///
    /// // Instantiate a VM.
    /// let mut vm = rbpf::EbpfVmMbuff::new(Some(prog1)).unwrap();
    /// // Change the verifier.
    /// vm.set_verifier(verifier).unwrap();
    /// ```

    /// Register a built-in or user-defined helper function in order to use it later from within
    /// the eBPF program. The helper is registered into a hashmap, so the `key` can be any `u32`.
    ///
    /// If using JIT-compiled eBPF programs, be sure to register all helpers before compiling the
    /// program. You should be able to change registered helpers after compiling, but not to add
    /// new ones (i.e. with new keys).
    ///
    /// # Examples
    ///
    /// ```
    /// use rbpf::helpers;
    ///
    /// let prog = &[
    ///     0x79, 0x11, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // ldxdw r1, r1[0x00]
    ///     0xb7, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // mov r2, 0
    ///     0xb7, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // mov r3, 0
    ///     0xb7, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // mov r4, 0
    ///     0xb7, 0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // mov r5, 0
    ///     0x85, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, // call helper with key 1
    ///     0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00  // exit
    /// ];
    ///
    /// let mem = &mut [
    ///     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01
    /// ];
    ///
    /// // Instantiate a VM.
    /// let mut vm = rbpf::EbpfVmRaw::new(Some(prog)).unwrap();
    ///
    /// // Register a helper. This helper will store the result of the square root of r1 into r0.
    /// vm.register_helper(1, helpers::sqrti);
    ///
    /// let res = vm.execute_program(mem).unwrap();
    /// assert_eq!(res, 0x10000000);
    /// ```
    pub fn register_helper(
        &mut self,
        key: u32,
        function: fn(u64, u64, u64, u64, u64) -> u64,
    ) {
        self.parent.register_helper(key, function)
    }

    /// Execute the program loaded, with the given packet data.
    ///
    /// # Examples
    ///
    /// ```
    /// let prog = &[
    ///     0x71, 0x11, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, // ldxb r1[0x04], r1
    ///     0x07, 0x01, 0x00, 0x00, 0x00, 0x22, 0x00, 0x00, // add r1, 0x22
    ///     0xbf, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // mov r0, r1
    ///     0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00  // exit
    /// ];
    ///
    /// let mem = &mut [
    ///     0xaa, 0xbb, 0x11, 0x22, 0xcc, 0x27
    /// ];
    ///
    /// let mut vm = rbpf::EbpfVmRaw::new(Some(prog)).unwrap();
    ///
    /// let res = vm.execute_program(mem).unwrap();
    /// assert_eq!(res, 0x22cc);
    /// ```
    pub fn execute_program(&self, mem: &'a mut [u8]) {
        self.parent.execute_program(mem, &[])
    }
}

/// A virtual machine to run eBPF program. This kind of VM is used for programs that do not work
/// with any memory area—no metadata buffer, no packet data either.
///
/// # Examples
///
/// ```
/// let prog = &[
///     0xb7, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // mov r0, 0
///     0xb7, 0x01, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, // mov r1, 1
///     0xb7, 0x02, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, // mov r2, 2
///     0xb7, 0x03, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, // mov r3, 3
///     0xb7, 0x04, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, // mov r4, 4
///     0xb7, 0x05, 0x00, 0x00, 0x05, 0x00, 0x00, 0x00, // mov r5, 5
///     0xb7, 0x06, 0x00, 0x00, 0x06, 0x00, 0x00, 0x00, // mov r6, 6
///     0xb7, 0x07, 0x00, 0x00, 0x07, 0x00, 0x00, 0x00, // mov r7, 7
///     0xb7, 0x08, 0x00, 0x00, 0x08, 0x00, 0x00, 0x00, // mov r8, 8
///     0x4f, 0x50, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // or r0, r5
///     0x47, 0x00, 0x00, 0x00, 0xa0, 0x00, 0x00, 0x00, // or r0, 0xa0
///     0x57, 0x00, 0x00, 0x00, 0xa3, 0x00, 0x00, 0x00, // and r0, 0xa3
///     0xb7, 0x09, 0x00, 0x00, 0x91, 0x00, 0x00, 0x00, // mov r9, 0x91
///     0x5f, 0x90, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // and r0, r9
///     0x67, 0x00, 0x00, 0x00, 0x20, 0x00, 0x00, 0x00, // lsh r0, 32
///     0x67, 0x00, 0x00, 0x00, 0x16, 0x00, 0x00, 0x00, // lsh r0, 22
///     0x6f, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // lsh r0, r8
///     0x77, 0x00, 0x00, 0x00, 0x20, 0x00, 0x00, 0x00, // rsh r0, 32
///     0x77, 0x00, 0x00, 0x00, 0x13, 0x00, 0x00, 0x00, // rsh r0, 19
///     0x7f, 0x70, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // rsh r0, r7
///     0xa7, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, // xor r0, 0x03
///     0xaf, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // xor r0, r2
///     0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00  // exit
/// ];
///
/// // Instantiate a VM.
/// let vm = rbpf::EbpfVmNoData::new(Some(prog)).unwrap();
///
/// // Provide only a reference to the packet data.
/// let res = vm.execute_program().unwrap();
/// assert_eq!(res, 0x11);
/// ```
pub struct EbpfVmNoData<'a> {
    parent: EbpfVmRaw<'a>,
}

impl<'a> EbpfVmNoData<'a> {
    /// Create a new virtual machine instance, and load an eBPF program into that instance.
    /// When attempting to load the program, it passes through a simple verifier.
    ///
    /// # Examples
    ///
    /// ```
    /// let prog = &[
    ///     0xb7, 0x00, 0x00, 0x00, 0x11, 0x22, 0x00, 0x00, // mov r0, 0x2211
    ///     0xdc, 0x00, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, // be16 r0
    ///     0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00  // exit
    /// ];
    ///
    /// // Instantiate a VM.
    /// let vm = rbpf::EbpfVmNoData::new(Some(prog));
    /// ```
    pub fn new(prog: Option<&'a [u8]>) -> Result<EbpfVmNoData<'a>, Error> {
        let parent = EbpfVmRaw::new(prog)?;
        Ok(EbpfVmNoData { parent })
    }

    /// Load a new eBPF program into the virtual machine instance.
    ///
    /// # Examples
    ///
    /// ```
    /// let prog1 = &[
    ///     0xb7, 0x00, 0x00, 0x00, 0x11, 0x22, 0x00, 0x00, // mov r0, 0x2211
    ///     0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00  // exit
    /// ];
    /// let prog2 = &[
    ///     0xb7, 0x00, 0x00, 0x00, 0x11, 0x22, 0x00, 0x00, // mov r0, 0x2211
    ///     0xdc, 0x00, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, // be16 r0
    ///     0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00  // exit
    /// ];
    ///
    /// let mut vm = rbpf::EbpfVmNoData::new(Some(prog1)).unwrap();
    ///
    /// let res = vm.execute_program().unwrap();
    /// assert_eq!(res, 0x2211);
    ///
    /// vm.set_program(prog2);
    ///
    /// let res = vm.execute_program().unwrap();
    /// assert_eq!(res, 0x1122);
    /// ```
    pub fn set_program(&mut self, prog: &'a [u8]) -> Result<(), Error> {
        self.parent.set_program(prog)?;
        Ok(())
    }


    /// Register a built-in or user-defined helper function in order to use it later from within
    /// the eBPF program. The helper is registered into a hashmap, so the `key` can be any `u32`.
    ///
    /// If using JIT-compiled eBPF programs, be sure to register all helpers before compiling the
    /// program. You should be able to change registered helpers after compiling, but not to add
    /// new ones (i.e. with new keys).
    ///
    /// # Examples
    ///
    /// ```
    /// use rbpf::helpers;
    ///
    /// let prog = &[
    ///     0xb7, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, // mov r1, 0x010000000
    ///     0xb7, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // mov r2, 0
    ///     0xb7, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // mov r3, 0
    ///     0xb7, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // mov r4, 0
    ///     0xb7, 0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // mov r5, 0
    ///     0x85, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, // call helper with key 1
    ///     0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00  // exit
    /// ];
    ///
    /// let mut vm = rbpf::EbpfVmNoData::new(Some(prog)).unwrap();
    ///
    /// // Register a helper. This helper will store the result of the square root of r1 into r0.
    /// vm.register_helper(1, helpers::sqrti).unwrap();
    ///
    /// let res = vm.execute_program().unwrap();
    /// assert_eq!(res, 0x1000);
    /// ```
    pub fn register_helper(
        &mut self,
        key: u32,
        function: fn(u64, u64, u64, u64, u64) -> u64,
    ) {
        self.parent.register_helper(key, function)
    }

    /// Execute the program loaded, without providing pointers to any memory area whatsoever.
    ///
    /// # Examples
    ///
    /// ```
    /// let prog = &[
    ///     0xb7, 0x00, 0x00, 0x00, 0x11, 0x22, 0x00, 0x00, // mov r0, 0x2211
    ///     0xdc, 0x00, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, // be16 r0
    ///     0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00  // exit
    /// ];
    ///
    /// let vm = rbpf::EbpfVmNoData::new(Some(prog)).unwrap();
    ///
    /// // For this kind of VM, the `execute_program()` function needs no argument.
    /// let res = vm.execute_program().unwrap();
    /// assert_eq!(res, 0x1122);
    /// ```
    pub fn execute_program(&self) -> Result<u64, Error> {
        self.parent.execute_program(&mut [])
    }
}
