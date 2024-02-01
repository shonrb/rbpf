fn main() {
    let prog = &[
        0x71, 0x10, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, // ldxh r0, [r1+2]
        0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00  // exit
    ];

    // Let's use some data.
    let mem = &mut [
        0xaa, 0xbb, 0x11, 0xcc, 0xdd
    ];

    // This is an eBPF VM for programs reading from a given memory area (it
    // directly reads from packet data)
    let vm = rbpf::EbpfVmRaw::new(Some(prog));

    assert_eq!(vm.execute_program(mem).unwrap(), 0x11);
}

