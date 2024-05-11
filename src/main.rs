mod cpu;
mod mem;
mod opcodes;

use cpu::Cpu;
use mem::Mem;
use opcodes::Opcode;

fn main() {
    let mut memory = Mem::new();
    let mut cpu = Cpu::new();

    // Program setup
    let program = [
        Opcode::LdaIm as u8,
        0x01, // LDA #0x01
        Opcode::LdxIm as u8,
        0x02, // LDX #0x02
        Opcode::LdyIm as u8,
        0x03, // LDY #0x03
        Opcode::StaAbs as u8,
        0x20,
        0x00, // STA $0020
        Opcode::StxAbs as u8,
        0x21,
        0x00, // STX $0021
        Opcode::StyAbs as u8,
        0x22,
        0x00, // STY $0022
        Opcode::Jsr as u8,
        0x30,
        0x80,              // JSR $8030
        Opcode::Nop as u8, // NOP (Subroutine)
        Opcode::Rts as u8, // RTS
    ];

    // Load the program into memory starting at 0x8000
    let mut address = 0x8000;
    for &byte in &program {
        memory.write(address, byte);
        address += 1;
    }

    // Set the program counter to the start of the program.
    cpu.pc = 0x8000;

    // Set up enough cycles to execute the program
    let mut cycles: u32 = 50; // Assign a number of cycles that is enough to run the program

    while cycles > 0 && cpu.pc < 0x8000 + program.len() as u16 {
        let opcode_byte = memory.get_byte(cpu.pc as usize);
        cpu.pc += 1; // Increment PC to point to the next byte
        if let Some(opcode) = Opcode::from_byte(opcode_byte) {
            cpu.execute_instruction(opcode, &mut memory, &mut cycles);
        } else {
            eprintln!("Unknown opcode: {:#x} at PC: {}", opcode_byte, cpu.pc - 1);
            break;
        }
    }

    // Output the results
    println!("Value in A: {:#x}", cpu.a);
    println!("Value in X: {:#x}", cpu.x);
    println!("Value in Y: {:#x}", cpu.y);
    println!("Value at 0x0020: {:#x}", memory.get_byte(0x0020));
    println!("Value at 0x0021: {:#x}", memory.get_byte(0x0021));
    println!("Value at 0x0022: {:#x}", memory.get_byte(0x0022));
    println!("Remaining cycles: {}", cycles);
}
