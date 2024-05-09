// mod cpu;
mod cpu;
mod mem;
mod opcodes;
use cpu::Cpu;
use mem::Mem;
use opcodes::opcodes::*;

fn main() {
    let mut memory = Mem::new();
    let mut cpu = Cpu::new();

    // Write a program to test the ROL instruction
    memory.write(0x8000, INS_LDA_IM); // Load value 0b1000_0000 into accumulator
    memory.write(0x8001, 0x80);
    memory.write(0x8002, INS_ROL_A); // Rotate accumulator left
    memory.write(0x8003, INS_RTS); // Return from subroutine

    // Set the program counter to the start of the program.
    cpu.pc = 0x8000;

    // Enough cycles to execute LDA, ROL, and RTS
    let mut cycles: u32 = 10;
    cpu.c = true;
    cpu.execute(&mut memory, &mut cycles);

    println!("Accumulator after ROL: {:#x}", cpu.a);
    println!("Zero Flag: {}", cpu.z);
    println!("Negative Flag: {}", cpu.n);
}
