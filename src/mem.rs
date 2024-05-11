use crate::cpu::Cpu;

// Memory size for the 6502 processor which can address 64KB.
const MAX_MEM: usize = 1024 * 64;

// Memory struct emulates the RAM of the 6502 CPU.
pub struct Mem {
    pub data: [u8; MAX_MEM],
}

impl Mem {
    // Constructor for Mem struct, initializes memory with zeroes.
    pub fn new() -> Mem {
        Mem { data: [0; MAX_MEM] }
    }

    // Write a byte of data to a specified memory address.
    pub fn write(&mut self, address: usize, data: u8) {
        self.data[address] = data;
    }

    pub fn get_byte(&self, address: usize) -> u8 {
        // Safely access memory with bounds checking
        if address < self.data.len() {
            self.data[address]
        } else {
            // Handle out-of-bounds access, perhaps by returning 0 or some error indication
            0
        }
    }
    // Reads a byte from memory at the current program counter and increments the counter.
    pub fn read_byte(&mut self, cycles: &mut u32, cpu: &mut Cpu) -> u8 {
        // Fetch the byte from memory.
        let data = self.data[cpu.pc as usize];
        // Increment the program counter.
        cpu.pc = cpu.pc.wrapping_add(1);
        // Decrement the cycle counter.
        *cycles = cycles.wrapping_sub(1);
        data
    }

    // Read a 16-bit word from memory at the current program counter using little endian format.
    pub fn read_word(&mut self, cycles: &mut u32, cpu: &mut Cpu) -> u16 {
        // Fetch the low byte.
        let low = self.data[cpu.pc as usize] as u16;
        cpu.pc = cpu.pc.wrapping_add(1);

        // Fetch the high byte and shift.
        let high = (self.data[cpu.pc as usize] as u16) << 8;
        cpu.pc = cpu.pc.wrapping_add(1);

        *cycles = cycles.wrapping_sub(2);
        // Combine the low and high bytes.
        low | high
    }

    // Pushes a byte onto the stack and decrement the stack pointer.
    pub fn push_stack(&mut self, cycles: &mut u32, cpu: &mut Cpu, value: u8) {
        // Calculate the stack address.
        let sp_address = 0x0100 + cpu.sp as usize;
        cpu.sp = cpu.sp.wrapping_sub(1);
        // Write the byte to the stack address.
        self.write(sp_address, value);

        *cycles = cycles.wrapping_sub(1);
    }

    // Pushes a 16-bit word onto the stack in two parts (high byte first).
    pub fn push_stack_word(&mut self, cycles: &mut u32, cpu: &mut Cpu, value: u16) {
        // Push low byte.
        self.push_stack(cycles, cpu, (value >> 8) as u8);
        // Push high byte.
        self.push_stack(cycles, cpu, (value & 0xFF) as u8);
    }

    // Pulls a byte from the stack and increments the stack pointer.
    pub fn pull_stack(&mut self, cycles: &mut u32, cpu: &mut Cpu) -> u8 {
        let sp_address = 0x0100 + cpu.sp as usize;
        cpu.sp = cpu.sp.wrapping_add(1);
        *cycles = cycles.wrapping_sub(1);
        // Return the byte from the stack.
        self.data[sp_address]
    }

    // Pulls a 16-bit word from the stack (low byte first).
    pub fn pull_stack_word(&mut self, cycles: &mut u32, cpu: &mut Cpu) -> u16 {
        let low_byte = self.pull_stack(cycles, cpu) as u16;
        let high_byte = self.pull_stack(cycles, cpu) as u16;
        (high_byte << 8) | low_byte
    }
}
