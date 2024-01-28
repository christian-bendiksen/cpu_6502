// Memory size for the 6502 processor which can address 64KB.
const MAX_MEM: usize = 1024 * 64;

// Opcodes for various 6502 assembly instructions.
const INS_LDA_IM: u8 = 0xA9; // Opcode for LDA with immediate addressing mode.
const INS_LDA_ZP: u8 = 0xA5; // Opcode for LDA with zero-page addressing mode.
const INS_LDA_ZPX: u8 = 0xB5; // Opcode for LDA with zero-page,X addressing mode.
const INS_JSR: u8 = 0x20; // Opcode for Jump to Subroutine
const INS_RTS: u8 = 0x60; // Opcode for Return from Soubroutine

// Memory struct emulates the RAM of the 6502 CPU.
struct Mem {
    data: [u8; MAX_MEM],
}

impl Mem {
    // Constructor for Mem struct, initializes memory with zeroes.
    fn new() -> Mem {
        Mem { data: [0; MAX_MEM] }
    }

    // Write a byte of data to a specified memory address.
    fn write(&mut self, address: usize, data: u8) {
        self.data[address] = data;
    }
}

// CPU struct represents the state of the CPU including registers and flags.
struct CPU {
    pc: u16, // Program counter: points to the next instruction to execute.
    sp: u16, // Stack pointer: points to the top of the stack.
    a: u8,   // Accumulator: used for arithmetic and logic operations.
    x: u8,   // X index register.
    y: u8,   // Y index register.
    // Processor status flags:
    c: bool, // Carry flag.
    z: bool, // Zero flag.
    i: bool, // Interrupt disable flag.
    d: bool, // Decimal mode flag.
    b: bool, // Break command flag.
    v: bool, // Overflow flag.
    n: bool, // Negative flag.
}

impl CPU {
    // Constructs a new CPU with initial state.
    fn new() -> CPU {
        CPU {
            pc: 0xFFFD,
            sp: 0x0100,
            a: 0,
            x: 0,
            y: 0,
            c: false,
            z: false,
            i: false,
            d: false,
            b: false,
            v: false,
            n: false,
        }
    }

    #[allow(dead_code)]
    // Resets the CPU to its initial state
    fn reset(&mut self) {
        self.pc = 0xFFFC;
        self.sp = 0x0100;
        self.a = 0;
        self.x = 0;
        self.y = 0;
        self.c = false;
        self.z = false;
        self.i = false;
        self.d = false;
        self.b = false;
        self.v = false;
        self.n = false;
    }

    // Reads a byte from memory at the current program counter and increments the counter.
    fn read_byte(&mut self, cycles: &mut u32, memory: &Mem) -> u8 {
        // Fetch the byte from memory.
        let data = memory.data[self.pc as usize];
        // Increment the program counter.
        self.pc = self.pc.wrapping_add(1);
        // Decrement the cycle counter.
        *cycles = cycles.saturating_sub(1);
        data
    }

    // Read a 16-bit word from memory at the current program counter using little endian format.
    fn read_word(&mut self, cycles: &mut u32, memory: &Mem) -> u16 {
        // Fetch the low byte.
        let low = memory.data[self.pc as usize] as u16;
        self.pc = self.pc.wrapping_add(1);

        // Fetch the high byte and shift.
        let high = (memory.data[self.pc as usize] as u16) << 8;
        self.pc = self.pc.wrapping_add(1);

        *cycles = cycles.saturating_sub(2);
        // Combine the low and high bytes.
        low | high
    }

    // Pushes a byte onto the stack and decrement the stack pointer.
    fn push_stack(&mut self, memory: &mut Mem, value: u8) {
        // Calculate the stack address.
        let sp_address = 0x0100 + self.sp as usize;
        self.sp = self.sp.wrapping_sub(1);
        // Write the byte to the stack address.
        memory.write(sp_address, value);
    }

    // Pushes a 16-bit word onto the stack in two parts (high byte first).
    fn push_stack_word(&mut self, memory: &mut Mem, value: u16) {
        // Push low byte.
        self.push_stack(memory, (value >> 8) as u8);
        // Push high byte.
        self.push_stack(memory, (value & 0xFF) as u8);
    }

    // Pulls a byte from the stack and increments the stack pointer.
    fn pull_stack(&mut self, memory: &Mem) -> u8 {
        let sp_address = 0x0100 + self.sp as usize;
        self.sp = self.sp.wrapping_add(1);
        // Return the byte from the stack.
        memory.data[sp_address]
    }

    // Pulls a 16-bit word from the stack (low byte first).
    fn pull_stack_word(&mut self, memory: &Mem) -> u16 {
        let low_byte = self.pull_stack(memory) as u16;
        let high_byte = self.pull_stack(memory) as u16;
        (high_byte << 8) | low_byte
    }

    // Sets the Zero and Negative flags depending on the accumulator's state.
    fn set_default_flags(&mut self) {
        // Set Zero flag if accumulator is zero.
        self.z = self.a == 0;
        // Set Negative flag based on high bit of accumulator.
        self.n = (self.a & 0b1000_0000) != 0;
    }

    // Execute CPU instructions.
    // This function drives the CPU's execution based on the opcodes.
    //
    // Arguments:
    // * `memory`: mutable reference to the CPU's memory.
    // * `cycles`: mutable reference to the number of cycles remaining for the CPU to execute.
    fn execute(&mut self, memory: &mut Mem, cycles: &mut u32) {
        // Continue executing while we have cycles left.
        while *cycles > 0 {
            // Read the next opcode from memory at the current program counter.
            let ins = self.read_byte(cycles, memory);

            match ins {
                // Handle LDA with Immediate addressing mode.
                INS_LDA_IM => {
                    // Read the next byte from memory, which is the immediate value for LDA.
                    let value = self.read_byte(cycles, memory);
                    // Load the read value into the accumulator.
                    self.a = value;
                    // Update the Zero and Negative flags based on the new accumulator value.
                    self.set_default_flags();
                }
                // Handle LDA with Zero Page addressing mode.
                INS_LDA_ZP => {
                    let zero_page_address = self.read_byte(cycles, memory) as usize;
                    self.a = memory.data[zero_page_address];
                    self.set_default_flags();
                }
                // Handle LDA with Zero Page,X addressing mode.
                INS_LDA_ZPX => {
                    // Read the next byte (zero-page address) and add the X register to it.
                    let zero_page_address = self.read_byte(cycles, memory) as usize;
                    // Wrap the address around the zero page boundary (0x0FF).
                    let zero_page_address_x =
                        zero_page_address.wrapping_add(self.x as usize) & 0x00FF;
                    // Load the calculated address into the accumulator.
                    self.a = memory.data[zero_page_address_x];
                }
                // Handle JSR (Jump to Subroutine).
                INS_JSR => {
                    // Read the next two bytes for the subroutine address.
                    let address = self.read_word(cycles, memory);
                    // Push the current program counter (minus one) onto the stack before jumping.
                    self.push_stack_word(memory, self.pc - 1);
                    // Set the program counter to the subroutine address.
                    self.pc = address;
                    // Subtract 6 cycles for the JSR operation.
                    *cycles = cycles.wrapping_sub(6);
                }
                // Handle RTS (Return from Subroutine).
                INS_RTS => {
                    // Pull the return address from the stack.
                    let address = self.pull_stack_word(memory);
                    // Set the program counter to one more than the pulled stack.
                    self.pc = address.wrapping_add(1);
                    // Subtract 6 cycles for RTS operation.
                    *cycles = cycles.saturating_sub(6);
                }
                _ => {}
            }
        }
    }
}

fn main() {
    let mut memory = Mem::new();
    let mut cpu = CPU::new();
    // Write a subroutine at address 0x8000
    memory.write(0x8000, INS_LDA_IM); // Subroutine: LDA #$84
    memory.write(0x8001, 0x84);
    memory.write(0x8002, INS_RTS); // Return from subroutine

    // Write program into memory to call the subroutine
    memory.write(0xFFFC, INS_JSR); // JSR to subroutine
    memory.write(0xFFFD, 0x00); // Low byte of subroutine address
    memory.write(0xFFFE, 0x80); // High byte of subroutine address

    // Set the program counter to the start of the program.
    cpu.pc = 0xFFFC;

    // Enough cycles to execute JSR, the subroutine, and RTS
    let mut cycles: u32 = 50;
    cpu.execute(&mut memory, &mut cycles);

    println!("Accumulator: {:#x}", cpu.a);
    println!("Zero Flag: {}", cpu.z);
    println!("Negative Flag: {}", cpu.n);
    // Fetch the byte from memory.
}
