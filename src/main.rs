// Memory size for the 6502 processor which can address 64KB.
const MAX_MEM: usize = 1024 * 64;

// Opcodes for various 6502 assembly instructions.
const INS_LDA_IM: u8 = 0xA9; // Opcode for LDA with immediate addressing mode.
const INS_LDA_ZP: u8 = 0xA5; // Opcode for LDA with zero-page addressing mode.
const INS_LDA_ZPX: u8 = 0xB5; // Opcode for LDA with zero-page,X addressing mode.
const INS_LDA_ABS: u8 = 0xAD; // Opcode for LDA with Absolute addressing mode.
const INS_LDA_ABS_X: u8 = 0xBD; // Opcode for LDA with Absolute,X addressing mode.
const INS_LDA_ABS_Y: u8 = 0xB9; // Opcode for LDA with Absolute,Y addressing mode.
const INS_LDA_IND_X: u8 = 0xA1; // Opcode for LDA with Indirect,X addressing mode.
const INS_LDA_IND_Y: u8 = 0xB1; // Opcode for LDA with Indirect,Y addressing mode.
const INS_LDX_IM: u8 = 0xA2; // Opcode for LDX with immediate addressing mode.
const INS_LDX_ZP: u8 = 0xA6; // Opcode for LDX with zero-page addressing mode.
const INS_LDX_ZPY: u8 = 0xB6; // Opcode for LDX with zero-page,Y addressing mode.
const INS_LDX_ABS: u8 = 0xAE; // Opcode for LDX with Absolute addressing mode.
const INS_LDX_ABS_Y: u8 = 0xBE; // Opcode for LDX with Absolute,Y addressing mode.
const INS_LDY_IM: u8 = 0xA0; // Opcode for LDY with immediate addressing mode.
const INS_LDY_ZP: u8 = 0xA4; // Opcode for LDY with zero-page addressing mode.
const INS_LDY_ZPX: u8 = 0xB4; // Opcode for LDY with zero-page,X addressing mode.
const INS_LDY_ABS: u8 = 0xAC; // Opcode for LDY with Absolute addressing mode.
const INS_LDY_ABS_X: u8 = 0xBC; // Opcode for LDY with Absolute,X addressing mode.
const INS_JSR: u8 = 0x20; // Opcode for Jump to Subroutine
const INS_RTS: u8 = 0x60; // Opcode for Return from Soubroutine
const INS_LSR_A: u8 = 0x4A; // Opcode for Logical Shift Right Accumulator.
const INS_LSR_ZP: u8 = 0x46; // Opcode for Logical Shift Right zero-page.
const INS_LSR_ZPX: u8 = 0x56; // Opcode for Logical Shift Right zero-page,X.
const INS_LSR_ABS: u8 = 0x4E; // Opcode for Logical Shift Right Absolute addressing mode.
const INS_LSR_ABS_X: u8 = 0x5E; // Opcode for Logical Shift Right Absolute,X addressing mode.
const INS_NOP: u8 = 0xEA; // Opcode for No Operation.
const INS_ORA_IM: u8 = 0x09; // Opcode for Logical Inclusive OR Immediate addressing mode.
const INS_ORA_ZP: u8 = 0x05; // Opcode for Logical Inclusive OR Zero Page addressing mode.
const INS_ORA_ZPX: u8 = 0x15; // Opcode for Logical Inclusive OR Zero Page,X addressing mode.
const INS_ORA_ABS: u8 = 0x0D; // Opcode for Logical Inclusive OR Absolute addressing mode.
const INS_ORA_ABS_X: u8 = 0x1D; // Opcode for Logical Inclusive OR Absolute,X addressing mode.
const INS_ORA_ABS_Y: u8 = 0x19; // Opcode for Logical Inclusive OR Absolute, Y addressing mode.
const INS_ORA_IND_X: u8 = 0x01; // Opcode for Logical Inclusive OR Indirect,X addressing mode.
const INS_ORA_IND_Y: u8 = 0x11; // Opcode for Logical Inclusive OR Indirect,Y addressing mode.
const INS_PHA: u8 = 0x48; // Opcode for PHA - Push accumulator.
const INS_PHP: u8 = 0x08; // Opcode for PHP
const INS_PLA: u8 = 0x68; // Opcode for PLA
const INS_PLP: u8 = 0x28; // Opcode for PLP
const INS_ROL_A: u8 = 0x2A; // Opcode for ROL - Rotate Left Accumulator addressing mode.
const INS_ROL_ZP: u8 = 0x26; // Opcode for ROL - Rotate Left Zero Page addressing mode.
const INS_ROL_ZPX: u8 = 0x36; // Opcode for ROL - Rotate Left Zero Page,X addressing mode.
const INS_ROL_ABS: u8 = 0x2E; // Opcode for ROL - Rotate Left Absolute addressing mode.
const INS_ROL_ABX: u8 = 0x3E; // Opcode for ROL - Rotate Left Absolute,X addressing mode.

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
struct Cpu {
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

impl Cpu {
    // Constructs a new CPU with initial state.
    fn new() -> Cpu {
        Cpu {
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
        *cycles = cycles.wrapping_sub(1);
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

        *cycles = cycles.wrapping_sub(2);
        // Combine the low and high bytes.
        low | high
    }

    // Pushes a byte onto the stack and decrement the stack pointer.
    fn push_stack(&mut self, cycles: &mut u32, memory: &mut Mem, value: u8) {
        // Calculate the stack address.
        let sp_address = 0x0100 + self.sp as usize;
        self.sp = self.sp.wrapping_sub(1);
        // Write the byte to the stack address.
        memory.write(sp_address, value);

        *cycles = cycles.wrapping_sub(1);
    }

    // Pushes a 16-bit word onto the stack in two parts (high byte first).
    fn push_stack_word(&mut self, cycles: &mut u32, memory: &mut Mem, value: u16) {
        // Push low byte.
        self.push_stack(cycles, memory, (value >> 8) as u8);
        // Push high byte.
        self.push_stack(cycles, memory, (value & 0xFF) as u8);
    }

    // Pulls a byte from the stack and increments the stack pointer.
    fn pull_stack(&mut self, cycles: &mut u32, memory: &Mem) -> u8 {
        let sp_address = 0x0100 + self.sp as usize;
        self.sp = self.sp.wrapping_add(1);
        *cycles = cycles.wrapping_sub(1);
        // Return the byte from the stack.
        memory.data[sp_address]
    }

    // Pulls a 16-bit word from the stack (low byte first).
    fn pull_stack_word(&mut self, cycles: &mut u32, memory: &Mem) -> u16 {
        let low_byte = self.pull_stack(cycles, memory) as u16;
        let high_byte = self.pull_stack(cycles, memory) as u16;
        (high_byte << 8) | low_byte
    }

    // Sets the Zero flags if accumulator is zero.
    // Set Negative flag based on high bit of accumulator.
    fn set_zero_and_negative_flags(&mut self, value: u8) {
        self.z = value == 0;
        self.n = (value & 0b1000_0000) != 0;
    }

    fn ins_php(&mut self, cycles: &mut u32, memory: &mut Mem) {}

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
                    self.set_zero_and_negative_flags(self.a);
                    *cycles = cycles.wrapping_sub(1);
                }
                // Handle LDA with Zero Page addressing mode.
                INS_LDA_ZP => {
                    let zero_page_address = self.read_byte(cycles, memory) as usize;
                    self.a = memory.data[zero_page_address];
                    self.set_zero_and_negative_flags(self.a);

                    *cycles = cycles.wrapping_sub(2);
                }
                // Handle LDA with Zero Page,X addressing mode.
                INS_LDA_ZPX => {
                    // Read the next byte (zero-page address) and add the X register to it.
                    let zero_page_address = self.read_byte(cycles, memory) as usize;
                    // Wrap the address around the zero page boundary (0x0FF).
                    let zero_page_address_x =
                        zero_page_address.wrapping_add(self.x as usize) & 0xFF;
                    // Load the calculated address into the accumulator.
                    self.a = memory.data[zero_page_address_x];
                    self.set_zero_and_negative_flags(self.a);

                    *cycles = cycles.wrapping_sub(3);
                }
                // Handle LDA with Absolute addressing mode.
                INS_LDA_ABS => {
                    // Read a 16-bit (two-byte) address from the current program counter position.
                    let absolute_address = self.read_word(cycles, memory);
                    // Load the value at the fetched address into the accumulator
                    self.a = memory.data[absolute_address as usize];
                    self.set_zero_and_negative_flags(self.a);

                    *cycles = cycles.wrapping_sub(2);
                }
                // Handle LDA with Absolute,X addressing mode.
                INS_LDA_ABS_X => {
                    // Read a 16-bit base address and add X register to it.
                    let absolute_address = self.read_word(cycles, memory);
                    let absolute_address_x = absolute_address.wrapping_add(self.x as u16);
                    // Check if adding X crosses a page boundary (256-byte boundary).
                    let page_crossed = (absolute_address & 0xFF00) != (absolute_address_x & 0xFF00);

                    // Load the value from the computed address into the accumulator.
                    self.a = memory.data[absolute_address_x as usize];
                    self.set_zero_and_negative_flags(self.a);

                    *cycles = cycles.wrapping_sub(2);
                    if page_crossed {
                        *cycles = cycles.wrapping_sub(1);
                    }
                }
                // Handle LDA with Absolute,Y addressing mode.
                INS_LDA_ABS_Y => {
                    // Similar to Absolute,X but using the Y register instead.
                    let absolute_address = self.read_word(cycles, memory);
                    let absolute_address_y = absolute_address.wrapping_add(self.y as u16);
                    let page_crossed = (absolute_address & 0xFF00) != (absolute_address_y & 0xFF00);

                    self.a = memory.data[absolute_address_y as usize];
                    self.set_zero_and_negative_flags(self.a);

                    *cycles = cycles.wrapping_sub(2);
                    if page_crossed {
                        *cycles = cycles.wrapping_sub(1);
                    }
                }
                // Handle LDA with Indexed Indirect addressing mode.
                INS_LDA_IND_X => {
                    // Read an 8-bit address, add the X register to it, and use it to find a 16-bit
                    // address in the zero page.
                    let address = self.read_byte(cycles, memory) as usize;
                    let table_address = address.wrapping_add(self.x as usize);

                    // Fetch the low and high bytes of indirect address from the zero page.
                    let low_byte = memory.data[table_address] as u16;
                    let high_byte = memory.data[table_address.wrapping_add(1)] as u16;
                    // Combine the low and high bytes to form the complete indirect address.
                    let indirect_address = (high_byte << 8) | low_byte;
                    // Load the value from the indirect address into the accumulator.
                    self.a = memory.data[indirect_address as usize];
                    self.set_zero_and_negative_flags(self.a);

                    *cycles = cycles.wrapping_sub(5);
                }
                INS_LDA_IND_Y => {
                    let zero_page_address = self.read_byte(cycles, memory) as usize;

                    let low_byte = memory.data[zero_page_address] as u16;
                    let high_byte = memory.data[zero_page_address.wrapping_add(1)] as u16;
                    let zero_page_fetched = (high_byte << 8) | low_byte;
                    let indirect_address = zero_page_fetched.wrapping_add(self.y as u16);
                    let page_crossed = (zero_page_fetched & 0xFF00) != (indirect_address & 0xFF00);

                    self.a = memory.data[indirect_address as usize];
                    self.set_zero_and_negative_flags(self.a);

                    *cycles = cycles.wrapping_sub(4);
                    if page_crossed {
                        *cycles = cycles.wrapping_sub(1);
                    }
                }
                // Similar to LDA IM. Handle LDX with Immediate addressing mode.
                INS_LDX_IM => {
                    let value = self.read_byte(cycles, memory);
                    self.x = value;
                    self.set_zero_and_negative_flags(self.x);

                    *cycles = cycles.wrapping_sub(1);
                }
                // Similar to LDA ZP. Handle LDX with zero-page addressing mode.
                INS_LDX_ZP => {
                    let zero_page_address = self.read_byte(cycles, memory) as usize;
                    self.x = memory.data[zero_page_address];
                    self.set_zero_and_negative_flags(self.x);

                    *cycles = cycles.wrapping_sub(2);
                }
                // Similar to LDA ZPX. Handle LDX with zero-page,Y addressing mode.
                INS_LDX_ZPY => {
                    let zero_page_address = self.read_byte(cycles, memory) as usize;
                    let zero_page_address_y =
                        zero_page_address.wrapping_add(self.y as usize) & 0xFF;
                    self.x = memory.data[zero_page_address_y];
                    self.set_zero_and_negative_flags(self.x);

                    *cycles = cycles.wrapping_sub(3);
                }
                // Similar to LDA Absolute. Handle LDX with Absolute addressing mode.
                INS_LDX_ABS => {
                    let absolute_address = self.read_word(cycles, memory);
                    self.x = memory.data[absolute_address as usize];

                    self.set_zero_and_negative_flags(self.x);
                    *cycles = cycles.wrapping_sub(2);
                }
                // Similar to LDA Absolute,Y. Handle LDX with Absolute,Y addressing mode.
                INS_LDX_ABS_Y => {
                    let absolute_address = self.read_word(cycles, memory);
                    let absolute_address_y = absolute_address.wrapping_add(self.y as u16);
                    let page_crossed = (absolute_address & 0xFF00) != (absolute_address_y & 0xFF00);

                    self.x = memory.data[absolute_address_y as usize];
                    self.set_zero_and_negative_flags(self.x);

                    *cycles = cycles.wrapping_sub(2);
                    if page_crossed {
                        *cycles = cycles.wrapping_sub(1);
                    }
                }
                // Similar to LDA Immediate. Handle LDY with immediate addressing mode.
                INS_LDY_IM => {
                    let value = self.read_byte(cycles, memory);
                    self.y = value;
                    self.set_zero_and_negative_flags(self.y);

                    *cycles = cycles.wrapping_sub(1);
                }
                INS_LDY_ZP => {
                    let zero_page_address = self.read_byte(cycles, memory) as usize;
                    self.y = memory.data[zero_page_address];
                    self.set_zero_and_negative_flags(self.y);

                    *cycles = cycles.wrapping_sub(2);
                }
                // Similar to LDA zero-page,X. Handle LDY with zero-page,X addressing mode.
                INS_LDY_ZPX => {
                    let zero_page_address = self.read_byte(cycles, memory) as usize;
                    let zero_page_address_x =
                        zero_page_address.wrapping_add(self.x as usize) & 0xFF;
                    self.y = memory.data[zero_page_address_x];
                    self.set_zero_and_negative_flags(self.y);

                    *cycles = cycles.wrapping_sub(3);
                }
                // Similar to LDA Absolute. Handle LDY with Absolute addressing mode.
                INS_LDY_ABS => {
                    let absolute_address = self.read_word(cycles, memory) as usize;
                    self.y = memory.data[absolute_address];
                    self.set_zero_and_negative_flags(self.y);

                    *cycles = cycles.wrapping_sub(2);
                }
                INS_LDY_ABS_X => {
                    let absolute_address = self.read_word(cycles, memory) as usize;
                    let absolute_address_x = absolute_address.wrapping_add(self.x as usize);
                    let page_crossed = (absolute_address & 0xFF00) != (absolute_address_x & 0xFF00);

                    self.y = memory.data[absolute_address_x];

                    *cycles = cycles.wrapping_sub(2);
                    if page_crossed {
                        *cycles = cycles.wrapping_sub(1);
                    }
                }
                // Handle JSR (Jump to Subroutine).
                INS_JSR => {
                    // Read the next two bytes for the subroutine address.
                    let address = self.read_word(cycles, memory);
                    // Push the current program counter (minus one) onto the stack before jumping.
                    self.push_stack_word(cycles, memory, self.pc - 1);
                    // Set the program counter to the subroutine address.
                    self.pc = address;
                    // Subtract 2 cycles more cycles for a total of 6 for the JSR operation.
                    *cycles = cycles.wrapping_sub(2);
                }
                // Handle RTS (Return from Subroutine).
                INS_RTS => {
                    // Pull the return address from the stack.
                    let address = self.pull_stack_word(cycles, memory);
                    // Set the program counter to one more than the pulled stack.
                    self.pc = address.wrapping_add(1);
                    // Subtract 4 more cycles for a total of 6 cycles for RTS operation.
                    *cycles = cycles.saturating_sub(4);
                }
                // Handle LSR (Logical Shift Right) Accumulator.
                INS_LSR_A => {
                    self.c = self.a & 0x01 != 0;
                    self.a >>= 1;
                    self.set_zero_and_negative_flags(self.a);

                    *cycles = cycles.wrapping_sub(2);
                }
                INS_LSR_ZP => {
                    let zero_page_address = self.read_byte(cycles, memory) as usize;
                    let zero_page_fetched = memory.data[zero_page_address];

                    self.c = zero_page_fetched & 0x01 != 0;

                    let zero_page_shifted = zero_page_fetched >> 1;

                    memory.data[zero_page_address] = zero_page_shifted;

                    self.set_zero_and_negative_flags(zero_page_shifted);

                    *cycles = cycles.wrapping_sub(4);
                }
                INS_LSR_ZPX => {
                    let zero_page_address = self.read_byte(cycles, memory) as usize;
                    let zero_page_address_x =
                        zero_page_address.wrapping_add(self.x as usize) & 0xFF;
                    let zero_page_fetched = memory.data[zero_page_address_x];

                    self.c = zero_page_fetched & 0x01 != 0;

                    let zero_page_shifted = zero_page_fetched >> 1;

                    memory.data[zero_page_address_x] = zero_page_shifted;

                    self.set_zero_and_negative_flags(zero_page_shifted);

                    *cycles = cycles.wrapping_sub(6);
                }
                INS_LSR_ABS => {
                    let absolute_address = self.read_word(cycles, memory) as usize;
                    let absolute_fetched = memory.data[absolute_address];

                    self.c = absolute_fetched & 0x01 != 0;

                    let absolute_shifted = absolute_fetched >> 1;

                    memory.data[absolute_address] = absolute_shifted;

                    self.set_zero_and_negative_flags(absolute_shifted);

                    *cycles = cycles.wrapping_sub(4);
                }
                INS_LSR_ABS_X => {
                    let absolute_address = self.read_word(cycles, memory) as usize;
                    let absolute_address_x = absolute_address.wrapping_add(self.x as usize);
                    let absolute_address_fetched = memory.data[absolute_address_x];

                    self.c = absolute_address_fetched & 0x01 != 0;

                    let absolute_address_shifted = absolute_address_fetched >> 1;

                    memory.data[absolute_address_x] = absolute_address_shifted;

                    self.set_zero_and_negative_flags(absolute_address_shifted);

                    *cycles = cycles.wrapping_sub(5);
                }
                INS_NOP => {
                    *cycles = cycles.saturating_sub(1);
                }
                INS_ORA_IM => {
                    let address = self.read_byte(cycles, memory);
                    self.a |= address;

                    self.set_zero_and_negative_flags(self.a);

                    *cycles = cycles.wrapping_sub(1);
                }
                INS_ORA_ZP => {
                    let zero_page_address = self.read_byte(cycles, memory) as usize;
                    self.a |= memory.data[zero_page_address];

                    self.set_zero_and_negative_flags(self.a);

                    *cycles = cycles.wrapping_sub(2);
                }
                INS_ORA_ZPX => {
                    let zero_page_address = self.read_byte(cycles, memory) as usize;
                    let zero_page_address_x =
                        zero_page_address.wrapping_add(self.x as usize) & 0xFF;
                    self.a |= memory.data[zero_page_address_x];

                    self.set_zero_and_negative_flags(self.a);

                    *cycles = cycles.wrapping_sub(3);
                }
                INS_ORA_ABS => {
                    let absolute_address = self.read_word(cycles, memory) as usize;
                    self.a |= memory.data[absolute_address];

                    self.set_zero_and_negative_flags(self.a);

                    *cycles = cycles.wrapping_sub(2);
                }
                INS_ORA_ABS_X => {
                    let absolute_address = self.read_word(cycles, memory) as usize;
                    let absolute_address_x = absolute_address.wrapping_add(self.x as usize);
                    let page_crossed = (absolute_address & 0xFF00) != (absolute_address_x & 0xFF00);

                    self.a |= memory.data[absolute_address_x];

                    *cycles = cycles.wrapping_sub(2);
                    if page_crossed {
                        *cycles = cycles.wrapping_sub(1);
                    }
                }
                INS_ORA_ABS_Y => {
                    let absolute_address = self.read_word(cycles, memory) as usize;
                    let absolute_address_y = absolute_address.wrapping_add(self.y as usize);
                    let page_crossed = (absolute_address & 0xFF00) != (absolute_address_y & 0xFF00);

                    self.a |= memory.data[absolute_address_y];

                    *cycles = cycles.wrapping_sub(2);
                    if page_crossed {
                        *cycles = cycles.wrapping_sub(1);
                    }
                }
                INS_ORA_IND_X => {
                    let address = self.read_byte(cycles, memory) as usize;
                    let table_address = address.wrapping_add(self.x as usize);

                    let low_byte = memory.data[table_address] as u16;
                    let high_byte = memory.data[table_address.wrapping_add(1)] as u16;

                    let indirect_address = (high_byte << 8) | low_byte;

                    self.a |= memory.data[indirect_address as usize];

                    *cycles = cycles.wrapping_sub(5);
                }

                INS_ORA_IND_Y => {
                    let address = self.read_byte(cycles, memory) as usize;
                    let table_address = address.wrapping_add(self.y as usize);
                    let page_crossed = (address & 0xFF00) != (table_address & 0xFF00);

                    let low_byte = memory.data[table_address] as u16;
                    let high_byte = memory.data[table_address.wrapping_add(1)] as u16;

                    let indirect_address = (high_byte << 8) | low_byte;

                    self.a |= memory.data[indirect_address as usize];

                    *cycles = cycles.wrapping_sub(4);
                    if page_crossed {
                        *cycles = cycles.wrapping_sub(1);
                    }
                }
                INS_PHA => {
                    self.push_stack(cycles, memory, self.a);

                    *cycles = cycles.wrapping_sub(2);
                }
                // Implementation of the PHP instruction
                INS_PHP => {
                    let mut flags: u8 = 0;

                    // Push each flag onto the stack
                    flags |= if self.c { 0b0000_0001 } else { 0 };
                    flags |= if self.z { 0b0000_0010 } else { 0 };
                    flags |= if self.i { 0b0000_0100 } else { 0 };
                    flags |= if self.d { 0b0000_1000 } else { 0 };
                    flags |= if self.b { 0b0001_0000 } else { 0 };
                    flags |= if self.v { 0b0100_0000 } else { 0 };
                    flags |= if self.n { 0b1000_0000 } else { 0 };

                    self.push_stack(cycles, memory, flags);

                    *cycles = cycles.wrapping_sub(2);
                }
                INS_PLA => {
                    self.a = self.pull_stack(cycles, memory);
                    self.set_zero_and_negative_flags(self.a);

                    *cycles = cycles.wrapping_sub(3);
                }
                INS_PLP => {
                    let status = self.pull_stack(cycles, memory);

                    // Set flags based on the bits of the status read from the stack
                    self.c = status & 0b0000_0001 != 0;
                    self.z = status & 0b0000_0010 != 0;
                    self.i = status & 0b0000_0100 != 0;
                    self.d = status & 0b0000_1000 != 0;
                    // The B flag should always be set to 1 when read from the stack.
                    self.b = true;
                    self.v = status & 0b0100_0000 != 0;
                    self.n = status & 0b1000_0000 != 0;
                }
                INS_ROL_A => {
                    let carry_value = self.c as u8;
                    let prev_a = self.a;

                    // shift left and set bit 0 to the carry flag
                    self.a = (prev_a << 1) | carry_value;

                    self.set_zero_and_negative_flags(self.a);

                    *cycles = cycles.wrapping_sub(2);
                }
                INS_ROL_ZP => {
                    let carry = self.c as u8;
                    let zero_page_address = self.read_byte(cycles, memory) as usize;
                    let prev_a = memory.data[zero_page_address];

                    self.a = (prev_a << 1) | carry;

                    self.set_zero_and_negative_flags(self.a);

                    *cycles = cycles.wrapping_sub(4);
                }
                INS_ROL_ZPX => {
                    let carry = self.c as u8;
                    let zero_page_address = self.read_byte(cycles, memory) as usize;
                    let zero_page_address_x =
                        zero_page_address.wrapping_add(self.x as usize) & 0xFF;
                    let prev_a = memory.data[zero_page_address_x];

                    self.a = (prev_a << 1) | carry;

                    self.set_zero_and_negative_flags(self.a);

                    *cycles = cycles.wrapping_sub(5);
                }
                INS_ROL_ABS => {
                    let carry = self.c as u8;
                    let absolute_address = self.read_word(cycles, memory) as usize;
                    let prev_a = memory.data[absolute_address];

                    self.a = (prev_a << 1) | carry;

                    self.set_zero_and_negative_flags(self.a);

                    *cycles = cycles.wrapping_sub(4);
                }
                INS_ROL_ABX => {
                    let carry = self.c as u8;
                    let absolute_address = self.read_word(cycles, memory) as usize;
                    let absolute_address_x = absolute_address.wrapping_add(self.x as usize) & 0xFF;
                    let prev_a = memory.data[absolute_address_x];

                    self.a = (prev_a << 1) | carry;

                    self.set_zero_and_negative_flags(self.a);

                    *cycles = cycles.wrapping_sub(5);
                }
                _ => {}
            }
        }
    }
}

fn main() {
    let mut memory = Mem::new();
    let mut cpu = Cpu::new();
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
}
