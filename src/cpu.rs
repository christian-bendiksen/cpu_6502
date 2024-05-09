use crate::mem::Mem;
use crate::opcodes::opcodes::*;

// CPU struct represents the state of the CPU including registers and flags.

pub struct Cpu {
    pub pc: u16, // Program counter: points to the next instruction to execute.
    pub sp: u16, // Stack pointer: points to the top of the stack.
    pub a: u8,   // Accumulator: used for arithmetic and logic operations.
    pub x: u8,   // X index register.
    pub y: u8,   // Y index register.
    // Processor status flags:
    pub c: bool, // Carry flag.
    pub z: bool, // Zero flag.
    pub i: bool, // Interrupt disable flag.
    pub d: bool, // Decimal mode flag.
    pub b: bool, // Break command flag.
    pub v: bool, // Overflow flag.
    pub n: bool, // Negative flag.
}

impl Cpu {
    // Constructs a new CPU with initial state.
    pub fn new() -> Cpu {
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

    pub fn set_zero_and_negative_flags(&mut self, result: u8) {
        self.z = result == 0;
        self.n = (result & 0x80) != 0;
    }

    fn rol_rotate_left(&mut self, value: u8) {
        let carry = self.c as u8;
        self.a = (value << 1) | carry;
        self.set_zero_and_negative_flags(self.a);
    }
    fn ror_rotate_right(&mut self, value: u8) {
        let carry = self.c as u8;
        self.a = (value >> 1) | carry;
        self.set_zero_and_negative_flags(self.a);
    }

    fn subtract_with_carry(&mut self, operand: u8) {
        let carry = if self.c { 0 } else { 1 };

        let result = self.a.wrapping_sub(operand).wrapping_sub(carry);

        self.c = self.a >= (operand + carry);
        self.z = result == 0;
        self.n = (result & 0x80) != 0;
        self.v = (((self.a ^ operand) & 0x80) != 0) && (((self.a ^ result) & 0x80) != 0);

        self.a = result;
    }

    // Execute CPU instructions.
    // This function drives the CPU's execution based on the opcodes.
    //
    // Arguments:
    // * `memory`: mutable reference to the CPU's memory.
    // * `cycles`: mutable reference to the number of cycles remaining for the CPU to execute.
    pub fn execute(&mut self, memory: &mut Mem, cycles: &mut u32) {
        // Continue executing while we have cycles left.
        while *cycles > 0 {
            // Read the next opcode from memory at the current program counter.
            let ins = memory.read_byte(cycles, self);

            match ins {
                // Handle LDA with Immediate addressing mode.
                INS_LDA_IM => {
                    // Read the next byte from memory, which is the immediate value for LDA.
                    let value = memory.read_byte(cycles, self);
                    // Load the read value into the accumulator.
                    self.a = value;
                    // Update the Zero and Negative flags based on the new accumulator value.
                    self.set_zero_and_negative_flags(self.a);
                    *cycles = cycles.wrapping_sub(1);
                }
                // Handle LDA with Zero Page addressing mode.
                INS_LDA_ZP => {
                    let zero_page_address = memory.read_byte(cycles, self) as usize;
                    self.a = memory.data[zero_page_address];
                    self.set_zero_and_negative_flags(self.a);

                    *cycles = cycles.wrapping_sub(2);
                }
                // Handle LDA with Zero Page,X addressing mode.
                INS_LDA_ZPX => {
                    // Read the next byte (zero-page address) and add the X register to it.
                    let zero_page_address = memory.read_byte(cycles, self) as usize;
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
                    let absolute_address = memory.read_word(cycles, self);
                    // Load the value at the fetched address into the accumulator
                    self.a = memory.data[absolute_address as usize];
                    self.set_zero_and_negative_flags(self.a);

                    *cycles = cycles.wrapping_sub(2);
                }
                // Handle LDA with Absolute,X addressing mode.
                INS_LDA_ABS_X => {
                    // Read a 16-bit base address and add X register to it.
                    let absolute_address = memory.read_word(cycles, self);
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
                    let absolute_address = memory.read_word(cycles, self);
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
                    let address = memory.read_byte(cycles, self) as usize;
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
                    let zero_page_address = memory.read_byte(cycles, self) as usize;

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
                    let value = memory.read_byte(cycles, self);
                    self.x = value;
                    self.set_zero_and_negative_flags(self.x);

                    *cycles = cycles.wrapping_sub(1);
                }
                // Similar to LDA ZP. Handle LDX with zero-page addressing mode.
                INS_LDX_ZP => {
                    let zero_page_address = memory.read_byte(cycles, self) as usize;
                    self.x = memory.data[zero_page_address];
                    self.set_zero_and_negative_flags(self.x);

                    *cycles = cycles.wrapping_sub(2);
                }
                // Similar to LDA ZPX. Handle LDX with zero-page,Y addressing mode.
                INS_LDX_ZPY => {
                    let zero_page_address = memory.read_byte(cycles, self) as usize;
                    let zero_page_address_y =
                        zero_page_address.wrapping_add(self.y as usize) & 0xFF;
                    self.x = memory.data[zero_page_address_y];
                    self.set_zero_and_negative_flags(self.x);

                    *cycles = cycles.wrapping_sub(3);
                }
                // Similar to LDA Absolute. Handle LDX with Absolute addressing mode.
                INS_LDX_ABS => {
                    let absolute_address = memory.read_word(cycles, self);
                    self.x = memory.data[absolute_address as usize];

                    self.set_zero_and_negative_flags(self.x);
                    *cycles = cycles.wrapping_sub(2);
                }
                // Similar to LDA Absolute,Y. Handle LDX with Absolute,Y addressing mode.
                INS_LDX_ABS_Y => {
                    let absolute_address = memory.read_word(cycles, self);
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
                    let value = memory.read_byte(cycles, self);
                    self.y = value;
                    self.set_zero_and_negative_flags(self.y);

                    *cycles = cycles.wrapping_sub(1);
                }
                INS_LDY_ZP => {
                    let zero_page_address = memory.read_byte(cycles, self) as usize;
                    self.y = memory.data[zero_page_address];
                    self.set_zero_and_negative_flags(self.y);

                    *cycles = cycles.wrapping_sub(2);
                }
                // Similar to LDA zero-page,X. Handle LDY with zero-page,X addressing mode.
                INS_LDY_ZPX => {
                    let zero_page_address = memory.read_byte(cycles, self) as usize;
                    let zero_page_address_x =
                        zero_page_address.wrapping_add(self.x as usize) & 0xFF;
                    self.y = memory.data[zero_page_address_x];
                    self.set_zero_and_negative_flags(self.y);

                    *cycles = cycles.wrapping_sub(3);
                }
                // Similar to LDA Absolute. Handle LDY with Absolute addressing mode.
                INS_LDY_ABS => {
                    let absolute_address = memory.read_word(cycles, self) as usize;
                    self.y = memory.data[absolute_address];
                    self.set_zero_and_negative_flags(self.y);

                    *cycles = cycles.wrapping_sub(2);
                }
                INS_LDY_ABS_X => {
                    let absolute_address = memory.read_word(cycles, self) as usize;
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
                    let address = memory.read_word(cycles, self);
                    // Push the current program counter (minus one) onto the stack before jumping.
                    memory.push_stack_word(cycles, self, self.pc - 1);
                    // Set the program counter to the subroutine address.
                    self.pc = address;
                    // Subtract 2 cycles more cycles for a total of 6 for the JSR operation.
                    *cycles = cycles.wrapping_sub(2);
                }
                // Handle RTS (Return from Subroutine).
                INS_RTS => {
                    let address = memory.pull_stack_word(cycles, self);
                    self.pc = address.wrapping_add(1);
                    *cycles = cycles.saturating_sub(6);
                }
                // Handle LSR (Logical Shift Right) Accumulator.
                INS_LSR_A => {
                    self.c = self.a & 0x01 != 0;
                    self.a >>= 1;
                    self.set_zero_and_negative_flags(self.a);

                    *cycles = cycles.wrapping_sub(2);
                }
                INS_LSR_ZP => {
                    let zero_page_address = memory.read_byte(cycles, self) as usize;
                    let zero_page_fetched = memory.data[zero_page_address];

                    self.c = zero_page_fetched & 0x01 != 0;

                    let zero_page_shifted = zero_page_fetched >> 1;

                    memory.data[zero_page_address] = zero_page_shifted;

                    self.set_zero_and_negative_flags(zero_page_shifted);

                    *cycles = cycles.wrapping_sub(4);
                }
                INS_LSR_ZPX => {
                    let zero_page_address = memory.read_byte(cycles, self) as usize;
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
                    let absolute_address = memory.read_word(cycles, self) as usize;
                    let absolute_fetched = memory.data[absolute_address];

                    self.c = absolute_fetched & 0x01 != 0;

                    let absolute_shifted = absolute_fetched >> 1;

                    memory.data[absolute_address] = absolute_shifted;

                    self.set_zero_and_negative_flags(absolute_shifted);

                    *cycles = cycles.wrapping_sub(4);
                }
                INS_LSR_ABS_X => {
                    let absolute_address = memory.read_word(cycles, self) as usize;
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
                    let address = memory.read_byte(cycles, self);
                    self.a |= address;

                    self.set_zero_and_negative_flags(self.a);

                    *cycles = cycles.wrapping_sub(1);
                }
                INS_ORA_ZP => {
                    let zero_page_address = memory.read_byte(cycles, self) as usize;
                    self.a |= memory.data[zero_page_address];

                    self.set_zero_and_negative_flags(self.a);

                    *cycles = cycles.wrapping_sub(2);
                }
                INS_ORA_ZPX => {
                    let zero_page_address = memory.read_byte(cycles, self) as usize;
                    let zero_page_address_x =
                        zero_page_address.wrapping_add(self.x as usize) & 0xFF;
                    self.a |= memory.data[zero_page_address_x];

                    self.set_zero_and_negative_flags(self.a);

                    *cycles = cycles.wrapping_sub(3);
                }
                INS_ORA_ABS => {
                    let absolute_address = memory.read_word(cycles, self) as usize;
                    self.a |= memory.data[absolute_address];

                    self.set_zero_and_negative_flags(self.a);

                    *cycles = cycles.wrapping_sub(2);
                }
                INS_ORA_ABS_X => {
                    let absolute_address = memory.read_word(cycles, self) as usize;
                    let absolute_address_x = absolute_address.wrapping_add(self.x as usize);
                    let page_crossed = (absolute_address & 0xFF00) != (absolute_address_x & 0xFF00);

                    self.a |= memory.data[absolute_address_x];

                    *cycles = cycles.wrapping_sub(2);
                    if page_crossed {
                        *cycles = cycles.wrapping_sub(1);
                    }
                }
                INS_ORA_ABS_Y => {
                    let absolute_address = memory.read_word(cycles, self) as usize;
                    let absolute_address_y = absolute_address.wrapping_add(self.y as usize);
                    let page_crossed = (absolute_address & 0xFF00) != (absolute_address_y & 0xFF00);

                    self.a |= memory.data[absolute_address_y];

                    *cycles = cycles.wrapping_sub(2);
                    if page_crossed {
                        *cycles = cycles.wrapping_sub(1);
                    }
                }
                INS_ORA_IND_X => {
                    let address = memory.read_byte(cycles, self) as usize;
                    let table_address = address.wrapping_add(self.x as usize);

                    let low_byte = memory.data[table_address] as u16;
                    let high_byte = memory.data[table_address.wrapping_add(1)] as u16;

                    let indirect_address = (high_byte << 8) | low_byte;

                    self.a |= memory.data[indirect_address as usize];

                    *cycles = cycles.wrapping_sub(5);
                }

                INS_ORA_IND_Y => {
                    let address = memory.read_byte(cycles, self) as usize;
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
                    memory.push_stack(cycles, self, self.a);

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

                    memory.push_stack(cycles, self, flags);

                    *cycles = cycles.wrapping_sub(2);
                }
                INS_PLA => {
                    self.a = memory.pull_stack(cycles, self);
                    self.set_zero_and_negative_flags(self.a);

                    *cycles = cycles.wrapping_sub(3);
                }
                INS_PLP => {
                    let status = memory.pull_stack(cycles, self);

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
                    self.rol_rotate_left(self.a);

                    *cycles = cycles.wrapping_sub(2);
                }
                INS_ROL_ZP => {
                    let zero_page_address = memory.read_byte(cycles, self) as usize;
                    self.rol_rotate_left(memory.data[zero_page_address]);

                    *cycles = cycles.wrapping_sub(4);
                }
                INS_ROL_ZPX => {
                    let zero_page_address = memory.read_byte(cycles, self) as usize;
                    let zero_page_address_x =
                        zero_page_address.wrapping_add(self.x as usize) & 0xFF;
                    self.rol_rotate_left(memory.data[zero_page_address_x]);

                    *cycles = cycles.wrapping_sub(5);
                }
                INS_ROL_ABS => {
                    let absolute_address = memory.read_word(cycles, self) as usize;
                    self.rol_rotate_left(memory.data[absolute_address]);

                    *cycles = cycles.wrapping_sub(4);
                }
                INS_ROL_ABX => {
                    let absolute_address = memory.read_word(cycles, self) as usize;
                    let absolute_address_x = absolute_address.wrapping_add(self.x as usize) & 0xFF;
                    self.rol_rotate_left(memory.data[absolute_address_x]);

                    *cycles = cycles.wrapping_sub(5);
                }
                INS_ROR_A => {
                    self.ror_rotate_right(self.a);
                    self.set_zero_and_negative_flags(self.a);

                    *cycles = cycles.wrapping_sub(2);
                }
                INS_ROR_ZP => {
                    let zero_page_address = memory.read_byte(cycles, self) as usize;
                    self.ror_rotate_right(memory.data[zero_page_address]);

                    *cycles = cycles.wrapping_sub(4);
                }
                INS_ROR_ZPX => {
                    let zero_page_address = memory.read_byte(cycles, self) as usize;
                    let zero_page_address_x =
                        zero_page_address.wrapping_add(self.x as usize) & 0xFF;

                    self.ror_rotate_right(memory.data[zero_page_address_x]);

                    *cycles = cycles.wrapping_sub(5);
                }
                INS_ROR_ABS => {
                    let absolute_address = memory.read_word(cycles, self) as usize;
                    self.ror_rotate_right(memory.data[absolute_address]);

                    *cycles = cycles.wrapping_sub(4);
                }
                INS_ROR_ABX => {
                    let absolute_address = memory.read_word(cycles, self) as usize;
                    let absolute_address_x = absolute_address.wrapping_add(self.x as usize);

                    self.ror_rotate_right(memory.data[absolute_address_x]);

                    *cycles = cycles.wrapping_sub(5);
                }
                INS_RTI => {
                    let status = memory.pull_stack(cycles, self);

                    self.c = status & 0b0000_0001 != 0;
                    self.z = status & 0b0000_0010 != 0;
                    self.i = status & 0b0000_0100 != 0;
                    self.d = status & 0b0000_1000 != 0;
                    self.v = status & 0b0100_0000 != 0;
                    self.n = status & 0b1000_0000 != 0;

                    self.pc = memory.pull_stack_word(cycles, self);

                    *cycles = cycles.wrapping_sub(6);
                }
                INS_SBC_IM => {
                    let value = memory.read_byte(cycles, self);
                    self.subtract_with_carry(value);

                    *cycles = cycles.wrapping_sub(1);
                }
                INS_SBC_ZP => {
                    let value = memory.read_byte(cycles, self);
                    let value_zp = memory.data[value as usize];
                    self.subtract_with_carry(value_zp);

                    *cycles = cycles.wrapping_sub(2);
                }
                INS_SBC_ZPX => {
                    let zp_address = memory.read_byte(cycles, self) as usize;
                    let value_zpx = memory.data[zp_address.wrapping_add(self.x as usize)];
                    self.subtract_with_carry(value_zpx);

                    *cycles = cycles.wrapping_sub(4);
                }
                INS_SBC_ABS => {
                    let absolute_address = memory.read_word(cycles, self);
                    let value_abs = memory.data[absolute_address as usize];

                    self.subtract_with_carry(value_abs);

                    *cycles = cycles.wrapping_sub(4);
                }
                INS_SBC_ABX => {
                    let absolute_address = memory.read_word(cycles, self) as usize;
                    let absolute_address_x = absolute_address.wrapping_add(self.x as usize);
                    let page_crossed = (absolute_address & 0xFF00) != (absolute_address_x & 0xFF00);

                    let value_abx = memory.data[absolute_address_x];
                    self.subtract_with_carry(value_abx);

                    *cycles = cycles.wrapping_sub(4);
                    if page_crossed {
                        *cycles = cycles.wrapping_sub(1);
                    }
                }
                INS_SBC_ABY => {
                    let absolute_address = memory.read_word(cycles, self) as usize;
                    let absolute_address_y = absolute_address.wrapping_add(self.y as usize);
                    let page_crossed = (absolute_address & 0xFF00) != (absolute_address_y & 0xFF00);

                    let value_aby = memory.data[absolute_address_y];
                    self.subtract_with_carry(value_aby);

                    *cycles = cycles.wrapping_sub(4);
                    if page_crossed {
                        *cycles = cycles.wrapping_sub(1);
                    }
                }
                INS_SBC_IND_X => {
                    let zp_address = memory.read_byte(cycles, self) as usize;
                    let zp_address_x = zp_address.wrapping_add(self.x as usize);

                    let low_byte = memory.data[zp_address_x] as u16;
                    let high_byte = memory.data[zp_address_x.wrapping_add(1)] as u16;

                    let indirect_address = (high_byte << 8) | low_byte;

                    self.subtract_with_carry(indirect_address as u8);

                    *cycles = cycles.wrapping_sub(6);
                }
                INS_SBC_IND_Y => {
                    let zp_address = memory.read_byte(cycles, self) as usize;
                    let zp_address_y = zp_address.wrapping_add(self.y as usize);
                    let page_crossed = (zp_address & 0xFF00) != (zp_address_y & 0xFF00);

                    let low_byte = memory.data[zp_address_y] as u16;
                    let high_byte = memory.data[zp_address_y.wrapping_add(1)] as u16;

                    let indirect_address = (high_byte << 8) | low_byte;

                    self.subtract_with_carry(indirect_address as u8);

                    *cycles = cycles.wrapping_sub(5);
                    if page_crossed {
                        *cycles = cycles.wrapping_sub(1);
                    }
                }
                INS_SEC => {
                    self.c = true;
                }
                INS_SED => {
                    self.d = true;
                }
                INS_SEI => {
                    self.i = true;
                }
                INS_STA_ZP => {
                    let zp_address = memory.read_byte(cycles, self) as usize;
                    memory.data[zp_address] = self.a;

                    *cycles = cycles.wrapping_sub(3);
                }
                INS_STA_ZPX => {
                    let zp_address = memory.read_byte(cycles, self) as usize;
                    let zp_address_x = zp_address.wrapping_add(self.x as usize);
                    memory.data[zp_address_x] = self.a;

                    *cycles = cycles.wrapping_add(4);
                }
                INS_STA_ABS => {
                    let absolute_address = memory.read_word(cycles, self);
                    memory.data[absolute_address as usize] = self.a;

                    *cycles = cycles.wrapping_sub(4);
                }
                INS_STA_ABS_X => {
                    let absolute_address = memory.read_word(cycles, self) as usize;
                    let absolute_address_x = absolute_address.wrapping_add(self.x as usize);
                    memory.data[absolute_address_x] = self.a;

                    *cycles = cycles.wrapping_sub(5);
                }
                INS_STA_ABS_Y => {
                    let absolute_address = memory.read_word(cycles, self) as usize;
                    let absolute_address_y = absolute_address.wrapping_add(self.y as usize);
                    memory.data[absolute_address_y] = self.a;

                    *cycles = cycles.wrapping_sub(5);
                }
                INS_STA_IND_X => {
                    let zp_address = memory.read_word(cycles, self) as usize;
                    let zp_address_x = zp_address.wrapping_add(self.x as usize);

                    let low_byte = memory.data[zp_address_x] as u16;
                    let high_byte = memory.data[zp_address_x.wrapping_add(1)] as u16;

                    let indirect_address = (high_byte << 8) | low_byte;
                    memory.data[indirect_address as usize] = self.a;

                    *cycles = cycles.wrapping_sub(6);
                }
                INS_STA_IND_Y => {
                    let zp_address = memory.read_word(cycles, self) as usize;
                    let zp_address_y = zp_address.wrapping_add(self.y as usize);

                    let low_byte = memory.data[zp_address_y] as u16;
                    let high_byte = memory.data[zp_address_y.wrapping_add(1)] as u16;

                    let indirect_address = (high_byte << 8) | low_byte;
                    memory.data[indirect_address as usize] = self.a;

                    *cycles = cycles.wrapping_sub(6);
                }
                INS_STX_ZP => {
                    let zp_address = memory.read_byte(cycles, self) as usize;
                    memory.data[zp_address] = self.x;

                    *cycles = cycles.wrapping_sub(3);
                }
                INS_STX_ZPY => {
                    let zp_address = memory.read_byte(cycles, self) as usize;
                    let zp_address_y = zp_address.wrapping_add(self.y as usize);
                    memory.data[zp_address_y] = self.x;

                    *cycles = cycles.wrapping_sub(4);
                }
                INS_STX_ABS => {
                    let absolute_address = memory.read_word(cycles, self) as usize;
                    memory.data[absolute_address] = self.x;

                    *cycles = cycles.wrapping_sub(4);
                }
                INS_STY_ZP => {
                    let zp_address = memory.read_byte(cycles, self) as usize;
                    memory.data[zp_address] = self.y;

                    *cycles = cycles.wrapping_sub(3);
                }
                INS_STY_ZPX => {
                    let zp_address = memory.read_byte(cycles, self) as usize;
                    let zp_address_x = zp_address.wrapping_add(self.x as usize);
                    memory.data[zp_address_x] = self.y;

                    *cycles = cycles.wrapping_sub(4);
                }
                INS_STY_ABS => {
                    let absolute_address = memory.read_word(cycles, self) as usize;
                    memory.data[absolute_address] = self.y;

                    *cycles = cycles.wrapping_sub(4);
                }
                _ => {}
            }
        }
    }
}
