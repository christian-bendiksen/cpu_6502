use crate::mem::Mem;
use crate::opcodes::Opcode;

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

    fn lda_im(&mut self, cycles: &mut u32, memory: &mut Mem) {
        // Read the next byte from memory, which is the immediate value for LDA.
        let value = memory.read_byte(cycles, self);
        // Load the read value into the accumulator.
        self.a = value;
        // Update the Zero and Negative flags based on the new accumulator value.
        self.set_zero_and_negative_flags(self.a);
        *cycles = cycles.wrapping_sub(1);
    }

    fn lda_zp(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let zero_page_address = memory.read_byte(cycles, self) as usize;
        self.a = memory.data[zero_page_address];
        self.set_zero_and_negative_flags(self.a);

        *cycles = cycles.wrapping_sub(2);
    }

    fn lda_zpx(&mut self, cycles: &mut u32, memory: &mut Mem) {
        // Read the next byte (zero-page address) and add the X register to it.
        let zero_page_address = memory.read_byte(cycles, self) as usize;
        // Wrap the address around the zero page boundary (0x0FF).
        let zero_page_address_x = zero_page_address.wrapping_add(self.x as usize) & 0xFF;
        // Load the calculated address into the accumulator.
        self.a = memory.data[zero_page_address_x];
        self.set_zero_and_negative_flags(self.a);

        *cycles = cycles.wrapping_sub(3);
    }

    fn lda_abs(&mut self, cycles: &mut u32, memory: &mut Mem) {
        // Read a 16-bit (two-byte) address from the current program counter position.
        let absolute_address = memory.read_word(cycles, self);
        // Load the value at the fetched address into the accumulator
        self.a = memory.data[absolute_address as usize];
        self.set_zero_and_negative_flags(self.a);

        *cycles = cycles.wrapping_sub(2);
    }

    fn lda_absx(&mut self, cycles: &mut u32, memory: &mut Mem) {
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

    fn lda_absy(&mut self, cycles: &mut u32, memory: &mut Mem) {
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

    fn lda_indx(&mut self, cycles: &mut u32, memory: &mut Mem) {
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

    fn lda_indy(&mut self, cycles: &mut u32, memory: &mut Mem) {
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

    fn ldx_im(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let value = memory.read_byte(cycles, self);
        self.x = value;
        self.set_zero_and_negative_flags(self.x);

        *cycles = cycles.wrapping_sub(1);
    }

    fn ldx_zp(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let zero_page_address = memory.read_byte(cycles, self) as usize;
        self.x = memory.data[zero_page_address];
        self.set_zero_and_negative_flags(self.x);

        *cycles = cycles.wrapping_sub(2);
    }

    fn ldx_zpy(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let zero_page_address = memory.read_byte(cycles, self) as usize;
        let zero_page_address_y = zero_page_address.wrapping_add(self.y as usize) & 0xFF;
        self.x = memory.data[zero_page_address_y];
        self.set_zero_and_negative_flags(self.x);

        *cycles = cycles.wrapping_sub(3);
    }

    fn ldx_abs(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let absolute_address = memory.read_word(cycles, self);
        self.x = memory.data[absolute_address as usize];

        self.set_zero_and_negative_flags(self.x);
        *cycles = cycles.wrapping_sub(2);
    }

    fn ldx_absy(&mut self, cycles: &mut u32, memory: &mut Mem) {
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

    fn ldy_im(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let value = memory.read_byte(cycles, self);
        self.y = value;
        self.set_zero_and_negative_flags(self.y);

        *cycles = cycles.wrapping_sub(1);
    }

    fn ldy_zp(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let zero_page_address = memory.read_byte(cycles, self) as usize;
        self.y = memory.data[zero_page_address];
        self.set_zero_and_negative_flags(self.y);

        *cycles = cycles.wrapping_sub(2);
    }

    fn ldy_zpx(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let zero_page_address = memory.read_byte(cycles, self) as usize;
        let zero_page_address_x = zero_page_address.wrapping_add(self.x as usize) & 0xFF;
        self.y = memory.data[zero_page_address_x];
        self.set_zero_and_negative_flags(self.y);

        *cycles = cycles.wrapping_sub(3);
    }

    fn ldy_abs(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let absolute_address = memory.read_word(cycles, self) as usize;
        self.y = memory.data[absolute_address];
        self.set_zero_and_negative_flags(self.y);

        *cycles = cycles.wrapping_sub(2);
    }
    fn ldy_absx(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let absolute_address = memory.read_word(cycles, self) as usize;
        let absolute_address_x = absolute_address.wrapping_add(self.x as usize);
        let page_crossed = (absolute_address & 0xFF00) != (absolute_address_x & 0xFF00);

        self.y = memory.data[absolute_address_x];

        *cycles = cycles.wrapping_sub(2);
        if page_crossed {
            *cycles = cycles.wrapping_sub(1);
        }
    }

    fn jsr(&mut self, cycles: &mut u32, memory: &mut Mem) {
        // Read the next two bytes for the subroutine address.
        let address = memory.read_word(cycles, self);
        // Push the current program counter (minus one) onto the stack before jumping.
        memory.push_stack_word(cycles, self, self.pc - 1);
        // Set the program counter to the subroutine address.
        self.pc = address;
        // Subtract 2 cycles more cycles for a total of 6 for the JSR operation.
        *cycles = cycles.wrapping_sub(2);
    }

    fn rts(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let address = memory.pull_stack_word(cycles, self);
        self.pc = address.wrapping_add(1);
        *cycles = cycles.saturating_sub(6);
    }

    fn lsr_a(&mut self, cycles: &mut u32) {
        self.c = self.a & 0x01 != 0;
        self.a >>= 1;
        self.set_zero_and_negative_flags(self.a);

        *cycles = cycles.wrapping_sub(2);
    }

    fn lsr_zp(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let zero_page_address = memory.read_byte(cycles, self) as usize;
        let zero_page_fetched = memory.data[zero_page_address];

        self.c = zero_page_fetched & 0x01 != 0;

        let zero_page_shifted = zero_page_fetched >> 1;

        memory.data[zero_page_address] = zero_page_shifted;

        self.set_zero_and_negative_flags(zero_page_shifted);

        *cycles = cycles.wrapping_sub(4);
    }

    fn lsr_zpx(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let zero_page_address = memory.read_byte(cycles, self) as usize;
        let zero_page_address_x = zero_page_address.wrapping_add(self.x as usize) & 0xFF;
        let zero_page_fetched = memory.data[zero_page_address_x];

        self.c = zero_page_fetched & 0x01 != 0;

        let zero_page_shifted = zero_page_fetched >> 1;

        memory.data[zero_page_address_x] = zero_page_shifted;

        self.set_zero_and_negative_flags(zero_page_shifted);

        *cycles = cycles.wrapping_sub(6);
    }

    fn lsr_abs(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let absolute_address = memory.read_word(cycles, self) as usize;
        let absolute_fetched = memory.data[absolute_address];

        self.c = absolute_fetched & 0x01 != 0;

        let absolute_shifted = absolute_fetched >> 1;

        memory.data[absolute_address] = absolute_shifted;

        self.set_zero_and_negative_flags(absolute_shifted);

        *cycles = cycles.wrapping_sub(4);
    }

    fn lsr_absx(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let absolute_address = memory.read_word(cycles, self) as usize;
        let absolute_address_x = absolute_address.wrapping_add(self.x as usize);
        let absolute_address_fetched = memory.data[absolute_address_x];

        self.c = absolute_address_fetched & 0x01 != 0;

        let absolute_address_shifted = absolute_address_fetched >> 1;

        memory.data[absolute_address_x] = absolute_address_shifted;

        self.set_zero_and_negative_flags(absolute_address_shifted);

        *cycles = cycles.wrapping_sub(5);
    }

    fn nop(&mut self, cycles: &mut u32) {
        *cycles = cycles.saturating_sub(1);
    }

    fn ora_im(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let address = memory.read_byte(cycles, self);
        self.a |= address;

        self.set_zero_and_negative_flags(self.a);

        *cycles = cycles.wrapping_sub(1);
    }

    fn ora_zp(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let zero_page_address = memory.read_byte(cycles, self) as usize;
        self.a |= memory.data[zero_page_address];

        self.set_zero_and_negative_flags(self.a);

        *cycles = cycles.wrapping_sub(2);
    }

    fn ora_zpx(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let zero_page_address = memory.read_byte(cycles, self) as usize;
        let zero_page_address_x = zero_page_address.wrapping_add(self.x as usize) & 0xFF;
        self.a |= memory.data[zero_page_address_x];

        self.set_zero_and_negative_flags(self.a);

        *cycles = cycles.wrapping_sub(3);
    }

    fn ora_abs(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let absolute_address = memory.read_word(cycles, self) as usize;
        self.a |= memory.data[absolute_address];

        self.set_zero_and_negative_flags(self.a);

        *cycles = cycles.wrapping_sub(2);
    }

    fn ora_absx(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let absolute_address = memory.read_word(cycles, self) as usize;
        let absolute_address_x = absolute_address.wrapping_add(self.x as usize);
        let page_crossed = (absolute_address & 0xFF00) != (absolute_address_x & 0xFF00);

        self.a |= memory.data[absolute_address_x];

        *cycles = cycles.wrapping_sub(2);
        if page_crossed {
            *cycles = cycles.wrapping_sub(1);
        }
    }

    fn ora_absy(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let absolute_address = memory.read_word(cycles, self) as usize;
        let absolute_address_y = absolute_address.wrapping_add(self.y as usize);
        let page_crossed = (absolute_address & 0xFF00) != (absolute_address_y & 0xFF00);

        self.a |= memory.data[absolute_address_y];

        *cycles = cycles.wrapping_sub(2);
        if page_crossed {
            *cycles = cycles.wrapping_sub(1);
        }
    }

    fn ora_indx(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let address = memory.read_byte(cycles, self) as usize;
        let table_address = address.wrapping_add(self.x as usize);

        let low_byte = memory.data[table_address] as u16;
        let high_byte = memory.data[table_address.wrapping_add(1)] as u16;

        let indirect_address = (high_byte << 8) | low_byte;

        self.a |= memory.data[indirect_address as usize];

        *cycles = cycles.wrapping_sub(5);
    }

    fn ora_indy(&mut self, cycles: &mut u32, memory: &mut Mem) {
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

    fn pha(&mut self, cycles: &mut u32, memory: &mut Mem) {
        memory.push_stack(cycles, self, self.a);

        *cycles = cycles.wrapping_sub(2);
    }

    fn php(&mut self, cycles: &mut u32, memory: &mut Mem) {
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

    fn pla(&mut self, cycles: &mut u32, memory: &mut Mem) {
        self.a = memory.pull_stack(cycles, self);
        self.set_zero_and_negative_flags(self.a);

        *cycles = cycles.wrapping_sub(3);
    }

    fn plp(&mut self, cycles: &mut u32, memory: &mut Mem) {
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

    fn rol_a(&mut self, cycles: &mut u32) {
        self.rol_rotate_left(self.a);

        *cycles = cycles.wrapping_sub(2);
    }

    fn rol_zp(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let zero_page_address = memory.read_byte(cycles, self) as usize;
        self.rol_rotate_left(memory.data[zero_page_address]);

        *cycles = cycles.wrapping_sub(4);
    }

    fn rol_zpx(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let zero_page_address = memory.read_byte(cycles, self) as usize;
        let zero_page_address_x = zero_page_address.wrapping_add(self.x as usize) & 0xFF;
        self.rol_rotate_left(memory.data[zero_page_address_x]);

        *cycles = cycles.wrapping_sub(5);
    }

    fn rol_abs(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let absolute_address = memory.read_word(cycles, self) as usize;
        self.rol_rotate_left(memory.data[absolute_address]);

        *cycles = cycles.wrapping_sub(4);
    }

    fn rol_absx(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let absolute_address = memory.read_word(cycles, self) as usize;
        let absolute_address_x = absolute_address.wrapping_add(self.x as usize) & 0xFF;
        self.rol_rotate_left(memory.data[absolute_address_x]);

        *cycles = cycles.wrapping_sub(5);
    }

    fn ror_a(&mut self, cycles: &mut u32) {
        self.ror_rotate_right(self.a);
        self.set_zero_and_negative_flags(self.a);

        *cycles = cycles.wrapping_sub(2);
    }

    fn ror_zp(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let zero_page_address = memory.read_byte(cycles, self) as usize;
        self.ror_rotate_right(memory.data[zero_page_address]);

        *cycles = cycles.wrapping_sub(4);
    }

    fn ror_zpx(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let zero_page_address = memory.read_byte(cycles, self) as usize;
        let zero_page_address_x = zero_page_address.wrapping_add(self.x as usize) & 0xFF;

        self.ror_rotate_right(memory.data[zero_page_address_x]);

        *cycles = cycles.wrapping_sub(5);
    }

    fn ror_abs(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let absolute_address = memory.read_word(cycles, self) as usize;
        self.ror_rotate_right(memory.data[absolute_address]);

        *cycles = cycles.wrapping_sub(4);
    }

    fn ror_absx(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let absolute_address = memory.read_word(cycles, self) as usize;
        let absolute_address_x = absolute_address.wrapping_add(self.x as usize);

        self.ror_rotate_right(memory.data[absolute_address_x]);

        *cycles = cycles.wrapping_sub(5);
    }

    fn rti(&mut self, cycles: &mut u32, memory: &mut Mem) {
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

    fn sbc_im(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let value = memory.read_byte(cycles, self);
        self.subtract_with_carry(value);

        *cycles = cycles.wrapping_sub(1);
    }

    fn sbc_zp(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let value = memory.read_byte(cycles, self);
        let value_zp = memory.data[value as usize];
        self.subtract_with_carry(value_zp);

        *cycles = cycles.wrapping_sub(2);
    }

    fn sbc_zpx(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let zp_address = memory.read_byte(cycles, self) as usize;
        let value_zpx = memory.data[zp_address.wrapping_add(self.x as usize)];
        self.subtract_with_carry(value_zpx);

        *cycles = cycles.wrapping_sub(4);
    }

    fn sbc_abs(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let absolute_address = memory.read_word(cycles, self);
        let value_abs = memory.data[absolute_address as usize];

        self.subtract_with_carry(value_abs);

        *cycles = cycles.wrapping_sub(4);
    }

    fn sbc_absx(&mut self, cycles: &mut u32, memory: &mut Mem) {
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

    fn sbc_absy(&mut self, cycles: &mut u32, memory: &mut Mem) {
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

    fn sbc_indx(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let zp_address = memory.read_byte(cycles, self) as usize;
        let zp_address_x = zp_address.wrapping_add(self.x as usize);

        let low_byte = memory.data[zp_address_x] as u16;
        let high_byte = memory.data[zp_address_x.wrapping_add(1)] as u16;

        let indirect_address = (high_byte << 8) | low_byte;

        self.subtract_with_carry(indirect_address as u8);

        *cycles = cycles.wrapping_sub(6);
    }

    fn sbc_indy(&mut self, cycles: &mut u32, memory: &mut Mem) {
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

    fn sec(&mut self) {
        self.c = true;
    }

    fn sed(&mut self) {
        self.d = true;
    }

    fn sei(&mut self) {
        self.i = true;
    }

    fn sta_zp(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let zp_address = memory.read_byte(cycles, self) as usize;
        memory.data[zp_address] = self.a;

        *cycles = cycles.wrapping_sub(3);
    }

    fn sta_zpx(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let zp_address = memory.read_byte(cycles, self) as usize;
        let zp_address_x = zp_address.wrapping_add(self.x as usize);
        memory.data[zp_address_x] = self.a;

        *cycles = cycles.wrapping_add(4);
    }

    fn sta_abs(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let absolute_address = memory.read_word(cycles, self);
        memory.data[absolute_address as usize] = self.a;

        *cycles = cycles.wrapping_sub(4);
    }

    fn sta_absx(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let absolute_address = memory.read_word(cycles, self) as usize;
        let absolute_address_x = absolute_address.wrapping_add(self.x as usize);
        memory.data[absolute_address_x] = self.a;

        *cycles = cycles.wrapping_sub(5);
    }

    fn sta_absy(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let absolute_address = memory.read_word(cycles, self) as usize;
        let absolute_address_y = absolute_address.wrapping_add(self.y as usize);
        memory.data[absolute_address_y] = self.a;

        *cycles = cycles.wrapping_sub(5);
    }

    fn sta_indx(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let zp_address = memory.read_word(cycles, self) as usize;
        let zp_address_x = zp_address.wrapping_add(self.x as usize);

        let low_byte = memory.data[zp_address_x] as u16;
        let high_byte = memory.data[zp_address_x.wrapping_add(1)] as u16;

        let indirect_address = (high_byte << 8) | low_byte;
        memory.data[indirect_address as usize] = self.a;

        *cycles = cycles.wrapping_sub(6);
    }

    fn sta_indy(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let zp_address = memory.read_word(cycles, self) as usize;
        let zp_address_y = zp_address.wrapping_add(self.y as usize);

        let low_byte = memory.data[zp_address_y] as u16;
        let high_byte = memory.data[zp_address_y.wrapping_add(1)] as u16;

        let indirect_address = (high_byte << 8) | low_byte;
        memory.data[indirect_address as usize] = self.a;

        *cycles = cycles.wrapping_sub(6);
    }

    fn stx_zp(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let zp_address = memory.read_byte(cycles, self) as usize;
        memory.data[zp_address] = self.x;

        *cycles = cycles.wrapping_sub(3);
    }

    fn stx_zpy(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let zp_address = memory.read_byte(cycles, self) as usize;
        let zp_address_y = zp_address.wrapping_add(self.y as usize);
        memory.data[zp_address_y] = self.x;

        *cycles = cycles.wrapping_sub(4);
    }

    fn stx_abs(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let absolute_address = memory.read_word(cycles, self) as usize;
        memory.data[absolute_address] = self.x;

        *cycles = cycles.wrapping_sub(4);
    }

    fn sty_zp(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let zp_address = memory.read_byte(cycles, self) as usize;
        memory.data[zp_address] = self.y;

        *cycles = cycles.wrapping_sub(3);
    }

    fn sty_zpx(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let zp_address = memory.read_byte(cycles, self) as usize;
        let zp_address_x = zp_address.wrapping_add(self.x as usize);
        memory.data[zp_address_x] = self.y;

        *cycles = cycles.wrapping_sub(4);
    }

    fn sty_abs(&mut self, cycles: &mut u32, memory: &mut Mem) {
        let absolute_address = memory.read_word(cycles, self) as usize;
        memory.data[absolute_address] = self.y;

        *cycles = cycles.wrapping_sub(4);
    }
    // Execute CPU instructions.
    // This function drives the CPU's execution based on the opcodes.k
    //
    // Arguments:
    // * `memory`: mutable reference to the CPU's memory.
    // * `cycles`: mutable reference to the number of cycles remaining for the CPU to execute.
    pub fn execute_instruction(&mut self, opcode: Opcode, memory: &mut Mem, cycles: &mut u32) {
        // let opcode = Opcode::from_byte(opcode_byte).expect("Could not get opcode");
        match opcode {
            Opcode::LdaIm => self.lda_im(cycles, memory),
            Opcode::LdaZp => self.lda_zp(cycles, memory),
            Opcode::LdaZpx => self.lda_zpx(cycles, memory),
            Opcode::LdaAbs => self.lda_abs(cycles, memory),
            Opcode::LdaAbsX => self.lda_absx(cycles, memory),
            Opcode::LdaAbsY => self.lda_absy(cycles, memory),
            Opcode::LdaIndX => self.lda_indx(cycles, memory),
            Opcode::LdaIndY => self.lda_indy(cycles, memory),
            Opcode::LdxIm => self.ldx_im(cycles, memory),
            Opcode::LdxZp => self.ldx_zp(cycles, memory),
            Opcode::LdxZpY => self.ldx_zpy(cycles, memory),
            Opcode::LdxAbs => self.ldx_abs(cycles, memory),
            Opcode::LdxAbsY => self.ldx_absy(cycles, memory),
            Opcode::LdyIm => self.ldy_im(cycles, memory),
            Opcode::LdyZp => self.ldy_zp(cycles, memory),
            Opcode::LdyZpX => self.ldy_zpx(cycles, memory),
            Opcode::LdyAbs => self.ldy_abs(cycles, memory),
            Opcode::LdyAbsX => self.ldy_absx(cycles, memory),
            Opcode::Jsr => self.jsr(cycles, memory),
            Opcode::Rts => self.rts(cycles, memory),
            Opcode::LsrA => self.lsr_a(cycles),
            Opcode::LsrZp => self.lsr_zp(cycles, memory),
            Opcode::LsrZpX => self.lsr_zpx(cycles, memory),
            Opcode::LsrAbs => self.lsr_abs(cycles, memory),
            Opcode::LsrAbsX => self.lsr_absx(cycles, memory),
            Opcode::Nop => self.nop(cycles),
            Opcode::OraIm => self.ora_im(cycles, memory),
            Opcode::OraZp => self.ora_zp(cycles, memory),
            Opcode::OraZpX => self.ora_zpx(cycles, memory),
            Opcode::OraAbs => self.ora_abs(cycles, memory),
            Opcode::OraAbsX => self.ora_absx(cycles, memory),
            Opcode::OraAbsY => self.ora_absy(cycles, memory),
            Opcode::OraIndX => self.ora_indx(cycles, memory),
            Opcode::OraIndY => self.ora_indy(cycles, memory),
            Opcode::Pha => self.pha(cycles, memory),
            Opcode::Php => self.php(cycles, memory),
            Opcode::Pla => self.pla(cycles, memory),
            Opcode::Plp => self.plp(cycles, memory),
            Opcode::RolA => self.rol_a(cycles),
            Opcode::RolZp => self.rol_zp(cycles, memory),
            Opcode::RolZpX => self.rol_zpx(cycles, memory),
            Opcode::RolAbs => self.rol_abs(cycles, memory),
            Opcode::RolAbsX => self.rol_absx(cycles, memory),
            Opcode::RorA => self.ror_a(cycles),
            Opcode::RorZp => self.ror_zp(cycles, memory),
            Opcode::RorZpX => self.ror_zpx(cycles, memory),
            Opcode::RorAbs => self.ror_abs(cycles, memory),
            Opcode::RorAbsX => self.ror_absx(cycles, memory),
            Opcode::Rti => self.rti(cycles, memory),
            Opcode::SbcIm => self.sbc_im(cycles, memory),
            Opcode::SbcZp => self.sbc_zp(cycles, memory),
            Opcode::SbcZpX => self.sbc_zpx(cycles, memory),
            Opcode::SbcAbs => self.sbc_abs(cycles, memory),
            Opcode::SbcAbsX => self.sbc_absx(cycles, memory),
            Opcode::SbcAbsY => self.sbc_absy(cycles, memory),
            Opcode::SbcIndX => self.sbc_indx(cycles, memory),
            Opcode::SbcIndY => self.sbc_indy(cycles, memory),
            Opcode::Sec => self.sec(),
            Opcode::Sed => self.sed(),
            Opcode::Sei => self.sei(),
            Opcode::StaZp => self.sta_zp(cycles, memory),
            Opcode::StaZpX => self.sta_zpx(cycles, memory),
            Opcode::StaAbs => self.sta_abs(cycles, memory),
            Opcode::StaAbsX => self.sta_absx(cycles, memory),
            Opcode::StaAbsY => self.sta_absy(cycles, memory),
            Opcode::StaIndX => self.sta_indx(cycles, memory),
            Opcode::StaIndY => self.sta_indy(cycles, memory),
            Opcode::StxZp => self.stx_zp(cycles, memory),
            Opcode::StxZpY => self.stx_zpy(cycles, memory),
            Opcode::StxAbs => self.stx_abs(cycles, memory),
            Opcode::StyZp => self.sty_zp(cycles, memory),
            Opcode::StyZpX => self.sty_zpx(cycles, memory),
            Opcode::StyAbs => self.sty_abs(cycles, memory),
        }
    }
}
