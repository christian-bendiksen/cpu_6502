const MAX_MEM: usize = 1024 * 64;
const INS_LDA_IM: u8 = 0xA9;
const INS_LDA_ZP: u8 = 0xA5;
const INS_LDA_ZPX: u8 = 0xB5;

struct Mem {
    data: [u8; MAX_MEM],
}

impl Mem {
    fn new() -> Mem {
        Mem { data: [0; MAX_MEM] }
    }
    fn write(&mut self, address: usize, value: u8) {
        self.data[address] = value;
    }
}

struct CPU {
    pc: u16,
    sp: u16,
    a: u8,
    x: u8,
    y: u8,
    // flags
    c: bool,
    z: bool,
    i: bool,
    d: bool,
    b: bool,
    v: bool,
    n: bool,
}

impl CPU {
    fn new() -> CPU {
        CPU {
            pc: 0xFFFD, // Program counter
            sp: 0x0100, // Stack Pointer
            a: 0,       // Registers
            x: 0,
            y: 0,
            c: false, // Flags
            z: false,
            i: false,
            d: false,
            b: false,
            v: false,
            n: false,
        }
    }

    #[allow(dead_code)]
    // reset the CPU
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

    // Read a byte from memory.
    fn read_byte(&mut self, cycles: &mut u32, memory: &Mem) -> u8 {
        let data = memory.data[self.pc as usize];
        self.pc = self.pc.wrapping_add(1);
        *cycles = cycles.saturating_sub(1);
        data
    }

    // Execute instructions
    fn execute(&mut self, memory: &Mem, cycles: &mut u32) {
        while *cycles > 0 {
            let ins = self.read_byte(cycles, memory);
            match ins {
                INS_LDA_IM => {
                    let value = self.read_byte(cycles, memory);
                    self.a = value;
                    self.z = self.a == 0;
                    self.n = (self.a & 0b1000_0000) != 0;
                }
                INS_LDA_ZP => {
                    let zero_page_address = self.read_byte(cycles, memory) as usize;
                    dbg!("{}", zero_page_address);
                    self.a = memory.data[zero_page_address];
                    self.z = self.a == 0;
                    self.n = (self.a & 0b1000_0000) != 0;
                }
                INS_LDA_ZPX => {
                    let zero_page_address = self.read_byte(cycles, memory) as usize;
                    let zero_page_address_x =
                        zero_page_address.wrapping_add(self.x as usize) & 0x00FF;
                    self.a = memory.data[zero_page_address_x];
                    self.z = self.a == 0;
                    self.n = (self.a & 0b1000_0000) != 0;
                }
                _ => {}
            }
        }
    }
}

fn main() {
    let mut memory = Mem::new();
    let mut cpu = CPU::new();

    // Write program into memory
    memory.write(0xFFFC, INS_LDA_ZP);
    memory.write(0xFFFD, 0x42);
    memory.write(0x0042, 0x84);

    // Set the program counter to the start of the program.
    cpu.pc = 0xFFFC;

    let mut cycles: u32 = 3;
    cpu.execute(&memory, &mut cycles);

    println!("Accumulator: {}", cpu.a);
    println!("Zero Flag: {}", cpu.z);
    println!("Negative Flag: {}", cpu.n);
}