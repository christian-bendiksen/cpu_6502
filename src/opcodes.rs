pub enum Opcode {
    LdaIm = 0xA9,
    LdaZp = 0xA5,
    LdaZpx = 0xB5,
    LdaAbs = 0xAD,
    LdaAbsX = 0xBD,
    LdaAbsY = 0xB9,
    LdaIndX = 0xA1,
    LdaIndY = 0xB1,
    LdxIm = 0xA2,
    LdxZp = 0xA6,
    LdxZpY = 0xB6,
    LdxAbs = 0xAE,
    LdxAbsY = 0xBE,
    LdyIm = 0xA0,
    LdyZp = 0xA4,
    LdyZpX = 0xB4,
    LdyAbs = 0xAC,
    LdyAbsX = 0xBC,
    Jsr = 0x20,
    Rts = 0x60,
    LsrA = 0x4A,
    LsrZp = 0x46,
    LsrZpX = 0x56,
    LsrAbs = 0x4E,
    LsrAbsX = 0x5E,
    Nop = 0xEA,
    OraIm = 0x09,
    OraZp = 0x05,
    OraZpX = 0x15,
    OraAbs = 0x0D,
    OraAbsX = 0x1D,
    OraAbsY = 0x19,
    OraIndX = 0x01,
    OraIndY = 0x11,
    Pha = 0x48,
    Php = 0x08,
    Pla = 0x68,
    Plp = 0x28,
    RolA = 0x2A,
    RolZp = 0x26,
    RolZpX = 0x36,
    RolAbs = 0x2E,
    RolAbsX = 0x3E,
    RorA = 0x6A,
    RorZp = 0x66,
    RorZpX = 0x76,
    RorAbs = 0x6E,
    RorAbsX = 0x7E,
    Rti = 0x40,
    SbcIm = 0xE9,
    SbcZp = 0xE5,
    SbcZpX = 0xF5,
    SbcAbs = 0xED,
    SbcAbsX = 0xFD,
    SbcAbsY = 0xF9,
    SbcIndX = 0xE1,
    SbcIndY = 0xF1,
    Sec = 0x38,
    Sed = 0xF8,
    Sei = 0x78,
    StaZp = 0x85,
    StaZpX = 0x95,
    StaAbs = 0x8D,
    StaAbsX = 0x9D,
    StaAbsY = 0x99,
    StaIndX = 0x81,
    StaIndY = 0x91,
    StxZp = 0x86,
    StxZpY = 0x96,
    StxAbs = 0x8E,
    StyZp = 0x84,
    StyZpX = 0x94,
    StyAbs = 0x8C,
}

impl Opcode {
    pub fn from_byte(byte: u8) -> Option<Self> {
        match byte {
            0xA9 => Some(Opcode::LdaIm),
            0xA5 => Some(Opcode::LdaZp),
            0xB5 => Some(Opcode::LdaZpx),
            0xAD => Some(Opcode::LdaAbs),
            0xBD => Some(Opcode::LdaAbsX),
            0xB9 => Some(Opcode::LdaAbsY),
            0xA1 => Some(Opcode::LdaIndX),
            0xB1 => Some(Opcode::LdaIndY),
            0xA2 => Some(Opcode::LdxIm),
            0xA6 => Some(Opcode::LdxZp),
            0xB6 => Some(Opcode::LdxZpY),
            0xAE => Some(Opcode::LdxAbs),
            0xBE => Some(Opcode::LdxAbsY),
            0xA0 => Some(Opcode::LdyIm),
            0xA4 => Some(Opcode::LdyZp),
            0xB4 => Some(Opcode::LdyZpX),
            0xAC => Some(Opcode::LdyAbs),
            0xBC => Some(Opcode::LdyAbsX),
            0x20 => Some(Opcode::Jsr),
            0x60 => Some(Opcode::Rts),
            0x4A => Some(Opcode::LsrA),
            0x46 => Some(Opcode::LsrZp),
            0x56 => Some(Opcode::LsrZpX),
            0x4E => Some(Opcode::LsrAbs),
            0x5E => Some(Opcode::LsrAbsX),
            0xEA => Some(Opcode::Nop),
            0x09 => Some(Opcode::OraIm),
            0x05 => Some(Opcode::OraZp),
            0x15 => Some(Opcode::OraZpX),
            0x0D => Some(Opcode::OraAbs),
            0x1D => Some(Opcode::OraAbsX),
            0x19 => Some(Opcode::OraAbsY),
            0x01 => Some(Opcode::OraIndX),
            0x11 => Some(Opcode::OraIndY),
            0x48 => Some(Opcode::Pha),
            0x08 => Some(Opcode::Php),
            0x68 => Some(Opcode::Pla),
            0x28 => Some(Opcode::Plp),
            0x2A => Some(Opcode::RolA),
            0x26 => Some(Opcode::RolZp),
            0x36 => Some(Opcode::RolZpX),
            0x2E => Some(Opcode::RolAbs),
            0x3E => Some(Opcode::RolAbsX),
            0x6A => Some(Opcode::RorA),
            0x66 => Some(Opcode::RorZp),
            0x76 => Some(Opcode::RorZpX),
            0x6E => Some(Opcode::RorAbs),
            0x7E => Some(Opcode::RorAbsX),
            0x40 => Some(Opcode::Rti),
            0xE9 => Some(Opcode::SbcIm),
            0xE5 => Some(Opcode::SbcZp),
            0xF5 => Some(Opcode::SbcZpX),
            0xED => Some(Opcode::SbcAbs),
            0xFD => Some(Opcode::SbcAbsX),
            0xF9 => Some(Opcode::SbcAbsY),
            0xE1 => Some(Opcode::SbcIndX),
            0xF1 => Some(Opcode::SbcIndY),
            0x38 => Some(Opcode::Sec),
            0xF8 => Some(Opcode::Sed),
            0x78 => Some(Opcode::Sei),
            0x85 => Some(Opcode::StaZp),
            0x95 => Some(Opcode::StaZpX),
            0x8D => Some(Opcode::StaAbs),
            0x9D => Some(Opcode::StaAbsX),
            0x99 => Some(Opcode::StaAbsY),
            0x81 => Some(Opcode::StaIndX),
            0x91 => Some(Opcode::StaIndY),
            0x86 => Some(Opcode::StxZp),
            0x96 => Some(Opcode::StxZpY),
            0x8E => Some(Opcode::StxAbs),
            0x84 => Some(Opcode::StyZp),
            0x94 => Some(Opcode::StyZpX),
            0x8C => Some(Opcode::StyAbs),
            _ => None,
        }
    }
}
