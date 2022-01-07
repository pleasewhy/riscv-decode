use super::consts::*;
use crate::*;

const ADDI_OPCODE: u32 = 0b0010011;
const ADDIW_OPCODE: u32 = 0b0011011;
// 1111111100
pub fn decode_q00(i: u32) -> DecodingResult {
    match i >> 13 {
        0b000 if i == 0 => Ok(Instruction::Illegal),
        0b000 => {
            let rd = ((i & 0b11100) >> 2) + 8;
            let mut uimm = 0;
            uimm |= (i & 0b100000) >> 2; // uimm[3] = inst[5]
            uimm |= (i & 0b1000000) >> 4; // uimm[2] = inst[6]
            uimm |= (i & 0b11110000000) >> 1; // uimm[6:9] = inst[7:10]
            uimm |= (i & 0b1100000000000) >> 7; // uimm[4:5] = inst[11:12]
            Ok(Instruction::Addi(IType::new(ADDI_OPCODE, rd, SP, uimm)))
        } // C.ADDI4SPN -> addi rd' + 8, x2, uimm
        0b001 => Err(DecodingError::Unimplemented), // C.FLD
        0b010 => Ok(Instruction::Lw(IType(
            ((i & 0x1c00) << 13)      // imm[5:3]
            | ((i & 0x380) << 8)      // rs1[2:0]
            | ((i & 0x40) << 16)      // imm[2]
            | ((i & 0x20) << 21)      // imm[6]
            | ((i & 0x1c) << 5)       // rd[2:0]
            | 0b_01000_010_01000_0000011,
        ))),
        0b011 => Ok(Instruction::Ld(IType(
            // C.LD (C.FLW in RV32)
            ((i & 0x1c00) << 13)      // imm[5:3]
            | ((i & 0x380) << 8)      // rs1[2:0]
            | ((i & 0x60) << 21)      // imm[7:6]
            | ((i & 0x1c) << 5)       // rd[2:0]
            | 0b_01000_011_01000_0000011,
        ))),
        0b100 => Err(DecodingError::Unimplemented), // reserved
        0b101 => Err(DecodingError::Unimplemented), // C.FSD
        0b110 => Ok(Instruction::Sw(SType(
            // C.SW
            ((i & 0x1000) << 13)      // imm[5]
            | ((i & 0xc00))           // imm[4:3]
            | ((i & 0x380) << 8)      // rs1[2:0]
            | ((i & 0x40) << 3)       // imm[2]
            | ((i & 0x20) << 21)      // imm[6]
            | ((i & 0x1c) << 18)      // rs2[2:0]
            | 0b_01000_01000_010_00000_0100011,
        ))),
        0b111 => Ok(Instruction::Sd(SType(
            // C.SD (C.FSW in RV32)
            ((i & 0x1000) << 13)      // imm[5]
            | ((i & 0xc00))           // imm[4:3]
            | ((i & 0x380) << 8)      // rs1[2:0]
            | ((i & 0x60) << 21)      // imm[7:6]
            | ((i & 0x1c) << 18)      // rs2[2:0]
            | 0b_01000_01000_011_00000_0100011,
        ))),
        _ => Err(DecodingError::Unimplemented),
    }
}

fn get_11_10_bit(i: u32) -> u32 {
    (i & 0b110000000000) >> 10
}

fn get_12_and_6_5_bit(i: u32) -> u32 {
    (i & 0b1000000000000) >> 10 | ((i & 0b1100000) >> 5)
}

pub fn decode_q01(i: u32) -> DecodingResult {
    match i >> 13 {
        0b000 if i == 1 => Ok(Instruction::Addi(IType::new(ADDI_OPCODE, X0, X0, 0))), // C.NOP(HINT, nzimm̸=0)
        0b000 => {
            let rd = (i & 0b111110000000) >> 7;
            let mut imm = (i & 0b1111100) >> 2; // imm[0:4] = inst[2:6]
            imm |= (i & 0b1000000000000) >> 7; // imm[5] = inst[12]
            imm = (((imm << 26) as i32) >> 26) as u32; // sign extend
            assert!(
                imm != 0,
                "if C.ADDI's nzimm=0, this degrades to HINT instruction"
            );
            Ok(Instruction::Addi(IType::new(ADDI_OPCODE, rd, rd, imm)))
        } // C.ADDI (HINT, nzimm=0) rd, imm -> addi rd, rd, imm
        0b001 => {
            let rd = (i & 0b111110000000) >> 7;
            assert!(rd != 0, "C.ADDIW rd can't be X0");
            let mut imm = (i & 0b1111100) >> 2; // imm[0:4] = inst[2:6]
            imm |= (i & 0b1000000000000) >> 7; // imm[5] = inst[12]
            imm = (((imm << 26) as i32) >> 26) as u32; // sign extend
            Ok(Instruction::Addiw(IType::new(ADDIW_OPCODE, rd, rd, imm)))
        } // C.ADDIW rd, imm(rd != 0) => addi rd, rd, imm
        0b010 => {
            let rd = (i & 0b111110000000) >> 7;
            assert!(
                rd != 0,
                "if C.ADDI's rd=0, this degrades to HINT instruction"
            );
            let mut imm = (i & 0b1111100) >> 2; // imm[0:4] = inst[2:6]
            imm |= (i & 0b1000000000000) >> 7; // imm[5] = inst[12]
            imm = (((imm << 26) as i32) >> 26) as u32; // sign extend
            Ok(Instruction::Addiw(IType::new(ADDI_OPCODE, rd, X0, imm)))
        } // C.LI(HINT, rd=0) rd, imm => addi rd, x0, imm
        0b011 if (i & 0b111110000000) >> 7 == 2 => {
            let mut imm = 0u32;
            imm |= (i & 0b1000000) >> 2; // imm[4] = inst[6]
            imm |= (i & 0b100) << 3; // imm[5] = inst[2]
            imm |= (i & 0b100000) << 1; // imm[6] = inst[5]
            imm |= (i & 0b11000) << 4; // imm[8:7] = inst[4:3]
            imm |= (i & 0b1000000000000) >> 3; // imm[9] = inst[12]

            imm = (((imm << 22) as i32) >> 22) as u32; // sign extend
            assert!(imm != 0, "C.ADDI16SP imm can't be 0");
            Ok(Instruction::Addi(IType::new(ADDI_OPCODE, SP, SP, imm)))
        } // C.ADDI16SP (RES, nzimm=0)
        0b011 => Err(DecodingError::Unimplemented), // C.LUI (RES, nzimm=0; HINT, rd=0)
        0b100 if get_11_10_bit(i) == 0b00 => Err(DecodingError::Unimplemented), // C.SRLI (RV32 NSE, nzuimm[5]=1)
        0b100 if get_11_10_bit(i) == 0b01 => Err(DecodingError::Unimplemented), // C.SRAI (RV32 NSE, nzuimm[5]=1)
        0b100 if get_11_10_bit(i) == 0b10 => Err(DecodingError::Unimplemented), // C.ANDI
        0b100 if get_12_and_6_5_bit(i) == 0b000 => Err(DecodingError::Unimplemented), // C.SUB
        0b100 if get_12_and_6_5_bit(i) == 0b001 => Err(DecodingError::Unimplemented), // C.XOR
        0b100 if get_12_and_6_5_bit(i) == 0b010 => Err(DecodingError::Unimplemented), // C.OR
        0b100 if get_12_and_6_5_bit(i) == 0b011 => Err(DecodingError::Unimplemented), // C.AND
        0b100 if get_12_and_6_5_bit(i) == 0b100 => Err(DecodingError::Unimplemented), // C.SUBW (RV64/128; RV32 RES)
        0b100 if get_12_and_6_5_bit(i) == 0b101 => Err(DecodingError::Unimplemented), // C.ADDW (RV64/128; RV32 RES)
        0b100 if get_12_and_6_5_bit(i) == 0b110 => Err(DecodingError::Reserved),      // Reserved
        0b100 if get_12_and_6_5_bit(i) == 0b111 => Err(DecodingError::Reserved),      // Reserved
        0b101 => Err(DecodingError::Unimplemented),                                   // C.J
        0b110 => Err(DecodingError::Unimplemented),                                   // C.BEQZ
        0b111 => Err(DecodingError::Unimplemented),                                   // C.BNEZ
        _ => Err(DecodingError::Unknown),
    }
}

pub fn decode_q10(_i: u32) -> DecodingResult {
    Err(DecodingError::Unimplemented)
}

#[cfg(test)]
mod tests {
    use super::Instruction::*;
    use super::*;

    #[test]
    fn q00() {
        assert_eq!(decode_q00(0x6188).unwrap(), Ld(IType(0x0005b503))); // ld a0,0(a1)
        assert_eq!(decode_q00(0x75e0).unwrap(), Ld(IType(0x0e85b403))); // ld s0,232(a1)
        assert_eq!(decode_q00(0x43b0).unwrap(), Lw(IType(0x0407a603))); // lw a2,64(a5)
        assert_eq!(decode_q00(0xe188).unwrap(), Sd(SType(0x00a5b023))); // sd a0,0(a1)
        assert_eq!(decode_q00(0xf5e0).unwrap(), Sd(SType(0x0e85b423))); // sd s0,232(a1)
        assert_eq!(decode_q00(0xc3b0).unwrap(), Sw(SType(0x04c7a023))); // sw a2,64(a5)

        // C.ADDI4SPN
        assert_eq!(decode_q00(0x0044).unwrap(), Addi(IType(0x00410493))); // addi s1,sp,4
        assert_eq!(decode_q00(0x0808).unwrap(), Addi(IType(0x01010513))); // addi a0,sp,16
        assert_eq!(decode_q00(0x040c).unwrap(), Addi(IType(0x20010593))); // addi a1,sp,512
        assert_eq!(decode_q00(0x1ffc).unwrap(), Addi(IType(0x3FC10793))); // addi a5,sp,1020

        // C.ADDIW
        assert_eq!(decode_q01(0x30fd).unwrap(), Addiw(IType(0xFFF0809B))); // addiw   ra,ra,-1
        assert_eq!(decode_q01(0x34fd).unwrap(), Addiw(IType(0xFFF4849B))); // addiw   s1,s1,-1
        assert_eq!(decode_q01(0x36ed).unwrap(), Addiw(IType(0xFFB6869B))); // addiw   a3,a3,-5
        assert_eq!(decode_q01(0x3ad9).unwrap(), Addiw(IType(0xFF6A8A9B))); // addiw   s5,s5,-10
        assert_eq!(decode_q01(0x2ffd).unwrap(), Addiw(IType(0x01FF8F9B))); // addiw   t6,t6,31

        // C.ADDI
        assert_eq!(decode_q01(0x10fd).unwrap(), Addi(IType(0xFFF08093))); // addi   ra,ra,-1
        assert_eq!(decode_q01(0x14fd).unwrap(), Addi(IType(0xFFF48493))); // addi   s1,s1,-1
        assert_eq!(decode_q01(0x16ed).unwrap(), Addi(IType(0xFFB68693))); // addi   a3,a3,-5
        assert_eq!(decode_q01(0x1ad9).unwrap(), Addi(IType(0xFF6A8A93))); // addi   s5,s5,-10
        assert_eq!(decode_q01(0x0ffd).unwrap(), Addi(IType(0x01FF8F93))); // addi   t6,t6,31

        // C.LI
        assert_eq!(decode_q01(0x50fd).unwrap(), Addiw(IType(0xFFF00093))); // li   ra,ra,-1
        assert_eq!(decode_q01(0x4481).unwrap(), Addiw(IType(0x00000493))); // li   s1,s1,0
        assert_eq!(decode_q01(0x5689).unwrap(), Addiw(IType(0xFE200693))); // li   a3,a3,-30
        assert_eq!(decode_q01(0x4a95).unwrap(), Addiw(IType(0x00500A93))); // li   s5,s5,5
        assert_eq!(decode_q01(0x4ffd).unwrap(), Addiw(IType(0x01F00F93))); // li   t6,t6,31

        // C.ADDI16SP
        assert_eq!(decode_q01(0x6141).unwrap(), Addi(IType(0x01010113))); // addi    sp,sp,16
        assert_eq!(decode_q01(0x6121).unwrap(), Addi(IType(0x04010113))); // addi    sp,sp,64
        assert_eq!(decode_q01(0x717d).unwrap(), Addi(IType(0xFF010113))); // addi    sp,sp,-16
        assert_eq!(decode_q01(0x617d).unwrap(), Addi(IType(0x1F010113))); // addi    sp,sp,496
        assert_eq!(decode_q01(0x7101).unwrap(), Addi(IType(0xE0010113))); // addi    sp,sp,-512

        assert_eq!(get_11_10_bit(0x0000), 0b00);
        assert_eq!(get_11_10_bit(0xffff), 0b11);
        assert_eq!(get_11_10_bit(0xf0ff), 0b00);
        assert_eq!(get_11_10_bit(0xf000), 0b00);
        assert_eq!(get_11_10_bit(0x0e00), 0b11);
        assert_eq!(get_11_10_bit(0x0800), 0b10);
        assert_eq!(get_11_10_bit(0x0700), 0b01);
        assert_eq!(get_11_10_bit(0xf8ff), 0b10);
        assert_eq!(get_11_10_bit(0xf7ff), 0b01);

        assert_eq!(get_12_and_6_5_bit(0x0000), 0b000);
        assert_eq!(get_12_and_6_5_bit(0xffff), 0b111);
        assert_eq!(get_12_and_6_5_bit(0xff6f), 0b111);
        assert_eq!(get_12_and_6_5_bit(0x1060), 0b111);
        assert_eq!(get_12_and_6_5_bit(0x0060), 0b011);
        assert_eq!(get_12_and_6_5_bit(0x1000), 0b100);
        assert_eq!(get_12_and_6_5_bit(0x1040), 0b110);
        assert_eq!(get_12_and_6_5_bit(0x1020), 0b101);
    }
}

