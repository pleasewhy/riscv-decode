use super::consts::*;
use crate::*;

const ADDI_OPCODE: u32 = 0b0010011;
const ADDI_FUNC3: u32 = 0b000;

const ADDIW_OPCODE: u32 = 0b0011011;
const ADDIW_FUNC3: u32 = 0b000;

const LUI_OPCODE: u32 = 0b0110111;

const SRLI_OPCODE: u32 = 0b0010011;
const SRLI_FUNC3: u32 = 0b101;
const SRLI_FUNC6: u32 = 0b000000;

const SRAI_OPCODE: u32 = 0b0010011;
const SRAI_FUNC3: u32 = 0b101;
const SRAI_FUNC6: u32 = 0b010000;

const SLLI_OPCODE: u32 = 0b0010011;
const SLLI_FUNC3: u32 = 0b001;
const SLLI_FUNC6: u32 = 0b000000;

const ANDI_OPCODE: u32 = 0b0010011;
const ANDI_FUNC3: u32 = 0b111;

const SUB_OPCODE: u32 = 0b0110011;
const SUB_FUNC3: u32 = 0b000;
const SUB_FUNC7: u32 = 0b0100000;

const XOR_OPCODE: u32 = 0b0110011;
const XOR_FUNC3: u32 = 0b100;
const XOR_FUNC7: u32 = 0b0000000;

const OR_OPCODE: u32 = 0b0110011;
const OR_FUNC3: u32 = 0b110;
const OR_FUNC7: u32 = 0b0000000;

const AND_OPCODE: u32 = 0b0110011;
const AND_FUNC3: u32 = 0b111;
const AND_FUNC7: u32 = 0b0000000;

const SUBW_OPCODE: u32 = 0b0111011;
const SUBW_FUNC3: u32 = 0b000;
const SUBW_FUNC7: u32 = 0b0100000;

const ADDW_OPCODE: u32 = 0b0111011;
const ADDW_FUNC3: u32 = 0b000;
const ADDW_FUNC7: u32 = 0b0000000;

const JAL_OPCODE: u32 = 0b1101111;

const BEQ_OPCODE: u32 = 0b1100011;
const BEQ_FUNC3: u32 = 0b000;

const BNE_OPCODE: u32 = 0b1100011;
const BNE_FUNC3: u32 = 0b001;

const FLD_OPCODE: u32 = 0b0000111;
const FLD_FUNC3: u32 = 0b011;

const FSD_OPCODE: u32 = 0b0100111;
const FSD_FUNC3: u32 = 0b011;

const LW_OPCODE: u32 = 0b0000011;
const LW_FUNC3: u32 = 0b010;

const SW_OPCODE: u32 = 0b0100011;
const SW_FUNC3: u32 = 0b010;

const LD_OPCODE: u32 = 0b0000011;
const LD_FUNC3: u32 = 0b011;

const SD_OPCODE: u32 = 0b0100011;
const SD_FUNC3: u32 = 0b011;

const JALR_OPCODE: u32 = 0b1100111;
const JALR_FUNC3: u32 = 0b000;

const ADD_OPCODE: u32 = 0b0110011;
const ADD_FUNC3: u32 = 0b000;
const ADD_FUNC7: u32 = 0b0000000;

const EBREAK_OPCODE: u32 = 0b1110011;
const EBREAK_FUNC3: u32 = 0b000;

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
            Ok(Instruction::Addi(IType::new(
                ADDI_OPCODE,
                ADDI_FUNC3,
                rd,
                SP,
                uimm,
            )))
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
        0b000 if i == 1 => Ok(Instruction::Addi(IType::new(
            ADDI_OPCODE,
            ADDI_FUNC3,
            X0,
            X0,
            0,
        ))), // C.NOP(HINT, nzimm̸=0)
        0b000 => {
            let rd = (i & 0b111110000000) >> 7;
            let mut imm = (i & 0b1111100) >> 2; // imm[0:4] = inst[2:6]
            imm |= (i & 0b1000000000000) >> 7; // imm[5] = inst[12]
            imm = (((imm << 26) as i32) >> 26) as u32; // sign extend
            assert!(
                imm != 0,
                "if C.ADDI's nzimm=0, this degrades to HINT instruction"
            );
            Ok(Instruction::Addi(IType::new(
                ADDI_OPCODE,
                ADDI_FUNC3,
                rd,
                rd,
                imm,
            )))
        } // C.ADDI (HINT, nzimm=0) rd, imm -> addi rd, rd, imm
        0b001 => {
            let rd = (i & 0b111110000000) >> 7;
            assert!(rd != 0, "Invalid Instruction: C.ADDIW rd can't be X0");
            let mut imm = (i & 0b1111100) >> 2; // imm[0:4] = inst[2:6]
            imm |= (i & 0b1000000000000) >> 7; // imm[5] = inst[12]
            imm = (((imm << 26) as i32) >> 26) as u32; // sign extend
            Ok(Instruction::Addiw(IType::new(
                ADDIW_OPCODE,
                ADDIW_FUNC3,
                rd,
                rd,
                imm,
            )))
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
            Ok(Instruction::Addiw(IType::new(
                ADDI_OPCODE,
                ADDI_FUNC3,
                rd,
                X0,
                imm,
            )))
        } // C.LI(HINT, rd=0) rd, imm => addi rd, x0, imm
        0b011 if (i & 0b111110000000) >> 7 == 2 => {
            let mut imm = 0u32;
            imm |= (i & 0b1000000) >> 2; // imm[4] = inst[6]
            imm |= (i & 0b100) << 3; // imm[5] = inst[2]
            imm |= (i & 0b100000) << 1; // imm[6] = inst[5]
            imm |= (i & 0b11000) << 4; // imm[8:7] = inst[4:3]
            imm |= (i & 0b1000000000000) >> 3; // imm[9] = inst[12]

            imm = (((imm << 22) as i32) >> 22) as u32; // sign extend
            assert!(imm != 0, "Invalid Instruction: C.ADDI16SP imm can't be 0");
            Ok(Instruction::Addi(IType::new(
                ADDI_OPCODE,
                ADDI_FUNC3,
                SP,
                SP,
                imm,
            )))
        } // C.ADDI16SP (RES, nzimm=0)
        0b011 => {
            let rd = (i & 0b111110000000) >> 7;
            assert!(
                rd != 2,
                "if C.LUI's rd=2, this degrades to HINT instruction"
            );
            let mut imm = (i & 0b1111100) << 10; // imm[16:12] = inst[6:2]
            imm |= (i & 0b1000000000000) << 5; // imm[17] = inst[12]
            imm = (((imm << 14) as i32) >> 14) as u32; // sign extend
            assert!(imm != 0, "Invalid Instruction: C.LUI imm can't be 0");
            Ok(Instruction::Lui(UType::new(LUI_OPCODE, rd, imm)))
        } // C.LUI (RES, nzimm=0; HINT, rd=0)
        0b100 if get_11_10_bit(i) == 0b00 => {
            let rd = ((i & 0b1110000000) >> 7) + 8;
            let mut uimm = (i & 0b1111100) >> 2; // uimm[4:0] = inst[6:2]
            uimm |= (i & 0b1000000000000) >> 7; // uimm[5] = inst[12]
            Ok(Instruction::Srli(ShiftType::new(
                SRLI_OPCODE,
                SRLI_FUNC3,
                SRLI_FUNC6,
                rd,
                rd,
                uimm,
            )))
        } // C.SRLI (RV32 NSE, nzuimm[5]=1)
        0b100 if get_11_10_bit(i) == 0b01 => {
            let rd = ((i & 0b1110000000) >> 7) + 8;
            let mut uimm = (i & 0b1111100) >> 2; // uimm[4:0] = inst[6:2]
            uimm |= (i & 0b1000000000000) >> 7; // uimm[5] = inst[12]
            Ok(Instruction::Srai(ShiftType::new(
                SRAI_OPCODE,
                SRAI_FUNC3,
                SRAI_FUNC6,
                rd,
                rd,
                uimm,
            )))
        } // C.SRAI (RV32 NSE, nzuimm[5]=1)
        0b100 if get_11_10_bit(i) == 0b10 => {
            let rd = ((i & 0b1110000000) >> 7) + 8;
            let mut imm = (i & 0b1111100) >> 2; // uimm[4:0] = inst[6:2]
            imm |= (i & 0b1000000000000) >> 7; // uimm[5] = inst[12]
            imm = (((imm << 26) as i32) >> 26) as u32; // sign extend
            Ok(Instruction::Andi(IType::new(
                ANDI_OPCODE,
                ANDI_FUNC3,
                rd,
                rd,
                imm,
            )))
        } // C.ANDI
        0b100 if get_12_and_6_5_bit(i) == 0b000 => {
            let rd = ((i & 0b1110000000) >> 7) + 8;
            let rs2 = ((i & 0b11100) >> 2) + 8;
            Ok(Instruction::Sub(RType::new(
                SUB_OPCODE, SUB_FUNC3, SUB_FUNC7, rd, rd, rs2,
            )))
        } // C.SUB
        0b100 if get_12_and_6_5_bit(i) == 0b001 => {
            let rd = ((i & 0b1110000000) >> 7) + 8;
            let rs2 = ((i & 0b11100) >> 2) + 8;
            Ok(Instruction::Xor(RType::new(
                XOR_OPCODE, XOR_FUNC3, XOR_FUNC7, rd, rd, rs2,
            )))
        } // C.XOR
        0b100 if get_12_and_6_5_bit(i) == 0b010 => {
            let rd = ((i & 0b1110000000) >> 7) + 8;
            let rs2 = ((i & 0b11100) >> 2) + 8;
            Ok(Instruction::Or(RType::new(
                OR_OPCODE, OR_FUNC3, OR_FUNC7, rd, rd, rs2,
            )))
        } // C.OR
        0b100 if get_12_and_6_5_bit(i) == 0b011 => {
            let rd = ((i & 0b1110000000) >> 7) + 8;
            let rs2 = ((i & 0b11100) >> 2) + 8;
            Ok(Instruction::And(RType::new(
                AND_OPCODE, AND_FUNC3, AND_FUNC7, rd, rd, rs2,
            )))
        } // C.AND
        0b100 if get_12_and_6_5_bit(i) == 0b100 => {
            let rd = ((i & 0b1110000000) >> 7) + 8;
            let rs2 = ((i & 0b11100) >> 2) + 8;
            Ok(Instruction::Subw(RType::new(
                SUBW_OPCODE,
                SUBW_FUNC3,
                SUBW_FUNC7,
                rd,
                rd,
                rs2,
            )))
        } // C.SUBW (RV64/128; RV32 RES)
        0b100 if get_12_and_6_5_bit(i) == 0b101 => {
            let rd = ((i & 0b1110000000) >> 7) + 8;
            let rs2 = ((i & 0b11100) >> 2) + 8;
            Ok(Instruction::Addw(RType::new(
                ADDW_OPCODE,
                ADDW_FUNC3,
                ADDW_FUNC7,
                rd,
                rd,
                rs2,
            )))
        } // C.ADDW (RV64/128; RV32 RES)
        0b100 if get_12_and_6_5_bit(i) == 0b110 => Err(DecodingError::Reserved), // Reserved
        0b100 if get_12_and_6_5_bit(i) == 0b111 => Err(DecodingError::Reserved), // Reserved
        0b101 => {
            let mut imm = 0u32;
            imm |= (i & 0b100) << 3; // imm[5] = inst[2]
            imm |= (i & 0b111000) >> 2; // imm[3:1] = inst[5:3]
            imm |= (i & 0b1000000) << 1; // imm[7] = inst[6]
            imm |= (i & 0b10000000) >> 1; // imm[6] = inst[7]
            imm |= (i & 0b100000000) << 2; // imm[10] = inst[8]
            imm |= (i & 0b11000000000) >> 1; // imm[9:8] = inst[10:9]
            imm |= (i & 0b100000000000) >> 7; // imm[4] = inst[11]
            imm |= (i & 0b1000000000000) >> 1; // imm[11] = inst[12]
            imm = (((imm << 20) as i32) >> 20) as u32; // sign extend
            Ok(Instruction::Jal(JType::new(JAL_OPCODE, X0, imm)))
        } // C.J
        0b110 => {
            let rs1 = ((i & 0b1110000000) >> 7) + 8;
            let mut imm = 0u32;
            imm |= (i & 0b100) << 3; // imm[5] = inst[2]
            imm |= (i & 0b11000) >> 2; // imm[2:1] = inst[4:3]
            imm |= (i & 0b1100000) << 1; // imm[7:6] = inst[6:5]
            imm |= (i & 0b110000000000) >> 7; // imm[4:3] = inst[11:10]
            imm |= (i & 0b1000000000000) >> 4; // imm[8] = inst[12]
            imm = (((imm << 23) as i32) >> 23) as u32; // sign extend
            Ok(Instruction::Beq(BType::new(
                BEQ_OPCODE, BEQ_FUNC3, rs1, X0, imm,
            )))
        } // C.BEQZ
        0b111 => {
            let rs1 = ((i & 0b1110000000) >> 7) + 8;
            let mut imm = 0u32;
            imm |= (i & 0b100) << 3; // imm[5] = inst[2]
            imm |= (i & 0b11000) >> 2; // imm[2:1] = inst[4:3]
            imm |= (i & 0b1100000) << 1; // imm[7:6] = inst[6:5]
            imm |= (i & 0b110000000000) >> 7; // imm[4:3] = inst[11:10]
            imm |= (i & 0b1000000000000) >> 4; // imm[8] = inst[12]
            imm = (((imm << 23) as i32) >> 23) as u32; // sign extend
            Ok(Instruction::Bne(BType::new(
                BNE_OPCODE, BNE_FUNC3, rs1, X0, imm,
            )))
        } // C.BNEZ
        _ => Err(DecodingError::Unknown),
    }
}

fn get_6_2_bit(i: u32) -> u32 {
    (i & 0b1111100) >> 2
}

fn get_12_bit(i: u32) -> u32 {
    (i & 0b1000000000000) >> 12
}

fn get_11_7_bit(i: u32) -> u32 {
    (i & 0b111110000000) >> 7
}

pub fn decode_q10(i: u32) -> DecodingResult {
    match i >> 13 {
        0b000 => {
            let rd = (i & 0b111110000000) >> 7;
            let mut nzuimm = (i & 0b1111100) >> 2; // nzuimm[4:0] = inst[6:2]
            nzuimm |= (i & 0b1000000000000) >> 7; // nzuimm[5] = inst[12]
            assert!(
                nzuimm != 0,
                "if C.SLLI's nzuimm=0, this degrades to HINT instruction"
            );
            Ok(Instruction::Slli(ShiftType::new(
                SLLI_OPCODE,
                SLLI_FUNC3,
                SLLI_FUNC6,
                rd,
                rd,
                nzuimm,
            )))
        } // C.SLLI (HINT, rd=0; RV32 NSE, nzuimm[5]=1)
        0b001 => Err(DecodingError::Unimplemented), // C.FLDSP (RV32/64)
        0b010 => {
            let rd = (i & 0b111110000000) >> 7;
            let mut uimm = (i & 0b1100) << 4; // uimm[7:6] = inst[3:2]
            uimm |= (i & 0b1110000) >> 2; // uimm[4:2] = inst[6:4]
            uimm |= (i & 0b1000000000000) >> 7; // uimm[5] = inst[12]
            assert!(rd != 0, "Invalid Instruction: C.LWSP's rd can't be X0");
            Ok(Instruction::Lw(IType::new(
                LW_OPCODE, LW_FUNC3, rd, SP, uimm,
            )))
        } // C.LWSP (RES, rd=0)
        0b011 => {
            let rd = (i & 0b111110000000) >> 7;
            let mut uimm = (i & 0b11100) << 4; // uimm[8:6] = inst[4:2]
            uimm |= (i & 0b1100000) >> 2; // uimm[4:3] = inst[6:5]
            uimm |= (i & 0b1000000000000) >> 7; // uimm[5] = inst[12]
            assert!(rd != 0, "Invalid Instruction: C.LDSP's rd can't be X0");
            Ok(Instruction::Ld(IType::new(
                LD_OPCODE, LD_FUNC3, rd, SP, uimm,
            )))
        } // C.LDSP (RV64/128; RES, rd=0)
        0b100 if get_12_bit(i) == 0 && get_11_7_bit(i) != 0 && get_6_2_bit(i) == 0 => {
            let rs1 = (i & 0b111110000000) >> 7;
            assert!(rs1 != 0, "Invalid Instruction: C.JR's rs1 can't be x0");
            Ok(Instruction::Jalr(IType::new(
                JALR_OPCODE,
                JALR_FUNC3,
                X0,
                rs1,
                0,
            )))
        } // C.JR (RES, rs1=0)
        0b100 if get_12_bit(i) == 0 && get_11_7_bit(i) != 0 && get_6_2_bit(i) != 0 => {
            let rd = (i & 0b111110000000) >> 7;
            let rs2 = (i & 0b1111100) >> 2;
            assert!(
                rd != 0,
                "if C.MV's rd=X0, this degrades to HINT instruction"
            );
            Ok(Instruction::Add(RType::new(
                ADD_OPCODE, ADD_FUNC3, ADD_FUNC7, rd, X0, rs2,
            )))
        } // C.MV (HINT, rd=0)
        0b100 if get_12_bit(i) == 1 && get_11_7_bit(i) == 0 && get_6_2_bit(i) == 0 => {
            Ok(Instruction::Ebreak)
        } // C.EBREAK
        0b100 if get_12_bit(i) == 1 && get_11_7_bit(i) != 0 && get_6_2_bit(i) == 0 => {
            let rs1 = get_11_7_bit(i);
            Ok(Instruction::Jalr(IType::new(
                JALR_OPCODE,
                JALR_FUNC3,
                RA,
                rs1,
                0,
            )))
        } // C.JALR
        0b100 if get_12_bit(i) == 1 && get_11_7_bit(i) != 0 && get_6_2_bit(i) != 0 => {
            let rd = get_11_7_bit(i);
            let rs2 = get_6_2_bit(i);
            Ok(Instruction::Add(RType::new(
                ADD_OPCODE, ADD_FUNC3, ADD_FUNC7, rd, rd, rs2,
            )))
        } // C.ADD (HINT, rd=0)
        0b101 => Err(DecodingError::Unimplemented), // C.FSDSP (RV32/64)
        0b110 => {
            let rs2 = (i & 0b1111100) >> 2;
            let mut uimm = (i & 0b110000000) >> 1; // uimm[7:6] = inst[8:7]
            uimm |= (i & 0b1111000000000) >> 7; // uimm[5:2] = inst[12:9]
            Ok(Instruction::Sw(SType::new(
                SW_OPCODE, SW_FUNC3, SP, rs2, uimm,
            )))
        } // C.SWSP
        0b111 => {
            let rs2 = (i & 0b1111100) >> 2;
            let mut uimm = (i & 0b1110000000) >> 1; // uimm[8:6] = inst[9:7]
            uimm |= (i & 0b1111000000000) >> 7; // uimm[5:3] = inst[12:10]
            Ok(Instruction::Sd(SType::new(
                SD_OPCODE, SD_FUNC3, SP, rs2, uimm,
            )))
        } // C.SDSP (RV64/128)
        _ => Err(DecodingError::Unknown),
    }
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

        // C.LUI
        assert_eq!(decode_q01(0x6085).unwrap(), Lui(UType(0x000010B7))); // lui     ra,0x1
        assert_eq!(decode_q01(0x7405).unwrap(), Lui(UType(0xFFFE1437))); // lui     s0,0xfffe1
        assert_eq!(decode_q01(0x7ffd).unwrap(), Lui(UType(0xFFFFFFB7))); // lui     t6,0xfffff
        assert_eq!(decode_q01(0x62fd).unwrap(), Lui(UType(0x0001F2B7))); // lui     t0,0x1f
        assert_eq!(decode_q01(0x7a81).unwrap(), Lui(UType(0xFFFE0AB7))); // lui     s5,0xfffe0

        // C.SRLI
        assert_eq!(decode_q01(0x807d).unwrap(), Srli(ShiftType(0x01F45413))); // srli    s0,s0,0x1f
        assert_eq!(decode_q01(0x83fd).unwrap(), Srli(ShiftType(0x01F7D793))); // srli    a5,a5,0x1f
        assert_eq!(decode_q01(0x8385).unwrap(), Srli(ShiftType(0x0017D793))); // srli    a5,a5,0x1

        // C.SRAI
        assert_eq!(decode_q01(0x847d).unwrap(), Srai(ShiftType(0x41F45413))); // srai    s0,s0,0x1f
        assert_eq!(decode_q01(0x87fd).unwrap(), Srai(ShiftType(0x41F7D793))); // srai    a5,a5,0x1f
        assert_eq!(decode_q01(0x8785).unwrap(), Srai(ShiftType(0x4017D793))); // srai    a5,a5,0x1

        // C.ANDI
        assert_eq!(decode_q01(0x983d).unwrap(), Andi(IType(0xFEF47413))); // c.andi s0, ~0x10
        assert_eq!(decode_q01(0x987d).unwrap(), Andi(IType(0xFFF47413))); // c.andi x8, ~0x0
        assert_eq!(decode_q01(0x8881).unwrap(), Andi(IType(0x0004F493))); // c.andi x9, 0x0
        assert_eq!(decode_q01(0x9b81).unwrap(), Andi(IType(0xFE07F793))); // c.andi x15, -32
        assert_eq!(decode_q01(0x8bfd).unwrap(), Andi(IType(0x01F7F793))); // c.andi x15, 31

        // C.SUB
        assert_eq!(decode_q01(0x8c05).unwrap(), Sub(RType(0x40940433))); // c.sub x8, x9
        assert_eq!(decode_q01(0x8c1d).unwrap(), Sub(RType(0x40F40433))); // c.sub x8, x15
        assert_eq!(decode_q01(0x8c95).unwrap(), Sub(RType(0x40D484B3))); // c.sub x9, x13
        assert_eq!(decode_q01(0x8d95).unwrap(), Sub(RType(0x40D585B3))); // c.sub x11, x13
        assert_eq!(decode_q01(0x8e15).unwrap(), Sub(RType(0x40D60633))); // c.sub x12, x13

        // C.XOR
        assert_eq!(decode_q01(0x8c25).unwrap(), Xor(RType(0x00944433))); // c.xor x8, x9
        assert_eq!(decode_q01(0x8c3d).unwrap(), Xor(RType(0x00F44433))); // c.xor x8, x15
        assert_eq!(decode_q01(0x8cb5).unwrap(), Xor(RType(0x00D4C4B3))); // c.xor x9, x13
        assert_eq!(decode_q01(0x8db5).unwrap(), Xor(RType(0x00D5C5B3))); // c.xor x11, x13
        assert_eq!(decode_q01(0x8e35).unwrap(), Xor(RType(0x00D64633))); // c.xor x12, x13

        // C.OR
        assert_eq!(decode_q01(0x8c45).unwrap(), Or(RType(0x00946433))); // c.or x8, x9
        assert_eq!(decode_q01(0x8c5d).unwrap(), Or(RType(0x00F46433))); // c.or x8, x15
        assert_eq!(decode_q01(0x8cd5).unwrap(), Or(RType(0x00D4E4B3))); // c.or x9, x13
        assert_eq!(decode_q01(0x8dd5).unwrap(), Or(RType(0x00D5E5B3))); // c.or x11, x13
        assert_eq!(decode_q01(0x8e55).unwrap(), Or(RType(0x00D66633))); // c.or x12, x13

        // C.AND
        assert_eq!(decode_q01(0x8c65).unwrap(), And(RType(0x00947433))); // c.and x8, x9
        assert_eq!(decode_q01(0x8c7d).unwrap(), And(RType(0x00F47433))); // c.and x8, x15
        assert_eq!(decode_q01(0x8cf5).unwrap(), And(RType(0x00D4F4B3))); // c.and x9, x13
        assert_eq!(decode_q01(0x8df5).unwrap(), And(RType(0x00D5F5B3))); // c.and x11, x13
        assert_eq!(decode_q01(0x8e75).unwrap(), And(RType(0x00D67633))); // c.and x12, x13

        // C.SUBW
        assert_eq!(decode_q01(0x9c05).unwrap(), Subw(RType(0x4094043B))); // c.subw x8, x9
        assert_eq!(decode_q01(0x9c1d).unwrap(), Subw(RType(0x40F4043B))); // c.subw x8, x15
        assert_eq!(decode_q01(0x9c95).unwrap(), Subw(RType(0x40D484BB))); // c.subw x9, x13
        assert_eq!(decode_q01(0x9d95).unwrap(), Subw(RType(0x40D585BB))); // c.subw x11, x13
        assert_eq!(decode_q01(0x9e15).unwrap(), Subw(RType(0x40D6063B))); // c.subw x12, x13

        // C.ADDW
        assert_eq!(decode_q01(0x9ca9).unwrap(), Addw(RType(0x00A484BB))); // c.addw s1, a0
        assert_eq!(decode_q01(0x9c3d).unwrap(), Addw(RType(0x00F4043B))); // c.addw x8, x15
        assert_eq!(decode_q01(0x9cb5).unwrap(), Addw(RType(0x00D484BB))); // c.addw x9, x13
        assert_eq!(decode_q01(0x9db5).unwrap(), Addw(RType(0x00D585BB))); // c.addw x11, x13
        assert_eq!(decode_q01(0x9e35).unwrap(), Addw(RType(0x00D6063B))); // c.addw x12, x13

        // C.J
        assert_eq!(decode_q01(0xbfc5).unwrap(), Jal(JType(0xFF1FF06F))); // jal x0, -16
        assert_eq!(decode_q01(0xbfdd).unwrap(), Jal(JType(0xFF7FF06F))); // jal x0, -10
        assert_eq!(decode_q01(0xa011).unwrap(), Jal(JType(0x0040006F))); // jal x0, 4
        assert_eq!(decode_q01(0xa029).unwrap(), Jal(JType(0x00A0006F))); // jal x0, 10

        // C.BEQZ
        assert_eq!(decode_q01(0xc401).unwrap(), Beq(BType(0x00040463))); // beq s0, x0, 0x8
        assert_eq!(decode_q01(0xc019).unwrap(), Beq(BType(0x00040363))); // beq s0, x0, 0x6
        assert_eq!(decode_q01(0xc011).unwrap(), Beq(BType(0x00040263))); // beq s0, x0, 0x4
        assert_eq!(decode_q01(0xc389).unwrap(), Beq(BType(0x00078163))); // beq a5, x0, 0x2

        // C.BNEZ
        assert_eq!(decode_q01(0xfc65).unwrap(), Bne(BType(0xFE041CE3))); // bne s0, x0, -8
        assert_eq!(decode_q01(0xf87d).unwrap(), Bne(BType(0xFE041BE3))); // bne s0, x0, -10
        assert_eq!(decode_q01(0xf875).unwrap(), Bne(BType(0xFE041AE3))); // bne s0, x0, -12
        assert_eq!(decode_q01(0xfbed).unwrap(), Bne(BType(0xFE0799E3))); // bne a5, x0, -14

        // C.SLLI
        assert_eq!(decode_q10(0x02fe).unwrap(), Slli(ShiftType(0x01F29293))); // slli    t0,t0,0x1f
        assert_eq!(decode_q10(0x0f9e).unwrap(), Slli(ShiftType(0x007F9F93))); // slli    t6,t6,0x7
        assert_eq!(decode_q10(0x00d6).unwrap(), Slli(ShiftType(0x01509093))); // slli    ra,ra,0x15
        assert_eq!(decode_q10(0x02fe).unwrap(), Slli(ShiftType(0x01F29293))); // slli    t0,t0,0x1f
        assert_eq!(decode_q10(0x0fd6).unwrap(), Slli(ShiftType(0x015F9F93))); // slli    t6,t6,0x15

        // C.LWSP
        assert_eq!(decode_q10(0x5ffe).unwrap(), Lw(IType(0x0FC12F83))); // lw      t6,252(sp)
        assert_eq!(decode_q10(0x40be).unwrap(), Lw(IType(0x0CC12083))); // lw      ra,204(sp)
        assert_eq!(decode_q10(0x4782).unwrap(), Lw(IType(0x00012783))); // lw      a5,0(sp)
        assert_eq!(decode_q10(0x4a92).unwrap(), Lw(IType(0x00412A83))); // lw      s5,4(sp)
        assert_eq!(decode_q10(0x53ee).unwrap(), Lw(IType(0x0F812383))); // lw      t2,248(sp)

        // C.LDSP
        assert_eq!(decode_q10(0x7fce).unwrap(), Ld(IType(0x0F013F83))); // ld      t6,240(sp)
        assert_eq!(decode_q10(0x60ae).unwrap(), Ld(IType(0x0C813083))); // ld      ra,200(sp)
        assert_eq!(decode_q10(0x6782).unwrap(), Ld(IType(0x00013783))); // ld      a5,0(sp)
        assert_eq!(decode_q10(0x6aa2).unwrap(), Ld(IType(0x00813A83))); // ld      s5,8(sp)
        assert_eq!(decode_q10(0x63aa).unwrap(), Ld(IType(0x08813383))); // ld      t2,136(sp)

        // C.JR
        assert_eq!(decode_q10(0x8f82).unwrap(), Jalr(IType(0x000F8067))); // jr    t6
        assert_eq!(decode_q10(0x8102).unwrap(), Jalr(IType(0x00010067))); // jr    sp
        assert_eq!(decode_q10(0x8782).unwrap(), Jalr(IType(0x00078067))); // jr    a5

        // C.MV
        assert_eq!(decode_q10(0x80fe).unwrap(), Add(RType(0x01F000B3))); // add      ra,x0,t6
        assert_eq!(decode_q10(0x8ffe).unwrap(), Add(RType(0x01F00FB3))); // add      t6,x0,t6
        assert_eq!(decode_q10(0x8f86).unwrap(), Add(RType(0x00100FB3))); // add      t6,x0,ra
        assert_eq!(decode_q10(0x87e6).unwrap(), Add(RType(0x019007B3))); // add      a5,x0,s9
        assert_eq!(decode_q10(0x83d6).unwrap(), Add(RType(0x015003B3))); // add      t2,x0,s5

        // C.JALR
        assert_eq!(decode_q10(0x9082).unwrap(), Jalr(IType(0x000080E7))); // jalr    t6
        assert_eq!(decode_q10(0x9f82).unwrap(), Jalr(IType(0x000F80E7))); // jalr    sp
        assert_eq!(decode_q10(0x9782).unwrap(), Jalr(IType(0x000780E7))); // jalr    a5

        // C.ADD
        assert_eq!(decode_q10(0x9f86).unwrap(), Add(RType(0x001F8FB3))); // add      t6,t6,ra
        assert_eq!(decode_q10(0x90fe).unwrap(), Add(RType(0x01F080B3))); // add      ra,ra,t6
        assert_eq!(decode_q10(0x9ffe).unwrap(), Add(RType(0x01FF8FB3))); // add      t6,t6,t6

        // C.SWSP
        assert_eq!(decode_q10(0xdffe).unwrap(), Sw(SType(0x0FF12E23))); // sw      t6,252(sp)
        assert_eq!(decode_q10(0xc786).unwrap(), Sw(SType(0x0C112623))); // sw      ra,204(sp)
        assert_eq!(decode_q10(0xc03e).unwrap(), Sw(SType(0x00F12023))); // sw      a5,0(sp)
        assert_eq!(decode_q10(0xc256).unwrap(), Sw(SType(0x01512223))); // sw      s5,4(sp)
        assert_eq!(decode_q10(0xdd9e).unwrap(), Sw(SType(0x0E712C23))); // sw      t2,248(sp)

        // C.SDSP (RV64/128)
        assert_eq!(decode_q10(0xf9fe).unwrap(), Sd(SType(0x0FF13823))); // sd      t6,240(sp)
        assert_eq!(decode_q10(0xe586).unwrap(), Sd(SType(0x0C113423))); // sd      ra,200(sp)
        assert_eq!(decode_q10(0xe03e).unwrap(), Sd(SType(0x00F13023))); // sd      a5,0(sp)
        assert_eq!(decode_q10(0xe456).unwrap(), Sd(SType(0x01513423))); // sd      s5,8(sp)
        assert_eq!(decode_q10(0xe51e).unwrap(), Sd(SType(0x08713423))); // sd      t2,136(sp)

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
