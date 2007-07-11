structure Data =
struct
datatype shift = LSL | LSR | ASR | ROR;

datatype condition = EQ | NE | CS | CC | MI | PL | VS | VC
                   | HI | LS | GE | LT | GT | LE | AL | NV;

datatype register = R0 | R1 | R2  | R3  | R4  | R5  | R6  | R7
                  | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15;

datatype register_ = R0_ | R1_ | R2_ | R3_ | R4_ | R5_ | R6_ | R7_;

datatype opcode = AND | EOR | SUB | RSB | ADD | ADC | SBC | RSC
                | TST | TEQ | CMP | CMN | ORR | MOV | BIC | MVN;

datatype opcode2 = AND_ | EOR_ | LSL_2 | LSR_2 | ASR_2 | ADC_ | SBC_ | ROR_
                 | TST_ | NEG_ | CMP_2 | CMN_  | ORR_  | MUL_ | BIC_ | MVN_;

datatype opcode3 = STR_2 | STRH_2 | STRB_2 | LDRSB_
                 | LDR_2 | LDRH_2 | LDRB_2 | LDRSH_;

datatype opcode4 = STR_1 | LDR_1 | STRB_1 | LDRB_1 | STRH_1 | LDRH_1;

datatype vregister = VReg of string | NReg of register;
datatype vregister_ = VReg_ of string | NReg_ of register_;

datatype addr_mode1 =
   DpImmediate of Arbnum.num
 | DpShiftImmediate of {Imm : int, Rm : vregister, Sh : shift}
 | DpShiftRegister of {Rm : vregister, Rs : vregister, Sh : shift};

datatype addr_mode2 =
   DtImmediate of int
 | DtShiftImmediate of {Imm : int, Rm : vregister, Sh : shift};

datatype addr_mode3 =
   DthImmediate of int
 | DthRegister of vregister;

datatype msr_mode = MsrImmediate of Arbnum.num | MsrRegister of vregister;

datatype ARM_instruction =
    Br        of {L : bool, offset : int}
  | Bx        of vregister
  | Swi_ex    of int
  | Data_proc of {opc : opcode, S : bool, Rn : vregister, Rd : vregister,
                  op2 : addr_mode1}
  | Mla_mul   of {L : bool, Signed : bool, A : bool, S : bool, Rd : vregister,
                  Rn : vregister, Rs : vregister, Rm : vregister}
  | Ldrh_strh of {P : bool, U : bool, W : bool, L : bool, S : bool, H : bool,
                  Rn : vregister, Rd : vregister, offset : addr_mode3}
  | Ldr_str   of {P : bool, U : bool, B : bool, W : bool, L : bool,
                  Rn : vregister, Rd : vregister, offset : addr_mode2}
  | Ldm_stm   of {P : bool, U : bool, S : bool, W : bool, L : bool,
                  Rn : vregister, list : int}
  | Swp       of {B : bool, Rn : vregister, Rd : vregister, Rm : vregister}
  | Mrs       of {R : bool, Rd : vregister}
  | Msr       of {R : bool, bit19 : bool, bit16 : bool, Op : msr_mode}
  | Cdp       of {Cop1 : int, CRn : vregister, CRd : vregister, CP : int,
                  Cop2 :int, CRm : vregister}
  | Mcr_mrc   of {Cop1 : int, L : bool, Rd : vregister,
                  CRn : vregister, CP : int, CRm : vregister, Cop2 : int}
  | Ldc_stc   of {P : bool, U : bool, N : bool, W : bool, L : bool,
                  CRd : vregister, Rn : vregister, CP : int, offset : int}
  | Undef;

datatype Thumb_instruction =
    LSL_1  of {Rd : vregister_, Rm : vregister_, imm : int}
  | LSR_1  of {Rd : vregister_, Rm : vregister_, imm : int}
  | ASR_1  of {Rd : vregister_, Rm : vregister_, imm : int}
  | ADD_3  of {Rd : vregister_, Rn : vregister_, Rm : vregister_}
  | SUB_3  of {Rd : vregister_, Rn : vregister_, Rm : vregister_}
  | ADD_1  of {Rd : vregister_, Rn : vregister_, imm : int}
  | SUB_1  of {Rd : vregister_, Rn : vregister_, imm : int}
  | MOV_1  of {Rd : vregister_, imm : int}
  | CMP_1  of {Rn : vregister_, imm : int}
  | ADD_2  of {Rd : vregister_, imm : int}
  | SUB_2  of {Rd : vregister_, imm : int}
  | DP_    of {opc : opcode2, Rd : vregister_, Rm : vregister_}
  | ADD_4  of {Rd : vregister, Rm : vregister}
  | CMP_3  of {Rd : vregister, Rm : vregister}
  | MOV_3  of {Rd : vregister, Rm : vregister}
  | BX_    of vregister
  | LDR_3  of {Rd : vregister_, imm : int}
  | DT_    of {opc : opcode3, Rd : vregister_, Rn : vregister_, Rm : vregister_}
  | DT_imm of {opc : opcode4, Rd : vregister_, Rn : vregister_, imm : int}
  | STR_3  of {Rd : vregister_, imm : int}
  | LDR_4  of {Rd : vregister_, imm : int}
  | ADD_5  of {Rd : vregister_, imm : int}
  | ADD_6  of {Rd : vregister_, imm : int}
  | ADD_7  of int
  | SUB_4  of int
  | PUSH   of {R : bool, list : int}
  | POP    of {R : bool, list : int}
  | LDMIA_ of {Rn : vregister_, list : int}
  | STMIA_ of {Rn : vregister_, list : int}
  | B_1    of {cond : condition, imm : int}
  | UND_
  | SWI_   of int
  | B_2    of int
  | BL_    of int
  | BL_a   of int
  | BL_b   of int;

datatype instruction =
   Instruction of ARM_instruction * condition
 | Thumb of Thumb_instruction
 | Data of Arbnum.num
 | ThumbData of Arbnum.num;

datatype assembler =
   Label of string
 | Mark of Arbnum.num
 | BranchS of condition * bool * string
 | BranchN of condition * bool * Arbnum.num
 | ThumbBranchS  of condition * bool * string
 | ThumbBranchN  of condition * bool * Arbnum.num
 | Code of instruction

exception BadInstruction of string;
exception Parse of string;

local open Arbnum
  val n4  = fromInt 4
  val n16 = pow(two, fromInt 16)
  val n24 = pow(two, fromInt 24)
  val n26 = pow(two, fromInt 26)
  val n32 = pow(two, fromInt 32)
  fun smsb b = if b then pow(two,fromInt 31) else zero
  fun mror32 x n =
    if n = 0 then x
             else mror32 ((div2 x) + smsb (mod2 x = one)) (Int.-(n, 1))
  fun ror32 x n = mror32 x (Int.mod(n, 32))
in
  fun two_comp16 n = (n16 - n mod n16) mod n16
  fun two_comp26 n = (n26 - n mod n26) mod n26
  fun two_comp32 n = (n32 - n mod n32) mod n32
  fun even a =  (a mod two) = zero
  val odd = not o even
  fun mul2 a =  a * two
  fun mul4 a =  a * n4
  fun div2 a =  a div two
  fun div4 a =  a div n4
  fun add32 a b = (a + b) mod n32
  fun sub32 a b = add32 a (two_comp32 b)
  fun rol32 x n = ror32 x (Int.-(32,Int.mod(n, 32)))
  val align16 = mul2 o div2
  val align32 = mul4 o div4
  fun mk_immediate rot imm = ror32 imm (Int.*(2, rot))
end

end
