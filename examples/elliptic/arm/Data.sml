datatype shift = LSL | LSR | ASR | ROR;

datatype condition = EQ | NE | CS | CC | MI | PL | VS | VC
                   | HI | LS | GE | LT | GT | LE | AL | NV;

datatype register = R0 | R1 | R2  | R3  | R4  | R5  | R6  | R7
                  | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15;

datatype opcode = AND | EOR | SUB | RSB | ADD | ADC | SBC | RSC
                | TST | TEQ | CMP | CMN | ORR | MOV | BIC | MVN;

datatype addr_mode1 =
   DpImmediate of Arbnum.num
 | DpShiftImmediate of {Imm : int, Rm : register, Sh : shift}
 | DpShiftRegister of {Rm : register, Rs : register, Sh : shift};

datatype addr_mode2 =
   DtImmediate of int
 | DtShiftImmediate of {Imm : int, Rm : register, Sh : shift};

datatype msr_mode = MsrImmediate of Arbnum.num | MsrRegister of register;

datatype ARM_instruction =
    Br of {L : bool, offset : int}
  | Swi_ex
  | Data_proc of {opc : opcode, S : bool, Rn : register, Rd : register,
                  op2 : addr_mode1}
  | Mla_mul of {L : bool, Signed : bool, A : bool, S : bool, Rd : register,
                Rn : register, Rs : register, Rm : register}
  | Ldr_str of {P : bool, U : bool, B : bool, W : bool, L : bool,
                Rn : register, Rd : register, offset : addr_mode2}
  | Ldm_stm of {P : bool, U : bool, S : bool, W : bool, L : bool,
                Rn : register, list : int}
  | Swp of {B : bool, Rn : register, Rd : register, Rm : register}
  | Mrs of {R : bool, Rd : register}
  | Msr of {R : bool, bit19 : bool, bit16 : bool, Op : msr_mode}
  | Cdp of {Cop1 : int, CRn : register, CRd : register, CP : int,
            Cop2 :int, CRm : register}
  | Mcr_mrc of {Cop1 : int, L : bool, Rd : register,
                CRn : register, CP : int, CRm : register, Cop2 : int}
  | Ldc_stc of {P : bool, U : bool, N : bool, W : bool, L : bool,
                CRd : register, Rn : register, CP : int, offset : int}
  | Undef;

datatype instruction =
   Instruction of ARM_instruction * condition
 | Data of Arbnum.num;

datatype assembler =
   Label of string
 | Mark of Arbnum.num
 | BranchS of condition * bool * string
 | BranchN of condition * bool * Arbnum.num
 | Code of instruction

exception BadInstruction of string;
exception Parse of string;

local open Arbnum
  val n4  = fromInt 4
  val n24 = pow(two, fromInt 24)
  val n26 = pow(two, fromInt 26)
  val n32 = pow(two, fromInt 32)
in
  fun two_comp26 n = (n26 - n mod n26) mod n26
  fun two_comp32 n = (n32 - n mod n32) mod n32
  fun align32 n = (n div n4) * n4
  fun add32 a b = (a + b) mod n32
  fun sub32 a b = add32 a (two_comp32 b)
end;
