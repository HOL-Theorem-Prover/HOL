open HolKernel boolLib Parse bossLib;

datatype shift = LSL | LSR | ASR | ROR;

datatype condition = EQ | NE | CS | CC | MI | PL | VS | VC
                   | HI | LS | GE | LT | GT | LE | AL | NV;

datatype register = R0 | R1 | R2  | R3  | R4  | R5  | R6  | R7
                  | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15;

datatype opcode = AND | EOR | SUB | RSB | ADD | ADC | SBC | RSC
                | TST | TEQ | CMP | CMN | ORR | MOV | BIC | MVN;

datatype addr_mode1 =
   DpImmediate of num
 | DpShiftImmediate of {Imm : int, Rm : register, Sh : shift}
 | DpShiftRegister of {Rm : register, Rs : register, Sh : shift};

datatype addr_mode2 =
   DtImmediate of int
 | DtShiftImmediate of {Imm : int, Rm : register, Sh : shift};

datatype msr_mode = MsrImmediate of num | MsrRegister of register;

datatype ARM_instruction =
    Br of {L : bool, offset : int}
  | Swi_ex
  | Data_proc of {opc : opcode, S : bool, Rn : register, Rd : register,
                  op2 : addr_mode1}
  | Mla_mul of {A : bool, S : bool, Rd : register, Rn : register,
                Rs : register, Rm : register}
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
 | Data of num;

exception BadInstruction of string;
