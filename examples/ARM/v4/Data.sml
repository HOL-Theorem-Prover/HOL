structure Data =
struct
datatype shift = LSL | LSR | ASR | ROR;

datatype condition = EQ | NE | CS | CC | MI | PL | VS | VC
                   | HI | LS | GE | LT | GT | LE | AL | NV;

datatype register = R0 | R1 | R2  | R3  | R4  | R5  | R6  | R7
                  | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15;

datatype opcode = AND | EOR | SUB | RSB | ADD | ADC | SBC | RSC
                | TST | TEQ | CMP | CMN | ORR | MOV | BIC | MVN;

datatype vregister = VReg of string | NReg of register;

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
    Br of {L : bool, offset : int}
  | Swi_ex
  | Data_proc of {opc : opcode, S : bool, Rn : vregister, Rd : vregister,
                  op2 : addr_mode1}
  | Mla_mul of {L : bool, Signed : bool, A : bool, S : bool, Rd : vregister,
                Rn : vregister, Rs : vregister, Rm : vregister}
  | Ldrh_strh of {P : bool, U : bool, W : bool, L : bool, S : bool, H : bool,
                  Rn : vregister, Rd : vregister, offset : addr_mode3}
  | Ldr_str of {P : bool, U : bool, B : bool, W : bool, L : bool,
                Rn : vregister, Rd : vregister, offset : addr_mode2}
  | Ldm_stm of {P : bool, U : bool, S : bool, W : bool, L : bool,
                Rn : vregister, list : int}
  | Swp of {B : bool, Rn : vregister, Rd : vregister, Rm : vregister}
  | Mrs of {R : bool, Rd : vregister}
  | Msr of {R : bool, bit19 : bool, bit16 : bool, Op : msr_mode}
  | Cdp of {Cop1 : int, CRn : vregister, CRd : vregister, CP : int,
            Cop2 :int, CRm : vregister}
  | Mcr_mrc of {Cop1 : int, L : bool, Rd : vregister,
                CRn : vregister, CP : int, CRm : vregister, Cop2 : int}
  | Ldc_stc of {P : bool, U : bool, N : bool, W : bool, L : bool,
                CRd : vregister, Rn : vregister, CP : int, offset : int}
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
  fun smsb b = if b then pow(two,fromInt 31) else zero
  fun mror32 x n =
    if n = 0 then x
             else mror32 ((div2 x) + smsb (mod2 x = one)) (Int.-(n, 1))
  fun ror32 x n = mror32 x (Int.mod(n, 32))
in
  fun two_comp26 n = (n26 - n mod n26) mod n26
  fun two_comp32 n = (n32 - n mod n32) mod n32
  fun align32 n = (n div n4) * n4
  fun add32 a b = (a + b) mod n32
  fun sub32 a b = add32 a (two_comp32 b)
  fun rol32 x n = ror32 x (Int.-(32,Int.mod(n, 32)))
  fun mk_immediate rot imm = ror32 imm (Int.*(2, rot))
end

end
