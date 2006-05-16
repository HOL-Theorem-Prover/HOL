(* ========================================================================= *)
(* FILE          : instructionSyntax.sml                                     *)
(* DESCRIPTION   : Support for working with ARM instructions                 *)
(*                                                                           *)
(* AUTHORS       : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2006                                                      *)
(* ========================================================================= *)

(* interactive use:
  app load ["Nonstdio","wordsSyntax", "instructionTheory",
            "Lexer", "Parser", "Data"];
*)

open HolKernel boolLib Parse bossLib;
open Q wordsSyntax instructionTheory Data;

(* ------------------------------------------------------------------------- *)

local
  fun rnum2list l n =
    if l = 0 then
      []
     else if n = Arbnum.zero then
       List.tabulate(l,fn x => false)
     else
       (rnum2list (l - 1) (Arbnum.div2 n)) @ [Arbnum.mod2 n = Arbnum.one]
in
  fun num2list l n = rev (rnum2list l n)
end;

local
  fun llist2num [] n = n
    | llist2num (x::xs) n =
        llist2num xs ((if x then Arbnum.plus1 else I) (Arbnum.times2 n))
in
  fun list2num l = llist2num (rev l) Arbnum.zero
end;

val list2int = Arbnum.toInt o list2num;

fun bits h l (n:bool list) = List.take(List.drop(n,l),h + 1 - l);
fun bit b n = (bits b b n = [true]);

(* ------------------------------------------------------------------------- *)

fun register2int r =
  case r of
    R0  => 0  | R1  => 1  | R2  => 2  | R3  => 3
  | R4  => 4  | R5  => 5  | R6  => 6  | R7  => 7
  | R8  => 8  | R9  => 9  | R10 => 10 | R11 => 11
  | R12 => 12 | R13 => 13 | R14 => 14 | R15 => 15;

fun reg2string r =
let val n = register2int r in
  case n of
    13 => "sp"
  | 14 => "lr"
  | 15 => "pc"
  | _  => "r" ^ int_to_string n
end;

fun cp_reg2string r = "c" ^ int_to_string (register2int r);
fun cp_num2string n = "p" ^ int_to_string n;

fun opcode2string opc =
  case opc of
    AND => "and" | EOR => "eor" | SUB => "sub" | RSB => "rsb"
  | ADD => "add" | ADC => "adc" | SBC => "sbc" | RSC => "rsc"
  | TST => "tst" | TEQ => "teq" | CMP => "cmp" | CMN => "cmn"
  | ORR => "orr" | MOV => "mov" | BIC => "bic" | MVN => "mvn";

fun condition2string cond =
  case cond of
    EQ => "eq" | NE => "ne" | CS => "cs" | CC => "cc"
  | MI => "mi" | PL => "pl" | VS => "vs" | VC => "vc"
  | HI => "hi" | LS => "ls" | GE => "ge" | LT => "lt"
  | GT => "gt" | LE => "le" | AL => ""   | NV => "nv";

val list2register = Lexer.int2register o list2int;

fun list2opcode l =
  case list2int l of
    0  => AND | 1  => EOR | 2  => SUB | 3  => RSB
  | 4  => ADD | 5  => ADC | 6  => SBC | 7  => RSC
  | 8  => TST | 9  => TEQ | 10 => CMP | 11 => CMN
  | 12 => ORR | 13 => MOV | 14 => BIC | 15 => MVN
  | _ =>  raise ERR "list2opcode" "not an opcode list";

fun list2condition l =
  case list2int l of
    0  => EQ | 1  => NE | 2  => CS | 3  => CC
  | 4  => MI | 5  => PL | 6  => VS | 7  => VC
  | 8  => HI | 9  => LS | 10 => GE | 11 => LT
  | 12 => GT | 13 => LE | 14 => AL | 15 => NV
  | _ =>  raise ERR "list2condition" "not a condition code list";

fun list2shift l =
  case list2int l of
    0 => LSL | 1 => LSR | 2 => ASR | 3 => ROR
  | _ => raise ERR "list2shift" "not a shift list";

(* ------------------------------------------------------------------------- *)

val Rn = list2register o bits 19 16;
val Rd = list2register o bits 15 12;
val Rs = list2register o bits 11 8;
val Rm = list2register o bits 3 0;

local
  open Arbnum
  fun smsb b = if b then pow(two,fromInt 31) else zero
  fun mror32 x n =
    if n = 0 then x
             else mror32 ((div2 x) + smsb (mod2 x = one)) (Int.-(n, 1))
  fun ror32 x n = mror32 x (Int.mod(n, 32))
in
  fun rol32 x n = ror32 x (Int.-(32,Int.mod(n, 32)))
  fun mk_immediate rot imm = ror32 imm (Int.*(2, rot))
  fun dec_immediate l =
        mk_immediate (list2int (bits 11 8 l)) (list2num (bits 7 0 l))
end;

fun dec_shift_immediate l =
let val imm = list2int (bits 11 7 l) in
  {Rm = Rm l, Imm = imm, Sh = list2shift (bits 6 5 l)}
end;

(* ------------------------------------------------------------------------- *)

fun dec_br l =
  Br {L = bit 24 l, offset = Arbnum.toInt (list2num (bits 23 0 l))};

local
  fun dec_shift_register l =
    {Rm = Rm l, Rs = Rs l, Sh = list2shift (bits 6 5 l)}

  fun dec_addr_mode1 l =
    if bit 25 l then
      DpImmediate (dec_immediate l)
    else if bit 4 l then
      DpShiftRegister (dec_shift_register l)
    else
      DpShiftImmediate (dec_shift_immediate l)
in
  fun dec_data_proc l = Data_proc
    {opc = list2opcode (bits 24 21 l), S = bit 20 l,
     Rn = Rn l, Rd = Rd l, op2 = dec_addr_mode1 l}
end;

fun dec_mla_mul l = Mla_mul
  {L = bit 23 l, Signed = bit 22 l, A = bit 21 l, S = bit 20 l,
   Rd = Rn l, Rn = Rd l, Rs = Rs l, Rm = Rm l};

local
  fun dec_addr_mode2 l =
    if bit 25 l then
      DtShiftImmediate (dec_shift_immediate l)
    else
      DtImmediate (list2int (bits 11 0 l))
in
  fun dec_ldr_str l = Ldr_str
    {P = bit 24 l, U = bit 23 l, B = bit 22 l, W = bit 21 l, L = bit 20 l,
     Rn = Rn l, Rd = Rd l, offset = dec_addr_mode2 l}
end;

fun dec_ldm_stm l = Ldm_stm
  {P = bit 24 l, U = bit 23 l, S = bit 22 l, W = bit 21 l, L = bit 20 l,
   Rn = Rn l, list = list2int (bits 15 0 l)};

fun dec_swp l = Swp {B = bit 22 l, Rn = Rn l, Rd = Rd l, Rm = Rm l};

fun dec_mrs l = Mrs {R = bit 22 l, Rd = Rd l};

local
  fun dec_msr_mode l =
    if bit 25 l then
      MsrImmediate (dec_immediate l)
    else
      MsrRegister (Rm l)
in
  fun dec_msr l = Msr
    {R = bit 22 l, bit19 = bit 19 l, bit16 = bit 16 l, Op = dec_msr_mode l}
end;

fun dec_cdp l = Cdp
  {Cop1 = list2int (bits 23 20 l), CRn = Rn l, CRd = Rd l,
   CP = register2int (Rs l), Cop2 = list2int (bits 7 5 l), CRm = Rm l};

fun dec_mcr_mrc l = Mcr_mrc
  {Cop1 = list2int (bits 23 21 l), L = bit 20 l, Rd = Rd l, CRn = Rn l,
   CP = register2int (Rs l), CRm = Rm l, Cop2 = list2int (bits 7 5 l)};

fun dec_ldc_stc l = Ldc_stc
  {P = bit 24 l, U = bit 23 l, N = bit 22 l, W = bit 21 l, L = bit 20 l,
   CRd = Rd l, Rn = Rn l, CP = register2int (Rs l),
   offset = list2int (bits 7 0 l)};

(* ------------------------------------------------------------------------- *)

fun decode_inst l =
  case rev (map (fn x => if x then 1 else 0) l) of
    [0,0,1,1,0,_,1,0,_,_,_,_,1,1,1,1,_,_,_,_,_,_,_,_,_,_,_,_] => dec_msr l
  | [0,0,0,1,0,_,1,0,_,_,_,_,1,1,1,1,0,0,0,0,0,0,0,0,_,_,_,_] => dec_msr l
  | [0,0,0,1,0,_,0,0,1,1,1,1,_,_,_,_,_,0,0,0,0,0,0,0,0,0,0,0] => dec_mrs l
  | [0,0,0,0,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,1,0,0,1,_,_,_,_] => dec_mla_mul l
  | [0,0,0,1,0,_,0,0,_,_,_,_,_,_,_,_,0,0,0,0,1,0,0,1,_,_,_,_] => dec_swp l
  | [0,1,0,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] => dec_ldr_str l
  | [0,1,1,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,0,_,_,_,_] => dec_ldr_str l
  | [1,0,0,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] => dec_ldm_stm l
  | [1,0,1,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] => dec_br l
  | [1,1,0,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] => dec_ldc_stc l
  | [1,1,1,0,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,0,_,_,_,_] => dec_cdp l
  | [1,1,1,0,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,1,_,_,_,_] => dec_mcr_mrc l
  | [1,1,1,1,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] => Swi_ex
  | [0,0,1,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] => dec_data_proc l
  | [0,0,0,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,0,_,_,_,_] => dec_data_proc l
  | [0,0,0,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,0,_,_,1,_,_,_,_] => dec_data_proc l
  | _ => Undef;

fun num_to_arm n =
let val l = num2list 32 n
    val li = List.take(l,28)
    val lc = List.drop(l,28)
    val i = decode_inst li
in
  case i of
    Undef =>
      if list2num li = Arbnum.fromHexString "6000010" then
        Instruction (i, list2condition lc)
      else
        Data n
  | _ => Instruction (i, list2condition lc)
end;

(* ------------------------------------------------------------------------- *)

fun mk_bool b = if b then T else F;

fun mk_word t n = mk_n2w(numLib.mk_numeral n, t);

val mk_word3 = mk_word ``:i3``;
val mk_word4 = mk_word ``:i4``;
val mk_word5 = mk_word ``:i5``;
val mk_word8 = mk_word ``:i8``;
val mk_word12 = mk_word ``:i12``;
val mk_word16 = mk_word ``:i16``;
val mk_word24 = mk_word ``:i24``;
val mk_word32 = mk_word ``:i32``;

val mk_register = mk_word4 o Arbnum.fromInt o register2int;

fun mk_condition cond =
  case cond of
    EQ => ``EQ`` | NE => ``NE`` | CS => ``CS`` | CC => ``CC``
  | MI => ``MI`` | PL => ``PL`` | VS => ``VS`` | VC => ``VC``
  | HI => ``HI`` | LS => ``LS`` | GE => ``GE`` | LT => ``LT``
  | GT => ``GT`` | LE => ``LE`` | AL => ``AL`` | NV => ``NV``;

fun mk_opcode opc =
  case opc of
    AND => ``instruction$AND`` | EOR => ``instruction$EOR``
  | SUB => ``instruction$SUB`` | RSB => ``instruction$RSB``
  | ADD => ``instruction$ADD`` | ADC => ``instruction$ADC``
  | SBC => ``instruction$SBC`` | RSC => ``instruction$RSC``
  | TST => ``instruction$TST`` | TEQ => ``instruction$TEQ``
  | CMP => ``instruction$CMP`` | CMN => ``instruction$CMN``
  | ORR => ``instruction$ORR`` | MOV => ``instruction$MOV``
  | BIC => ``instruction$BIC`` | MVN => ``instruction$MVN``;

fun mk_br (Instruction (x,c)) =
 (case x of
    Br y =>
      subst [``c:condition``   |-> mk_condition c,
             ``offset:word24`` |-> mk_word24 (Arbnum.fromInt (#offset y))]
        (if #L y then ``instruction$BL c offset``
                 else ``instruction$B c offset``)
  | _ => raise ERR "mk_br" "not a branch instruction")
 | mk_br _ = raise ERR "mk_br" "not a branch instruction";

fun mk_swi_ex c = subst [``c:condition`` |-> mk_condition c] ``SWI c``;

local
  fun num2imm(x,n) =
  let val x8 = Arbnum.mod(x,Arbnum.fromInt 256) in
    if x8 = x then
      (Arbnum.fromInt n, x8)
    else
      if n < 15 then
        num2imm(rol32 x 2, n + 1)
      else
        raise ERR "num2immediate" "number cannot be represented as an immediate"
  end
in
  fun num2immediate n = num2imm(n, 0)
end;

fun mk_shift r s =
  subst [``r:word4`` |-> mk_register r]
  (case s of
     LSL => ``instruction$LSL r``
   | LSR => ``instruction$LSR r``
   | ASR => ``instruction$ASR r``
   | ROR => ``instruction$ROR r``);

local
  fun mk_dp_immediate x =
  let val (n,m) = num2immediate x in
    subst [``n:word4`` |-> mk_word4 n,
           ``m:word8`` |-> mk_word8 m] ``Dp_immediate n m``
  end

  fun mk_addr_mode1 x =
    case x of
      DpImmediate n => mk_dp_immediate n
    | DpShiftImmediate i =>
         subst [``sh:shift``  |-> mk_shift (#Rm i) (#Sh i),
                ``imm:word5`` |-> mk_word5 (Arbnum.fromInt (#Imm i))]
           ``Dp_shift_immediate sh imm``
    | DpShiftRegister r =>
         subst [``sh:shift`` |-> mk_shift (#Rm r) (#Sh r),
                ``rs:word4`` |-> mk_register (#Rs r)]
           ``Dp_shift_register sh rs``
  val err = ERR "mk_data_proc" "not a data processing instruction"
in
  fun mk_data_proc (Instruction (x,c)) =
   (case x of
      Data_proc y => let val opc = #opc y in
        if mem opc [TST,TEQ,CMP,CMN] then
          subst [``f:condition -> word4 -> addr_mode1 -> arm_instruction`` |->
                 mk_opcode opc, ``c:condition`` |-> mk_condition c,
                 ``rn:word4`` |-> mk_register (#Rn y),
                 ``op2:addr_mode1`` |-> mk_addr_mode1 (#op2 y)]
            ``(f (c:condition) (rn:word4)
                 (op2:addr_mode1)):arm_instruction``
        else if opc = MOV orelse opc = MVN then
          subst [``f:condition -> bool -> word4 -> addr_mode1 ->
                     arm_instruction`` |-> mk_opcode opc,
                 ``c:condition`` |-> mk_condition c,
                 ``s:bool`` |-> mk_bool (#S y),
                 ``rd:word4`` |-> mk_register (#Rd y),
                 ``op2:addr_mode1`` |-> mk_addr_mode1 (#op2 y)]
            ``(f (c:condition) (s:bool) (rd:word4)
                 (op2:addr_mode1)):arm_instruction``
        else
          subst [``f:condition -> bool -> word4 -> word4 -> addr_mode1 ->
                     arm_instruction`` |-> mk_opcode opc,
                 ``c:condition`` |-> mk_condition c,
                 ``s:bool``   |-> mk_bool (#S y),
                 ``rd:word4`` |-> mk_register (#Rd y),
                 ``rn:word4`` |-> mk_register (#Rn y),
                 ``op2:addr_mode1`` |-> mk_addr_mode1 (#op2 y)]
            ``(f (c:condition) (s:bool) (rd:word4) (rn:word4)
                 (op2:addr_mode1)):arm_instruction``
      end
    | _ => raise err)
   | mk_data_proc _ = raise err
end;

fun mk_mla_mul (Instruction (x,c)) =
 (case x of
    Mla_mul y =>
      subst [``c:condition`` |-> mk_condition c,
             ``s:bool`` |-> mk_bool (#S y),
             ``rd:word4`` |-> mk_register (#Rd y),
             ``rm:word4`` |-> mk_register (#Rm y),
             ``rs:word4`` |-> mk_register (#Rs y),
             ``rn:word4`` |-> mk_register (#Rn y)]
      (case (#L y, #Signed y, #A y) of
         (false,_,false)    => ``MUL c s rd rm rs``
       | (false,_,true)     => ``MLA c s rd rm rs rn``
       | (true,false,false) => ``UMULL c s rd rn rm rs``
       | (true,false,true)  => ``UMLAL c s rd rn rm rs``
       | (true,true,false)  => ``SMULL c s rd rn rm rs``
       | (true,true,true)   => ``SMLAL c s rd rn rm rs``)
  | _ => raise ERR "mk_mla_mul" "not a multiply instruction")
 | mk_mla_mul _ = raise ERR "mk_mla_mul" "not a multiply instruction";

local
  fun mk_addr_mode2 x =
    case x of
      DtImmediate n =>
        subst [``i:word12`` |-> mk_word12 (Arbnum.fromInt n)] ``Dt_immediate i``
    | DtShiftImmediate i =>
        subst [``sh:shift`` |-> mk_shift (#Rm i) (#Sh i),
                ``imm:word5`` |-> mk_word5 (Arbnum.fromInt (#Imm i))]
        ``Dt_shift_immediate sh imm``

  fun mk_options (Ldr_str y) =
        subst [``p:bool`` |-> mk_bool (#P y),
               ``u:bool`` |-> mk_bool (#U y),
               ``b:bool`` |-> mk_bool (#B y),
               ``w:bool`` |-> mk_bool (#W y)]
        ``<| Pre := p; Up := u; BSN := b; Wb := w |>``
    | mk_options _ = raise ERR "mk_ldr_str" "not a load/store instruction"
  val err = ERR "mk_ldr_str" "not a load/store instruction"
in
  fun mk_ldr_str (Instruction(x,c)) =
   (case x of
      Ldr_str y =>
        subst [``c:condition`` |-> mk_condition c,
               ``opt:transfer_options`` |-> mk_options x,
               ``rd:word4`` |-> mk_register (#Rd y),
               ``rn:word4`` |-> mk_register (#Rn y),
               ``offset:addr_mode2`` |-> mk_addr_mode2 (#offset y)]
        (if #L y then
           ``instruction$LDR c opt rd rn offset``
         else
           ``instruction$STR c opt rd rn offset``)
    | _ => raise err)
   | mk_ldr_str _ = raise err
end;

local
  fun mk_options (Ldm_stm y) =
        subst [``p:bool`` |-> mk_bool (#P y),
               ``u:bool`` |-> mk_bool (#U y),
               ``s:bool`` |-> mk_bool (#S y),
               ``w:bool`` |-> mk_bool (#W y)]
        ``<| Pre := p; Up := u; BSN := s; Wb := w |>``
    | mk_options _ = raise ERR "mk_ldm_stm" "not a block transfer instruction"
  val err = ERR "mk_ldm_stm" "not a block transfer instruction"
in
  fun mk_ldm_stm (Instruction(x,c)) =
   (case x of
      Ldm_stm y =>
        subst [``c:condition`` |-> mk_condition c,
               ``opt:transfer_options`` |-> mk_options x,
               ``rn:word4``    |-> mk_register (#Rn y),
               ``list:word16`` |-> mk_word16 (Arbnum.fromInt (#list y))]
        (if #L y then
           ``instruction$LDM c opt rn list``
         else
           ``instruction$STM c opt rn list``)
    | _ => raise err)
   | mk_ldm_stm _ = raise err
end;

fun mk_swp (Instruction(x,c)) =
 (case x of
    Swp y =>
       subst [``c:condition`` |-> mk_condition c,
              ``b:bool``   |-> mk_bool (#B y),
              ``rd:word4`` |-> mk_register (#Rd y),
              ``rm:word4`` |-> mk_register (#Rm y),
              ``rn:word4`` |-> mk_register (#Rn y)]
      ``instruction$SWP c b rd rm rn``
  | _ => raise ERR "mk_swp" "not a swap instruction")
 | mk_swp _ = raise ERR "mk_swp" "not a swap instruction";

fun mk_mrs (Instruction(x,c)) =
 (case x of
    Mrs y =>
      subst [``c:condition`` |-> mk_condition c,
             ``r:bool``   |-> mk_bool (#R y),
             ``rd:word4`` |-> mk_register (#Rd y)]
        ``instruction$MRS c r rd``
  | _ => raise ERR "mk_mrs" "not an mrs instruction")
 | mk_mrs _ = raise ERR "mk_mrs" "not an mrs instruction";

local
  fun mk_msr_psr (Msr y) =
       (case (#R y,#bit19 y,#bit16 y) of
          (_,false,false) =>
             raise ERR "mk_msr" "either bit19 or bit16 must be set"
        | (false,false,true) => ``CPSR_c``
        | (false,true,false) => ``CPSR_f``
        | (false,true,true)  => ``CPSR_a``
        | (true,false,true)  => ``SPSR_c``
        | (true,true,false)  => ``SPSR_f``
        | (true,true,true)   => ``SPSR_a``)
    | mk_msr_psr _ = raise ERR "mk_msr" "not an msr instruction"

  fun mk_msr_immediate x =
  let val (n,m) = num2immediate x in
    subst [``n:word4`` |-> mk_word4 n,
           ``m:word8`` |-> mk_word8 m] ``Msr_immediate n m``
  end

  fun mk_msr_mode x =
        case x of
          MsrImmediate n => mk_msr_immediate n
        | MsrRegister r => subst [``r:word4`` |-> mk_register r]
            ``Msr_register r``

  val err = ERR "mk_msr" "not an msr instruction"
in
  fun mk_msr (Instruction(x,c)) =
   (case x of
      Msr y =>
        subst [``c:condition``  |-> mk_condition c,
               ``psrd:msr_psr`` |-> mk_msr_psr x,
               ``op:msr_mode``  |-> mk_msr_mode (#Op y)]
        ``instruction$MSR c psrd op``
    | _ => raise err)
   | mk_msr _ = raise err
end;

fun mk_cdp (Instruction(x,c)) =
 (case x of
    Cdp y =>
      subst [``c:condition`` |-> mk_condition c,
             ``cpn:word4``  |-> mk_word4 (Arbnum.fromInt (#CP y)),
             ``cop1:word4`` |-> mk_word4 (Arbnum.fromInt (#Cop1 y)),
             ``crd:word4``  |-> mk_register (#CRd y),
             ``crn:word4``  |-> mk_register (#CRn y),
             ``crm:word4``  |-> mk_register (#CRm y),
             ``cop2:word3`` |-> mk_word3 (Arbnum.fromInt (#Cop2 y))]
      ``instruction$CDP c cpn cop1 crd crn crm cop2``
  | _ => raise ERR "mk_cdp" "not a cdp instruction")
 | mk_cdp _ = raise ERR "mk_cdp" "not a cdp instruction";

fun mk_mcr_mrc (Instruction(x,c)) =
 (case x of
    Mcr_mrc y =>
      subst [``c:condition`` |-> mk_condition c,
             ``cpn:word4``  |-> mk_word4 (Arbnum.fromInt (#CP y)),
             ``cop1:word3`` |-> mk_word3 (Arbnum.fromInt (#Cop1 y)),
             ``rd:word4``   |-> mk_register (#Rd y),
             ``crn:word4``  |-> mk_register (#CRn y),
             ``crm:word4``  |-> mk_register (#CRm y),
             ``cop2:word3`` |-> mk_word3 (Arbnum.fromInt (#Cop2 y))]
      (if #L y then
         ``instruction$MRC c cpn cop1 rd crn crm cop2``
       else
         ``instruction$MCR c cpn cop1 rd crn crm cop2``)
  | _ => raise ERR "mk_mcr_mrc" "not an mcr or mrc instruction")
 | mk_mcr_mrc _ = raise ERR "mk_mcr_mrc" "not an mcr or mrc instruction";

local
  fun mk_options (Ldc_stc y) =
        subst [``p:bool`` |-> mk_bool (#P y),
               ``u:bool`` |-> mk_bool (#U y),
               ``n:bool`` |-> mk_bool (#N y),
               ``w:bool`` |-> mk_bool (#W y)]
        ``<| Pre := p; Up := u; BSN := n; Wb := w |>``
    | mk_options _ = raise ERR "mk_ldc_stc" "not an ldc or stc instruction"
  val err = ERR "mk_ldc_stc" "not an ldc or stc instruction"
in
  fun mk_ldc_stc (Instruction(x,c)) =
   (case x of
      Ldc_stc y =>
        subst [``c:condition`` |-> mk_condition c,
               ``opt:transfer_options`` |-> mk_options x,
               ``cpn:word4``   |-> mk_word4 (Arbnum.fromInt (#CP y)),
               ``crd:word4``   |-> mk_register (#CRd y),
               ``rn:word4``    |-> mk_register (#Rn y),
               ``offset:word8`` |-> mk_word8 (Arbnum.fromInt (#offset y))]
        (if #L y then
           ``instruction$LDC c opt cpn crd rn offset``
         else
           ``instruction$STC c opt cpn crd rn offset``)
    | _ => raise err)
  | mk_ldc_stc _ = raise err
end;

fun mk_undef c = subst [``c:condition`` |-> mk_condition c] ``UND c``;

(* ------------------------------------------------------------------------- *)

fun arm_to_term (i as Instruction (x,c)) =
 (case x of
    Br y        => mk_br i
  | Swi_ex      => mk_swi_ex c
  | Data_proc y => mk_data_proc i
  | Mla_mul y   => mk_mla_mul i
  | Ldr_str y   => mk_ldr_str i
  | Ldm_stm y   => mk_ldm_stm i
  | Swp y       => mk_swp i
  | Mrs y       => mk_mrs i
  | Msr y       => mk_msr i
  | Cdp y       => mk_cdp i
  | Mcr_mrc y   => mk_mcr_mrc i
  | Ldc_stc y   => mk_ldc_stc i
  | Undef       => mk_undef c)
 | arm_to_term (Data n) = mk_word32 n;

(* ------------------------------------------------------------------------- *)

local open Arbnum
  val max = pow(two, fromInt 32)
in
  fun num1comp n = (max - one) - n mod max
  fun num2comp n = (max - n mod max) mod max
  fun add32 a b = (a + b) mod max
end;

local
  fun ipow2 x = Word.toInt (Word.<<(Word.fromInt 1,Word.fromInt x))
  val (n12,n16,n24) = (ipow2 12,ipow2 16,ipow2 24)
in
  fun validate_instruction (Data n) = Data n
    | validate_instruction (ic as Instruction(i,c)) =
    case i of
      Br x => if #offset x <= n24 then ic else
                raise BadInstruction "Branch offset too large"
    | Data_proc x =>
       (case #op2 x of
          DpImmediate n =>
           (let val _ = num2immediate n in ic end handle HOL_ERR _ =>
              let val cn = num1comp n
                  fun copc a b = Instruction(Data_proc {opc = a, S = #S x,
                      Rd = #Rd x, Rn = #Rn x, op2 = DpImmediate b},c)
              in
                (case #opc x of
                   CMP => let val _ = num2immediate cn in copc CMN cn end
                 | CMN => let val _ = num2immediate cn in copc CMN cn end
                 | MOV => let val _ = num2immediate cn in copc MVN cn end
                 | MVN => let val _ = num2immediate cn in copc MOV cn end
                 | AND => let val _ = num2immediate cn in copc BIC cn end
                 | BIC => let val _ = num2immediate cn in copc AND cn end
                 | ADC => let val _ = num2immediate cn in copc SBC cn end
                 | SBC => let val _ = num2immediate cn in copc ADC cn end
                 | ADD => let val nn = num2comp n
                              val _ = num2immediate nn in copc SUB nn end
                 | SUB => let val nn = num2comp n
                              val _ = num2immediate nn in copc SUB nn end
                 | _ => raise BadInstruction
                          "Cannot represent the immediate value")
              end handle HOL_ERR _ => raise BadInstruction
                    "Cannot represent the immediate value")
        | DpShiftImmediate y => if #Imm y < 32 then ic else
            raise BadInstruction "Immediate shift value too large"
        | DpShiftRegister y => ic)
    | Ldr_str x =>
       (case #offset x of
          DtImmediate n => if n < n12 then ic else
            raise BadInstruction "Offset too large"
        | DtShiftImmediate y => if #Imm y < 32 then ic else
            raise BadInstruction "Immediate shift value too large")
    | Ldm_stm x => if #list x < n16 then ic else
                     raise BadInstruction "Block transfer list too long"
    | Msr x =>
       (case #Op x of
          MsrImmediate n =>
            (let val _ = num2immediate n in ic end handle HOL_ERR _ =>
               raise BadInstruction "Cannot represent the immediate value")
        | _ => ic)
    | Cdp x =>
        if 15 < #CP x   then raise BadInstruction "CP# too large" else
        if 15 < #Cop1 x then raise BadInstruction "CP Opc too large" else
        if 7  < #Cop2 x then raise BadInstruction "CP too large" else ic
    | Mcr_mrc x =>
        if 15 < #CP x   then raise BadInstruction "CP# too large" else
        if 7  < #Cop1 x then raise BadInstruction "CP Opc too large" else
        if 7  < #Cop2 x then raise BadInstruction "CP too large" else ic
    | Ldc_stc x =>
        if 15  < #CP x     then raise BadInstruction "CP# too large" else
        if 255 < #offset x then raise BadInstruction "offset too large" else ic
    | _ => ic;

  fun branch_to_arm (c,link,address) line =
        let open Arbnum
            val t = address - (fromInt 8)
            val jmp = add32 t (num2comp line)
            val offset = (jmp div (fromInt 4)) mod (fromInt n24)
            val ok = (if line <= t then jmp else num2comp jmp) <=
                     (fromHexString "FFFFFF")
        in
           if ok then
             Instruction(Br {L = link, offset = toInt offset},c)
           else
             raise Data.Parse "Invalid branch an instruction"
         end;

  fun assembler_to_instruction a =
    case a of
      [Code c] => c
    | [Mark line,BranchN (c,link,address)] =>
         branch_to_arm (c,link,address) line
    | [BranchN (c,link,address)] =>
         branch_to_arm (c,link,address) Arbnum.zero
    | [Label s, BranchS (c,link,l)] =>
         if s = l then
           Instruction(Br {L = link,
             offset = Arbnum.toInt (Arbnum.fromHexString "FFFFFE")},c)
         else
           raise Data.Parse "Not an instruction"
    | _ => raise Data.Parse "Not an instruction";
end;

fun simple_parse_arm_buf lexbuf =
  let val expr = Parser.Main Lexer.Token lexbuf in
    Parsing.clearParser(); expr
  end handle exn => (Parsing.clearParser(); raise exn);

val string_to_arm =
  validate_instruction o assembler_to_instruction o
  simple_parse_arm_buf o Lexing.createLexerString;

fun parse_arm_buf file stream lexbuf =
  let val expr = Parser.Main Lexer.Token lexbuf
            handle
               Parsing.ParseError f =>
                   let val pos1 = Lexing.getLexemeStart lexbuf
                       val pos2 = Lexing.getLexemeEnd lexbuf
                   in
                       Location.errMsg (file, stream, lexbuf)
                                       (Location.Loc(pos1, pos2))
                                       "Syntax error."
                   end
             | Lexer.LexicalError(msg, pos1, pos2) =>
                   if pos1 >= 0 andalso pos2 >= 0 then
                       Location.errMsg (file, stream, lexbuf)
                                       (Location.Loc(pos1, pos2))
                                       ("Lexical error: " ^ msg)
                   else
                       (Location.errPrompt ("Lexical error: " ^ msg ^ "\n\n");
                        raise Fail "Lexical error");
  in
    Parsing.clearParser(); expr
  end handle exn => (Parsing.clearParser(); raise exn);

fun createLexerStream (is : BasicIO.instream) =
  Lexing.createLexer (fn buff => fn n => Nonstdio.buff_input is buff 0 n);

fun parse_arm file =
  let val is = Nonstdio.open_in_bin file
      val lexbuf = createLexerStream is
      val expr = parse_arm_buf file is lexbuf handle exn =>
                   (BasicIO.close_in is; raise exn)
  in
    BasicIO.close_in is; expr
  end;

(* ------------------------------------------------------------------------- *)

fun index_size t = let open Arbnum in
   if t = ``:i3`` then fromInt 8 else
   if t = ``:i4`` then fromInt 16 else
   if t = ``:i5`` then fromInt 32 else
   if t = ``:i8`` then fromInt 256 else
   if t = ``:i12`` then fromInt 4096 else
   if t = ``:i16`` then fromInt 65536 else
   if t = ``:i24`` then fromInt 16777216 else
   if t = ``:i32`` then fromString "4294967296" else
    raise ERR "index_mod_size" "unknown word size"
end;

fun dest_word t = let val (n,typ) = dest_n2w t in
  Arbnum.mod(numLib.dest_numeral n,index_size typ) end;

val dest_wordi    = Arbnum.toInt o dest_word;
val dest_register = Lexer.int2register o dest_wordi;

fun dest_bool t =
  if term_eq t T then true else
  if term_eq t F then false else
    raise ERR "dest_bool" "neither T nor F";

fun dest_condition t = let val eqt = term_eq t
in
  if eqt ``EQ`` then EQ else
  if eqt ``NE`` then NE else
  if eqt ``CS`` then CS else
  if eqt ``CC`` then CC else
  if eqt ``MI`` then MI else
  if eqt ``PL`` then PL else
  if eqt ``VS`` then VS else
  if eqt ``VC`` then VC else
  if eqt ``HI`` then HI else
  if eqt ``LS`` then LS else
  if eqt ``GE`` then GE else
  if eqt ``LT`` then LT else
  if eqt ``GT`` then GT else
  if eqt ``LE`` then LE else
  if eqt ``AL`` then AL else
  if eqt ``NV`` then NV else
    raise ERR "dest_condition" "not an instance of :condition"
end;

local
  val err = ERR "dest_br" "not a variable-free branch instruction"
in
  fun dest_br t =
   (case strip_comb t of
      (i, [c, offset]) => let val l = term_eq i ``instruction$BL`` in
          if l orelse term_eq i ``instruction$B`` then
            Instruction(Br {L = l,offset = dest_wordi offset},dest_condition c)
          else
            raise err
        end
    | _ => raise err)
    handle HOL_ERR _ => raise err
end;

local
  val err = ERR "dest_swi_ex" "not a valid swi_ex instruction"
in
  fun dest_swi_ex t =
  let val (i,c) = dest_comb t in
     if term_eq i ``instruction$SWI`` then
       Instruction(Swi_ex, dest_condition c)
     else
       raise err
  end handle HOL_ERR _ => raise err
end;

local
  val err = ERR "dest_undef" "not a valid undefined instruction"
in
  fun dest_undef t =
  let val (i,c) = dest_comb t in
     if term_eq i ``instruction$UND`` then
       Instruction(Undef, dest_condition c)
     else
       raise err
  end handle HOL_ERR _ => raise err
end;

fun dest_opc1 t = let val eqt = term_eq t
in
  if eqt ``instruction$AND`` then AND else
  if eqt ``instruction$EOR`` then EOR else
  if eqt ``instruction$SUB`` then SUB else
  if eqt ``instruction$RSB`` then RSB else
  if eqt ``instruction$ADD`` then ADD else
  if eqt ``instruction$ADC`` then ADC else
  if eqt ``instruction$SBC`` then SBC else
  if eqt ``instruction$RSC`` then RSC else
  if eqt ``instruction$ORR`` then ORR else
  if eqt ``instruction$BIC`` then BIC else raise ERR "dest_opc1"
     "term is not: AND, EOR, SUB, RSB, ADD, ADC, SBC, RSC, ORR or BIC"
end;

fun dest_opc2 t = let val eqt = term_eq t
in
  if eqt ``instruction$TST`` then TST else
  if eqt ``instruction$TEQ`` then TEQ else
  if eqt ``instruction$CMP`` then CMP else
  if eqt ``instruction$CMN`` then CMN else
    raise ERR "dest_opc2" "term is not: TST, TEQ, CMP or CMN"
end;

fun dest_opc3 t =
  if term_eq t ``instruction$MOV`` then MOV else
  if term_eq t ``instruction$MVN`` then MVN else
    raise ERR "dest_opc3" "term is not: MOV or MVN";

fun dest_shift t =
let val (s,r) = dest_comb t in
  if term_eq s ``instruction$LSL`` then (LSL, dest_register r) else
  if term_eq s ``instruction$LSR`` then (LSR, dest_register r) else
  if term_eq s ``instruction$ASR`` then (ASR, dest_register r) else
  if term_eq s ``instruction$ROR`` then (ROR, dest_register r) else
    raise ERR "dest_shift" "not a valid term of type :shift"
end;

local
  val err = ERR "dest_addr_mode1" "not a valid instance of :addr_mode1"
in
  fun dest_addr_mode1 t =
    case strip_comb t of
      (m, [x, y]) =>
        if term_eq m ``Dp_immediate`` then
          DpImmediate (mk_immediate (dest_wordi x) (dest_word y))
        else let val (s,rm) = dest_shift x in
          if term_eq m ``Dp_shift_immediate`` then
            DpShiftImmediate {Imm = dest_wordi y, Sh = s, Rm = rm}
          else if term_eq m ``Dp_shift_register`` then
            DpShiftRegister {Rs = dest_register y, Sh = s, Rm = rm}
          else raise err
        end
    | _ => raise err
end;

local
  val err = ERR "dest_data_proc" "not a variable-free data_proc instruction"
in
  fun dest_data_proc t =
   (case strip_comb t of
      (opc, [c,s,rd,rn,op2]) =>
         Instruction(Data_proc {opc = dest_opc1 opc, S = dest_bool s,
           Rd = dest_register rd, Rn = dest_register rn,
           op2 = dest_addr_mode1 op2},dest_condition c)
    | (opc, [c,rn,op2]) =>
         Instruction(Data_proc {opc = dest_opc2 opc, S = true,
           Rd = R0, Rn = dest_register rn,
           op2 = dest_addr_mode1 op2},dest_condition c)
    | (opc, [c,s,rd,op2]) =>
         Instruction(Data_proc {opc = dest_opc3 opc, S = dest_bool s,
           Rd = dest_register rd, Rn = R0,
           op2 = dest_addr_mode1 op2},dest_condition c)
    | _ => raise err)
    handle HOL_ERR _ => raise err
end;

local
  val err = ERR "dest_mla_mul" "not a variable-free multiply instruction"
in
  fun dest_mla_mul t =
   (case strip_comb t of
      (i, [c,s,rd,rm,rs]) =>
         if term_eq i ``instruction$MUL`` then
           Instruction(Mla_mul {L = false, Signed = false,
             A = false, S = dest_bool s,
             Rd = dest_register rd, Rm = dest_register rm,
             Rs = dest_register rs, Rn = R0},dest_condition c)
         else
           raise err
    | (i, [c,s,rd,rm,rs,rn]) =>
         if term_eq i ``instruction$MLA`` then
           Instruction(Mla_mul {L = false, Signed = false,
             A = true, S = dest_bool s,
             Rd = dest_register rd, Rm = dest_register rm,
             Rs = dest_register rs, Rn = dest_register rn},dest_condition c)
         else if term_eq i ``instruction$UMULL`` then
           Instruction(Mla_mul {L = true, Signed = false,
             A = false, S = dest_bool s,
             Rd = dest_register rd, Rm = dest_register rs,
             Rs = dest_register rn, Rn = dest_register rm},dest_condition c)
         else if term_eq i ``instruction$UMLAL`` then
           Instruction(Mla_mul {L = true, Signed = false,
             A = true, S = dest_bool s,
             Rd = dest_register rd, Rm = dest_register rs,
             Rs = dest_register rn, Rn = dest_register rm},dest_condition c)
         else if term_eq i ``instruction$SMULL`` then
           Instruction(Mla_mul {L = true, Signed = true,
             A = false, S = dest_bool s,
             Rd = dest_register rd, Rm = dest_register rs,
             Rs = dest_register rn, Rn = dest_register rm},dest_condition c)
         else if term_eq i ``instruction$SMLAL`` then
           Instruction(Mla_mul {L = true, Signed = true,
             A = true, S = dest_bool s,
             Rd = dest_register rd, Rm = dest_register rs,
             Rs = dest_register rn, Rn = dest_register rm},dest_condition c)
         else
           raise err
    | _ => raise err)
    handle HOL_ERR _ => raise err
end;

fun dest_options t =
  case TypeBase.dest_record t of
    [("Pre", p), ("Up", u), ("BSN", b), ("Wb", w)] =>
       (dest_bool p, dest_bool u, dest_bool b, dest_bool w)
  | _ => raise ERR "dest_options" "not an instance of type :transfer_options";

local
  val err = ERR "dest_addr_mode1" "not a valid instance of :addr_mode1"
in
  fun dest_addr_mode2 t =
   (case strip_comb t of
      (m, [n]) =>
        if term_eq m ``Dt_immediate`` then
          DtImmediate (dest_wordi n)
        else
          raise err
    | (m, [sh, i]) =>
        if term_eq m ``Dt_shift_immediate`` then
          let val (s,rm) = dest_shift sh in
            DtShiftImmediate {Imm = dest_wordi i, Sh = s, Rm = rm}
          end
        else
          raise err
    | _ => raise err)
    handle HOL_ERR _ => raise err
end;

local
  val err = ERR "dest_ldr_str" "not a variable-free load/store instruction"
in
  fun dest_ldr_str t =
   (case strip_comb t of
      (i, [c,opt,rd,rn,offset]) =>
        let val l = term_eq i ``instruction$LDR``
            val (p,u,b,w) = dest_options opt
        in
          if l orelse term_eq i ``instruction$STR`` then
            Instruction(Ldr_str {L = l,offset = dest_addr_mode2 offset,
              Rd = dest_register rd, Rn = dest_register rn,
              P = p, U = u, B = b, W = w},dest_condition c)
          else
            raise err
        end
    | _ => raise err)
    handle HOL_ERR _ => raise err
end;

local
  val err = ERR "dest_ldm_stm" "not a variable-free block transfer instruction"
in
  fun dest_ldm_stm t =
   (case strip_comb t of
      (i, [c,opt,rn,list]) =>
        let val l = term_eq i ``instruction$LDM``
            val (p,u,b,w) = dest_options opt
        in
          if l orelse term_eq i ``instruction$STM`` then
            Instruction(Ldm_stm {L = l,list = dest_wordi list,
              Rn = dest_register rn, P = p, U = u, S = b, W = w},
              dest_condition c)
          else
            raise err
        end
    | _ => raise err)
    handle HOL_ERR _ => raise err
end;

local
  val err = ERR "dest_swp" "not a variable-free swap instruction"
in
  fun dest_swp t =
   (case strip_comb t of
      (i, [c,b,rd,rm,rn]) =>
        if term_eq i ``instruction$SWP`` then
          Instruction(Swp {B = dest_bool b,Rd = dest_register rd,
            Rm = dest_register rm, Rn = dest_register rn},dest_condition c)
        else
          raise err
    | _ => raise err)
    handle HOL_ERR _ => raise err
end;

local
  val err = ERR "dest_mrs" "not a variable-free mrs instruction"
in
  fun dest_mrs t =
   (case strip_comb t of
      (i, [c,r,rd]) =>
        if term_eq i ``instruction$MRS`` then
          Instruction(Mrs {R = dest_bool r,Rd = dest_register rd},
            dest_condition c)
        else
          raise err
    | _ => raise err)
    handle HOL_ERR _ => raise err
end;

fun dest_msr_psr t = let val eqt = term_eq t
in
  if eqt ``CPSR_c`` then (false,false,true) else
  if eqt ``CPSR_f`` then (false,true,false) else
  if eqt ``CPSR_a`` then (false,true,true) else
  if eqt ``SPSR_c`` then (true,false,true) else
  if eqt ``SPSR_f`` then (true,true,false) else
  if eqt ``SPSR_a`` then (true,true,true) else
    raise ERR "dest_msr_psr" "not a valid instance of :msr_psr"
end;

local
  val err = ERR "dest_addr_mode1" "not a valid instance of :msr_mode"
in
  fun dest_msr_mode t =
   (case strip_comb t of
      (m, [x, y]) =>
        if term_eq m ``Msr_immediate`` then
          MsrImmediate (mk_immediate (dest_wordi x) (dest_word y))
        else
          raise err
    | (m, [x]) =>
        if term_eq m ``Msr_register`` then
          MsrRegister (dest_register x)
        else
          raise err
    | _ => raise err) handle HOL_ERR _ => raise err
end;

local
  val err = ERR "dest_msr" "not a variable-free mrs instruction"
in
  fun dest_msr t =
   (case strip_comb t of
      (i, [c,psrd,opnd]) =>
        if term_eq i ``instruction$MSR`` then
          let val (r,b19,b16) = dest_msr_psr psrd in
            Instruction(Msr {R = r, bit19 = b19, bit16 = b16,
              Op = dest_msr_mode opnd},dest_condition c)
          end
        else
          raise err
    | _ => raise err)
    handle HOL_ERR _ => raise err
end;

local
  val err = ERR "dest_cdp" "not a variable-free cdp instruction"
in
  fun dest_cdp t =
   (case strip_comb t of
      (i, [c,cpn,cop1,crd,crn,crm,cop2]) =>
        if term_eq i ``instruction$CDP`` then
          Instruction(Cdp {CP = dest_wordi cpn, CRd = dest_register crd,
            CRn = dest_register crn, CRm = dest_register crm,
            Cop1 = dest_wordi cop1, Cop2 = dest_wordi cop2},dest_condition c)
        else
          raise err
    | _ => raise err)
    handle HOL_ERR _ => raise err
end;

local
  val err = ERR "dest_ldc_stc" "not a variable-free ldc/stc instruction"
in
  fun dest_ldc_stc t =
   (case strip_comb t of
      (i, [c,opt,cpn,crd,rn,offset]) =>
        let val l = term_eq i ``instruction$LDC``
            val (p,u,b,w) = dest_options opt
        in
          if l orelse term_eq i ``instruction$STC`` then
            Instruction(Ldc_stc {CP = dest_wordi cpn, CRd = dest_register crd,
              L = l, P = p, U = u, N = b, W = w, Rn = dest_register rn,
              offset = dest_wordi offset},dest_condition c)
          else
            raise err
        end
    | _ => raise err)
    handle HOL_ERR _ => raise err
end;

local
  val err = ERR "dest_mcr_mrc" "not a variable-free mcr/mrc instruction"
in
  fun dest_mcr_mrc t =
   (case strip_comb t of
      (i, [c,cpn,cop1,rd,crn,crm,cop2]) =>
        let val l = term_eq i ``instruction$MCR`` in
          if l orelse term_eq i ``instruction$MRC`` then
            Instruction(Mcr_mrc {CP = dest_wordi cpn, L = l,
              CRn = dest_register crn, CRm = dest_register crm,
              Rd = dest_register rd, Cop1 = dest_wordi cop1,
              Cop2 = dest_wordi cop2},dest_condition c)
          else
            raise err
        end
    | _ => raise err)
    handle HOL_ERR _ => raise err
end;

(* ------------------------------------------------------------------------- *)

fun term_to_arm t =
  if type_of t = ``:word32`` then
    Data (dest_word t)
  else let val opc = fst (strip_comb t)
           val eqt = term_eq opc
  in
    if eqt ``instruction$SWI`` then
      dest_swi_ex t
    else if eqt ``instruction$B`` orelse eqt ``instruction$BL`` then
      dest_br t
    else if eqt ``instruction$MUL`` orelse eqt ``instruction$MLA`` orelse
            eqt ``instruction$UMULL`` orelse eqt ``instruction$UMLAL`` orelse
            eqt ``instruction$SMULL`` orelse eqt ``instruction$SMLAL`` then
      dest_mla_mul t
    else if eqt ``instruction$LDR`` orelse eqt ``instruction$STR`` then
      dest_ldr_str t
    else if eqt ``instruction$LDM`` orelse eqt ``instruction$STM`` then
      dest_ldm_stm t
    else if eqt ``instruction$SWP`` then
      dest_swp t
    else if eqt ``instruction$MRS`` then
      dest_mrs t
    else if eqt ``instruction$MSR`` then
      dest_msr t
    else if eqt ``instruction$CDP`` then
      dest_cdp t
    else if eqt ``instruction$LDC`` orelse eqt ``instruction$STC`` then
      dest_ldc_stc t
    else if eqt ``instruction$MCR`` orelse eqt ``instruction$MRC`` then
      dest_mcr_mrc t
    else if eqt ``instruction$UND`` then
      dest_undef t
    else
      dest_data_proc t
  end
handle HOL_ERR _ =>
  raise ERR "term_to_arm" "not a variable-free ARM instruction";

(* ------------------------------------------------------------------------- *)

infix 0 <<;

fun op << (x,y) = let open Arbnum in
  x * pow(two, fromInt y)
end;

val register_to_num = Arbnum.fromInt o register2int;

fun condition_to_num cond = Arbnum.fromInt
 (case cond of
    EQ => 0  | NE => 1  | CS => 2  | CC => 3
  | MI => 4  | PL => 5  | VS => 6  | VC => 7
  | HI => 8  | LS => 9  | GE => 10 | LT => 11
  | GT => 12 | LE => 13 | AL => 14 | NV => 15) << 28;

fun shift_to_num (s,r) =
  Arbnum.+(register_to_num r,Arbnum.fromHexString
    (case s of
       LSL => "0"  | LSR => "20"
     | ASR => "40" | ROR => "60"));

fun sbit b i = if b then Arbnum.one << i else Arbnum.zero;

fun addr_mode1_to_num x = let open Arbnum
in
  case x of
    DpImmediate n =>
      let val (rot,imm) = num2immediate n in
        fromHexString "2000000" + (rot << 8) + imm
      end
  | DpShiftImmediate i =>
      (fromInt (#Imm i) << 7) + shift_to_num (#Sh i, #Rm i)
  | DpShiftRegister r =>
      fromHexString "10" + (register_to_num (#Rs r) << 8) +
      shift_to_num (#Sh r, #Rm r)
end;

fun addr_mode2_to_num x = let open Arbnum
in
  case x of
    DtImmediate n => fromInt n
  | DtShiftImmediate i => fromHexString "2000000" + (fromInt (#Imm i) << 7) +
                            shift_to_num (#Sh i, #Rm i)
end;

fun msr_mode_to_num x = let open Arbnum
in
  case x of
    MsrImmediate n =>
      let val (rot,imm) = num2immediate n in
        fromHexString "2000000" + (rot << 8) + imm
      end
  | MsrRegister r => register_to_num r
end;

fun msr_psr_to_num x = Arbnum.fromHexString
 (case x of
    (false,false,true) => "10000"
  | (false,true,false) => "80000"
  | (false,true,true)  => "90000"
  | (true,false,true)  => "410000"
  | (true,true,false)  => "480000"
  | (true,true,true)   => "490000"
  | _ => "0");

fun options_to_num (p,u,b,w) =
let open Arbnum
in
  sbit p 24 + sbit u 23 + sbit b 22 + sbit w 21
end;

fun opcode2int opc =
  case opc of
    AND => 0  | EOR => 1  | SUB => 2  | RSB => 3
  | ADD => 4  | ADC => 5  | SBC => 6  | RSC => 7
  | TST => 8  | TEQ => 9  | CMP => 10 | CMN => 11
  | ORR => 12 | MOV => 13 | BIC => 14 | MVN => 15;

fun opcode_to_num opc = Arbnum.fromInt (opcode2int opc) << 21;

fun srn_srd opc =
  if mem opc [TST,TEQ,CMP,CMN] then (true,false) else
  if opc = MOV orelse opc = MVN then (false,true) else
    (true,true);

fun arm_to_num (Data n) = n
  | arm_to_num (Instruction(x,c)) =
let open Arbnum
in
  condition_to_num c +
  (case x of
     Br y =>
       fromHexString (if #L y then "B000000" else "A000000") +
       fromInt (#offset y)
   | Swi_ex =>
       fromHexString "F000000"
   | Data_proc y =>
       let val (srn,srd) = srn_srd (#opc y) in
         (sbit (#S y) 20) + opcode_to_num (#opc y) +
         (if srn then register_to_num (#Rn y) << 16 else zero) +
         (if srd then register_to_num (#Rd y) << 12 else zero) +
         addr_mode1_to_num (#op2 y)
       end
   | Mla_mul y =>
       (sbit (#L y) 23) + (sbit (#Signed y) 22) +
       (sbit (#A y) 21) + (sbit (#S y) 20) + fromHexString "90" +
       (register_to_num (#Rd y) << 16) + (register_to_num (#Rn y) << 12) +
       (register_to_num (#Rs y) << 8) + register_to_num (#Rm y)
   | Ldr_str y =>
       fromHexString "4000000" + (sbit (#L y) 20) +
       options_to_num (#P y, #U y, #B y, #W y) +
       (register_to_num (#Rn y) << 16) + (register_to_num (#Rd y) << 12) +
       addr_mode2_to_num (#offset y)
   | Ldm_stm y =>
       fromHexString "8000000" + (sbit (#L y) 20) +
       options_to_num (#P y, #U y, #S y, #W y) +
       (register_to_num (#Rn y) << 16) + fromInt (#list y)
   | Swp y =>
       fromHexString "1000090" + (sbit (#B y) 22) +
       (register_to_num (#Rn y) << 16) + (register_to_num (#Rd y) << 12) +
       register_to_num (#Rm y)
   | Mrs y =>
       fromHexString "10F0000" + (sbit (#R y) 22) +
       (register_to_num (#Rd y) << 12)
   | Msr y =>
       fromHexString "120F000" + msr_psr_to_num (#R y, #bit19 y, #bit16 y) +
       msr_mode_to_num (#Op y)
   | Cdp y =>
       fromHexString "E000000" + (fromInt (#Cop1 y) << 20) +
       (register_to_num (#CRn y) << 16) + (register_to_num (#CRd y) << 12) +
       (fromInt (#CP y) << 8) + (fromInt (#Cop2 y) << 5) +
       register_to_num (#CRm y)
   | Ldc_stc y =>
       fromHexString "C000000" + (sbit (#L y) 20) +
       options_to_num (#P y, #U y, #N y, #W y) +
       (register_to_num (#Rn y) << 16) + (register_to_num (#CRd y) << 12) +
       (fromInt (#CP y) << 8) + fromInt (#offset y)
   | Mcr_mrc y =>
       fromHexString "E000010" + (sbit (#L y) 20) + (fromInt (#Cop1 y) << 21) +
       (register_to_num (#CRn y) << 16) + (register_to_num (#Rd y) << 12) +
       (fromInt (#CP y) << 8) + (fromInt (#Cop2 y) << 5) +
       register_to_num (#CRm y)
   | Undef => fromHexString "6000010")
end;

(* ------------------------------------------------------------------------- *)

(* val toUpperString = I; *)
val toUpperString = String.map Char.toUpper;
fun nspaces_string n = funpow n (fn x => " " ^ x) "";

fun mnemonic a s = let val max_width = 8 in
  (toUpperString s) ^ (if a then nspaces_string (max_width - size s) else " ")
end;

fun shift2string x = toUpperString(
  case x of
    LSL => "lsl"
  | LSR => "lsr"
  | ASR => "asr"
  | ROR => "ror");

fun shift_immediate2string (y:{Imm : int, Rm : register, Sh : shift}) =
  reg2string (#Rm y) ^
    (if #Imm y = 0 then toUpperString(
       case #Sh y of
         LSL => ""
       | LSR => ", lsr #32"
       | ASR => ", asr #32"
       | ROR => ", rrx")
     else
       ", " ^ shift2string (#Sh y) ^ " #" ^ int_to_string (#Imm y));

(* ------------------------------------------------------------------------- *)

local
  val n25 = Word.toInt (Word.<<(Word.fromInt 1,Word.fromInt 25))
  val n26 = Word.toInt (Word.<<(Word.fromInt 1,Word.fromInt 26))
  fun offset2comp i = Int.mod(n26 - i,n26)
  fun abs_offset_string i j =
        "0x" ^ Arbnum.toHexString(Arbnum.+(i,Arbnum.fromInt (4 * j + 8)))
  fun rel_offset_string i =
      let val j = Int.mod(Int.mod((i + 2) * 4,n26),n26) in
        if j < n25 then
          int_to_string j
        else
          "-" ^ int_to_string (offset2comp j)
      end
  val err = ERR "br_to_string" "not a branch instruction"
in
  fun br_to_string l a (Instruction(x,c)) =
   (case x of
      Br y =>
        let val h = mnemonic a ("b" ^ (if #L y then "l" else "") ^
                      condition2string c)
        in
           h ^ (if isSome l then abs_offset_string (valOf l) (#offset y)
                            else rel_offset_string (#offset y) ^ "; relative")
        end
    | _ => raise err)
   | br_to_string _ _ _ = raise err
  fun branch_to_string (BranchS(c,l,d)) =
        mnemonic false ("b" ^ (if l then "l" else "") ^ condition2string c) ^ d
    | branch_to_string (BranchN(c,l,n)) =
        mnemonic false ("b" ^ (if l then "l" else "") ^ condition2string c) ^
          "0x" ^ Arbnum.toHexString n
    | branch_to_string _ = raise err
end;

fun swi_ex_to_string c = toUpperString ("swi" ^ condition2string c);

local
  fun addr_mode2string x =
    case x of
      DpImmediate n => "#" ^ Arbnum.toString n
    | DpShiftImmediate i => shift_immediate2string i
    | DpShiftRegister r =>
        reg2string (#Rm r) ^ ", " ^ shift2string (#Sh r) ^ " " ^
        reg2string (#Rs r)
  val err = ERR "data_proc_to_string" "not a data processing instruction"
in
  fun data_proc_to_string a (Instruction(x,c)) =
   (case x of
      Data_proc y =>
        let val opc = #opc y
            val bop = mem opc [TST,TEQ,CMP,CMN]
            val h = mnemonic a (opcode2string opc ^ condition2string c ^
                      (if #S y andalso not bop then "s" else ""))
        in
          h ^ (if bop then "" else reg2string (#Rd y) ^ ", ") ^
          (if opc = MOV orelse opc = MVN then ""
           else reg2string (#Rn y) ^ ", ") ^ addr_mode2string (#op2 y)
        end
    | _ => raise err)
   | data_proc_to_string _ _ = raise err
end;

local
  val err = ERR "mla_mul_to_string" "not a multiply instruction"
in
  fun mla_mul_to_string a (Instruction(x,c)) =
   (case x of
      Mla_mul y =>
        let val opc = case (#L y,#Signed y,#A y) of
                        (false,_,false)    => "mul"
                      | (false,_,true)     => "mla"
                      | (true,false,false) => "umull"
                      | (true,false,true)  => "umlal"
                      | (true,true,false)  => "smull"
                      | (true,true,true)   => "smlal"
            val h = mnemonic a (opc ^ condition2string c ^
                                (if #S y then "s" else ""))
        in
          h ^ reg2string (#Rd y) ^ ", " ^
          (if #L y then reg2string (#Rn y) ^ ", " else "") ^
          reg2string (#Rm y) ^ ", " ^ reg2string (#Rs y) ^
          (if not (#L y) andalso #A y then ", " ^ reg2string (#Rn y) else "")
        end
    | _ => raise err)
   | mla_mul_to_string _ _ = raise err
end;

local
  fun addr_mode2string U x =
    case x of
      DtImmediate n =>
        if n = 0 then "" else
          ", #" ^ (if U then "" else "-") ^ int_to_string n
    | DtShiftImmediate i =>
        ", " ^ (if U then "" else "-") ^ shift_immediate2string i
  val err = ERR "ldr_str_to_string" "not a load/store instruction"
in
  fun ldr_str_to_string a (Instruction(x,c)) =
   (case x of
      Ldr_str y =>
        let val h = mnemonic a ((if #L y then "ldr" else "str") ^
                      condition2string c ^ (if #B y then "b" else ""))
            val offset = addr_mode2string (#U y) (#offset y)
        in
          h ^ reg2string (#Rd y) ^ ", [" ^ reg2string (#Rn y) ^
          (if #P y then
             offset ^ "]" ^ (if #W y then "!" else "")
           else
             "]" ^ offset)
        end
    | _ => raise err)
   | ldr_str_to_string _ _ = raise err
end;

local
  fun finish i ys = if ys = [] then [(i,i)] else ((fst (hd ys), i)::(tl ys))

  fun blocks [] i ys = ys
    | blocks [x] i ys = if x then finish i ys else ys
    | blocks (x::y::xs) i ys =
    case (x,y) of
      (true,true) => blocks (y::xs) (i + 1) ys
    | (false,true) => blocks (y::xs) (i + 1) ((i + 1,~1)::ys)
    | (true,false) => blocks (y::xs) (i + 1) (finish i ys)
    | (false,false) => blocks (y::xs) (i + 1) ys

  fun make_blocks l = rev (blocks l 0 (if hd l then [(0,~1)] else []))

  fun regn2string n = "r" ^ int_to_string n;

  fun blocks2string [] s = s ^ "}"
    | blocks2string ((i,j)::xs) s =
        blocks2string xs (s ^ regn2string i ^
          (if i = j then
            ""
           else if i + 1 = j then
            ", " ^ regn2string j
           else
            "-" ^ regn2string j) ^
          (if xs = [] then "" else ", "))

  fun reg_list2string l = blocks2string (make_blocks (
        List.take(num2list 16 (Arbnum.fromInt l),16))) "{"

  fun mode2string p u =
    case (p,u) of
      (false,false) => "da"
    | (false,true)  => "ia"
    | (true,false)  => "db"
    | (true,true)   => "ib";
  val err = ERR "ldm_stm_to_string" "not a block transfer instruction"
in
  fun ldm_stm_to_string a (Instruction(x,c)) =
   (case x of
      Ldm_stm y =>
        let val h = mnemonic a ((if #L y then "ldm" else "stm") ^
                      condition2string c ^ mode2string (#P y) (#U y))
        in
          h ^ reg2string (#Rn y) ^ (if #W y then "!, " else ", ") ^
          reg_list2string (#list y) ^ (if #S y then "^" else "")
        end
    | _ => raise err)
   | ldm_stm_to_string _ _ = raise err
end;

fun swp_to_string a (Instruction(x,c)) =
 (case x of
    Swp y =>
      let val h = mnemonic a ("swp" ^ condition2string c ^
                    (if #B y then "b" else ""))
      in
        h ^ reg2string (#Rd y) ^ ", " ^ reg2string (#Rm y) ^ ", [" ^
        reg2string (#Rn y) ^ "]"
      end
  | _ => raise ERR "swp_to_string" "not a swap instruction")
 | swp_to_string _ _ = raise ERR "swp_to_string" "not a swap instruction";

fun mrs_to_string a (Instruction(x,c)) =
 (case x of
    Mrs y =>
      let val h = mnemonic a ("mrs" ^ condition2string c)
      in
        h ^ reg2string (#Rd y) ^ ", " ^ (if #R y then "SPSR" else "CPSR")
      end
  | _ => raise ERR "mrs_to_string" "not an mrs instruction")
 | mrs_to_string _ _ = raise ERR "mrs_to_string" "not an mrs instruction";

fun msr_to_string a (Instruction(x,c)) =
 (case x of
    Msr y =>
      let val h = mnemonic a ("msr" ^ condition2string c)
      in
        h ^ (if #R y then "SPSR" else "CPSR") ^
        (if #bit19 y andalso not (#bit16 y) then
           "_f, "
         else if not (#bit19 y) andalso #bit16 y then
           "_c, "
         else
           ", ") ^
        (case #Op y of
           MsrImmediate n => "#" ^ Arbnum.toString n
         | MsrRegister r => reg2string r)
      end
  | _ => raise ERR "msr_to_string" "not an msr instruction")
 | msr_to_string _ _ = raise ERR "msr_to_string" "not an msr instruction";

fun cdp_to_string a (Instruction(x,c)) =
 (case x of
    Cdp y =>
      let val h = mnemonic a ("cdp" ^ condition2string c)
      in
        h ^ cp_num2string (#CP y) ^ ", " ^ int_to_string (#Cop1 y) ^ ", " ^
        cp_reg2string (#CRd y) ^ ", " ^ cp_reg2string (#CRn y) ^ ", " ^
        cp_reg2string (#CRm y) ^
        (if #Cop2 y = 0 then "" else ", " ^ int_to_string (#Cop2 y))
      end
  | _ => raise ERR "cdp_to_string" "not a cdp instruction")
 | cdp_to_string _ _ = raise ERR "cdp_to_string" "not a cdp instruction";

local
  val err = ERR "mcr_mrc_to_string" "not an mcr or mrc instruction"
in
  fun mcr_mrc_to_string a (Instruction(x,c)) =
   (case x of
      Mcr_mrc y =>
        let val h = mnemonic a ((if #L y then "mrc" else "mcr") ^
                      condition2string c)
        in
          h ^ cp_num2string (#CP y) ^ ", " ^ int_to_string (#Cop1 y) ^ ", " ^
          reg2string (#Rd y) ^ ", " ^ cp_reg2string (#CRn y) ^ ", " ^
          cp_reg2string (#CRm y) ^
          (if # Cop2 y = 0 then "" else ", " ^ int_to_string (#Cop2 y))
        end
    | _ => raise err)
   | mcr_mrc_to_string _ _ = raise err
end;

local
  val err = ERR "ldc_stc_to_string" "not an ldc or stc instruction"
in
  fun ldc_stc_to_string a (Instruction(x,c)) =
   (case x of
      Ldc_stc y =>
        let val h = mnemonic a ((if #L y then "ldc" else "stc") ^
                      condition2string c)
            val offset = if #offset y = 0 then "" else
                  (if #U y then ", #" else ", #-") ^
                     int_to_string (4 * #offset y)
        in
          h ^ cp_num2string (#CP y) ^ ", " ^ cp_reg2string (#CRd y) ^ ", [" ^
          reg2string (#Rn y) ^
          (if #P y then
             offset ^ "]" ^ (if #W y then "!" else "")
           else
             "]" ^ offset)
        end
    | _ => raise err)
   | ldc_stc_to_string _ _ = raise err
end;

(* ------------------------------------------------------------------------- *)

fun arm_to_string l a (i as Instruction (x,c)) =
 (case x of
    Br y        => br_to_string l a i
  | Swi_ex      => swi_ex_to_string c
  | Data_proc y => data_proc_to_string a i
  | Mla_mul y   => mla_mul_to_string a i
  | Ldr_str y   => ldr_str_to_string a i
  | Ldm_stm y   => ldm_stm_to_string a i
  | Swp y       => swp_to_string a i
  | Mrs y       => mrs_to_string a i
  | Msr y       => msr_to_string a i
  | Cdp y       => cdp_to_string a i
  | Mcr_mrc y   => mcr_mrc_to_string a i
  | Ldc_stc y   => ldc_stc_to_string a i
  | Undef       => "0x" ^ Arbnum.toHexString (arm_to_num i))
 | arm_to_string _ _ (Data n) = "0x" ^ Arbnum.toHexString n;

fun assembler_to_string i a l =
  let val s = if isSome l then (valOf l) ^ ": " else "" in
    case a of
      Data.Code c => s ^ arm_to_string i false c
    | Data.BranchS b => s ^ branch_to_string a
    | Data.BranchN b => s ^ branch_to_string a
    | _ => ""
  end;

(* ------------------------------------------------------------------------- *)

val encode_arm = arm_to_num o string_to_arm;
fun decode_arm i n = arm_to_string i false (num_to_arm n);
fun decode_arm_dec i n = decode_arm i (Arbnum.fromString n);
fun decode_arm_hex i n = decode_arm i (Arbnum.fromHexString n);

val encode_instruction = arm_to_num o term_to_arm;
val decode_instruction = arm_to_term o num_to_arm;
val decode_instruction_dec = decode_instruction o Arbnum.fromString;
val decode_instruction_hex = decode_instruction o Arbnum.fromHexString;

val mk_instruction = arm_to_term o string_to_arm;
fun dest_instruction i t = arm_to_string i false (term_to_arm t);

(* ------------------------------------------------------------------------- *)
