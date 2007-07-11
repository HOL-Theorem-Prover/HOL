(* interactive use:
  val _ = loadPath := !loadPath @
       ["/local/scratch/acjf3/hol98/tools/mlyacc/mlyacclib",
        "/local/scratch/acjf3/hol98/tools/mlton/pre",
        "/local/scratch/acjf3/hol98/src/portableML"];
  val _ = load "armParser.grm";
  val _ = load "armParser.lex";
  val _ = app load ["Arbnum", "Nonstdio", "Data"];
*)

structure assemblerML :> assemblerML =
struct

structure armLrVals =
    armLrValsFun(structure Token = LrParser.Token)

structure armLex =
    armLexFun(structure Tokens = armLrVals.Tokens)

structure armParser =
     Join(structure ParserData = armLrVals.ParserData
          structure Lex = armLex
          structure LrParser = LrParser)

open Data;

(* ------------------------------------------------------------------------- *)

fun mem i =
 let fun itr [] = false
       | itr (a::rst) = i=a orelse itr rst
 in itr end;

fun I x = x;

fun funpow n f x =
 let fun iter (0,res) = res
       | iter (n,res) = iter (n-1, f res)
 in if n<0 then x else iter(n,x)
 end;

fun fst (x,_) = x   and   snd (_,y) = y;

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

fun sign_extend l h n =
  let open Arbnum
      val ln = fromInt l
      val exp_l_sub1 = pow(two, ln - one)
      val exp_l = exp_l_sub1 * two
      val m = n mod exp_l
  in
    if mod2 (n div exp_l_sub1) = one then
      pow(two, fromInt h) - exp_l + m
    else
      m
  end;

(* ------------------------------------------------------------------------- *)

val int2register  = armLex.UserDeclarations.int2register;
val int2register_ = armLex.UserDeclarations.int2register_;

fun register2int r =
  case r of
    R0  => 0  | R1  => 1  | R2  => 2  | R3  => 3
  | R4  => 4  | R5  => 5  | R6  => 6  | R7  => 7
  | R8  => 8  | R9  => 9  | R10 => 10 | R11 => 11
  | R12 => 12 | R13 => 13 | R14 => 14 | R15 => 15;

fun register2int_ r =
  case r of
    R0_ => 0 | R1_ => 1 | R2_ => 2 | R3_ => 3
  | R4_ => 4 | R5_ => 5 | R6_ => 6 | R7_ => 7;

fun reg2string (NReg r) =
      let val n = register2int r in
        case n of
          13 => "sp"
        | 14 => "lr"
        | 15 => "pc"
        | _  => "r" ^ Int.toString n
      end
  | reg2string (VReg x) = x;

fun reg2string_ (NReg_ r) =
      let val n = register2int_ r in
        case n of
          13 => "sp"
        | 14 => "lr"
        | 15 => "pc"
        | _  => "r" ^ Int.toString n
      end
  | reg2string_ (VReg_ x) = x;

fun cp_reg2string (NReg r) = "c" ^ Int.toString (register2int r)
  | cp_reg2string (VReg x) = x;

fun cp_num2string n = "p" ^ Int.toString n;

fun opcode2string opc =
  case opc of
    AND => "and" | EOR => "eor" | SUB => "sub" | RSB => "rsb"
  | ADD => "add" | ADC => "adc" | SBC => "sbc" | RSC => "rsc"
  | TST => "tst" | TEQ => "teq" | CMP => "cmp" | CMN => "cmn"
  | ORR => "orr" | MOV => "mov" | BIC => "bic" | MVN => "mvn";

fun opcode2string2 opc =
  case opc of
    AND_  => "and" | EOR_ => "eor" | LSL_2 => "lsl" | LSR_2 => "lsr"
  | ASR_2 => "asr" | ADC_ => "adc" | SBC_  => "sbc" | ROR_  => "ror"
  | TST_  => "tst" | NEG_ => "neg" | CMP_2 => "cmp" | CMN_  => "cmn"
  | ORR_  => "orr" | MUL_ => "mul" | BIC_  => "bic" | MVN_  => "mvn";

fun opcode2string3 opc =
  case opc of
    STR_2 => "str" | STRH_2 => "strh" | STRB_2 => "strb" | LDRSB_ => "ldrsb"
  | LDR_2 => "ldr" | LDRH_2 => "ldrh" | LDRB_2 => "ldrb" | LDRSH_ => "ldrsh";

fun opcode2string4 opc =
  case opc of
    STR_1  => "str"  | LDR_1  => "ldr"
  | STRB_1 => "strb" | LDRB_1 => "ldrb"
  | STRH_1 => "strh" | LDRH_1 => "ldrh";

fun condition2string cond =
  case cond of
    EQ => "eq" | NE => "ne" | CS => "cs" | CC => "cc"
  | MI => "mi" | PL => "pl" | VS => "vs" | VC => "vc"
  | HI => "hi" | LS => "ls" | GE => "ge" | LT => "lt"
  | GT => "gt" | LE => "le" | AL => ""   | NV => "nv";

val list2register = NReg o int2register o list2int;
val list2register_ = NReg_ o int2register_ o list2int;

fun list2opcode l =
  case list2int l of
    0  => AND | 1  => EOR | 2  => SUB | 3  => RSB
  | 4  => ADD | 5  => ADC | 6  => SBC | 7  => RSC
  | 8  => TST | 9  => TEQ | 10 => CMP | 11 => CMN
  | 12 => ORR | 13 => MOV | 14 => BIC | 15 => MVN
  | _ =>  raise Parse "list2opcode: not an opcode list";

fun list2opcode2 l =
  case list2int l of
    0  => AND_  | 1  => EOR_ | 2  => LSL_2 | 3  => LSR_2
  | 4  => ASR_2 | 5  => ADC_ | 6  => SBC_  | 7  => ROR_
  | 8  => TST_  | 9  => NEG_ | 10 => CMP_2 | 11 => CMN_
  | 12 => ORR_  | 13 => MUL_ | 14 => BIC_  | 15 => MVN_
  | _ =>  raise Parse "list2opcode2: not an opcode list";

fun list2opcode3 l =
  case list2int l of
    0  => STR_2 | 1  => STRH_2 | 2  => STRB_2 | 3  => LDRSB_
  | 4  => LDR_2 | 5  => LDRH_2 | 6  => LDRB_2 | 7  => LDRSH_
  | _ =>  raise Parse "list2opcode3: not an opcode list";

fun list2condition l =
  case list2int l of
    0  => EQ | 1  => NE | 2  => CS | 3  => CC
  | 4  => MI | 5  => PL | 6  => VS | 7  => VC
  | 8  => HI | 9  => LS | 10 => GE | 11 => LT
  | 12 => GT | 13 => LE | 14 => AL | 15 => NV
  | _ =>  raise Parse "list2condition: not a condition code list";

fun list2shift l =
  case list2int l of
    0 => LSL | 1 => LSR | 2 => ASR | 3 => ROR
  | _ => raise Parse "list2shift: not a shift list";

(* ------------------------------------------------------------------------- *)

val Rn = list2register o bits 19 16;
val Rd = list2register o bits 15 12;
val Rs = list2register o bits 11 8;
val Rm = list2register o bits 3 0;

val r108 = list2register_ o bits 10 8;
val r86 = list2register_ o bits 8 6;
val r53 = list2register_ o bits 5 3;
val r20 = list2register_ o bits 2 0;

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

fun dec_bx l = Bx (Rm l);

fun dec_swi_ex l =
  Swi_ex (Arbnum.toInt (list2num (bits 23 0 l)));

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
  fun dec_addr_mode3 l =
    if bit 22 l then
      DthImmediate (list2int ((bits 11 8 l) @ (bits 3 0 l)))
    else
      DthRegister (Rm l)
in
  fun dec_ldrh_strh l = Ldrh_strh
    {P = bit 24 l, U = bit 23 l, W = bit 21 l, L = bit 20 l,
     S = bit 6 l, H = bit 5 l, Rn = Rn l, Rd = Rd l, offset = dec_addr_mode3 l}
end;

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
   CP = list2int (bits 11 8 l), Cop2 = list2int (bits 7 5 l), CRm = Rm l};

fun dec_mcr_mrc l = Mcr_mrc
  {Cop1 = list2int (bits 23 21 l), L = bit 20 l, Rd = Rd l, CRn = Rn l,
   CP = list2int (bits 11 8 l), CRm = Rm l, Cop2 = list2int (bits 7 5 l)};

fun dec_ldc_stc l = Ldc_stc
  {P = bit 24 l, U = bit 23 l, N = bit 22 l, W = bit 21 l, L = bit 20 l,
   CRd = Rd l, Rn = Rn l, CP = list2int (bits 11 8 l),
   offset = list2int (bits 7 0 l)};

(* ------------------------------------------------------------------------- *)

fun decode_inst l =
  case rev (map (fn x => if x then 1 else 0) l) of
    [0,0,0,1,0,_,0,0,1,1,1,1,_,_,_,_,_,0,0,0,0,0,0,0,0,0,0,0] => dec_mrs l
  | [0,0,0,1,0,_,1,0,_,_,_,_,1,1,1,1,0,0,0,0,0,0,0,0,_,_,_,_] => dec_msr l
  | [0,0,0,1,0,0,1,0,_,_,_,_,_,_,_,_,_,_,_,_,0,0,0,1,_,_,_,_] => dec_bx l
  | [0,0,0,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,0,_,_,_,_] => dec_data_proc l
  | [0,0,0,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,0,_,_,1,_,_,_,_] => dec_data_proc l
  | [0,0,0,0,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,1,0,0,1,_,_,_,_] => dec_mla_mul l
  | [0,0,0,1,0,_,0,0,_,_,_,_,_,_,_,_,0,0,0,0,1,0,0,1,_,_,_,_] => dec_swp l
  | [0,0,0,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,1,0,1,1,_,_,_,_] => dec_ldrh_strh l
  | [0,0,0,_,_,_,_,1,_,_,_,_,_,_,_,_,_,_,_,_,1,1,_,1,_,_,_,_] => dec_ldrh_strh l
  | [0,0,1,1,0,_,0,0,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] => Undef
  | [0,0,1,1,0,_,1,0,_,_,_,_,1,1,1,1,_,_,_,_,_,_,_,_,_,_,_,_] => dec_msr l
  | [0,0,1,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] => dec_data_proc l
  | [0,1,0,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] => dec_ldr_str l
  | [0,1,1,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,0,_,_,_,_] => dec_ldr_str l
  | [1,0,0,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] => dec_ldm_stm l
  | [1,0,1,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] => dec_br l
  | [1,1,0,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] => dec_ldc_stc l
  | [1,1,1,0,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,0,_,_,_,_] => dec_cdp l
  | [1,1,1,0,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,1,_,_,_,_] => dec_mcr_mrc l
  | [1,1,1,1,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] => dec_swi_ex l
  | _ => Undef;

fun decode_thumb l =
  case rev (map (fn x => if x then 1 else 0) (bits 15 8 l)) of
    [0,0,0,0,0,_,_,_] => LSL_1
                         {Rd = r20 l, Rm = r53 l, imm = list2int (bits 10 6 l)}
  | [0,0,0,0,1,_,_,_] => LSR_1
                         {Rd = r20 l, Rm = r53 l, imm = list2int (bits 10 6 l)}
  | [0,0,0,1,0,_,_,_] => ASR_1
                         {Rd = r20 l, Rm = r53 l, imm = list2int (bits 10 6 l)}
  | [0,0,0,1,1,0,0,_] => ADD_3 {Rd = r20 l, Rn = r53 l, Rm = r86 l}
  | [0,0,0,1,1,0,1,_] => SUB_3 {Rd = r20 l, Rn = r53 l, Rm = r86 l}
  | [0,0,0,1,1,1,0,_] => ADD_1 {Rd = r20 l, Rn = r53 l,
                                imm = list2int (bits 8 6 l)}
  | [0,0,0,1,1,1,1,_] => SUB_1 {Rd = r20 l, Rn = r53 l,
                                imm = list2int (bits 8 6 l)}
  | [0,0,1,0,0,_,_,_] => MOV_1 {Rd = r108 l, imm = list2int (bits 7 0 l)}
  | [0,0,1,0,1,_,_,_] => CMP_1 {Rn = r108 l, imm = list2int (bits 7 0 l)}
  | [0,0,1,1,0,_,_,_] => ADD_2 {Rd = r108 l, imm = list2int (bits 7 0 l)}
  | [0,0,1,1,1,_,_,_] => SUB_2 {Rd = r108 l, imm = list2int (bits 7 0 l)}
  | [0,1,0,0,0,0,_,_] => DP_ {opc = list2opcode2 (bits 9 6 l),
                              Rd = r20 l, Rm = r53 l}
  | [0,1,0,0,0,1,0,0] => ADD_4 {Rd = list2register (bits 2 0 l @ bits 7 7 l),
                                Rm = list2register (bits 6 3 l)}
  | [0,1,0,0,0,1,0,1] => CMP_3 {Rd = list2register (bits 2 0 l @ bits 7 7 l),
                                Rm = list2register (bits 6 3 l)}
  | [0,1,0,0,0,1,1,0] => MOV_3 {Rd = list2register (bits 2 0 l @ bits 7 7 l),
                                Rm = list2register (bits 6 3 l)}
  | [0,1,0,0,0,1,1,1] => if bit 7 l then UND_ else
                           BX_ (list2register (bits 6 3 l))
  | [0,1,0,0,1,_,_,_] => LDR_3 {Rd = r108 l, imm = list2int (bits 7 0 l)}
  | [0,1,0,1,_,_,_,_] => DT_ {opc = list2opcode3 (bits 11 9 l),
                              Rd = r20 l, Rn = r53 l, Rm = r86 l}
  | [0,1,1,0,0,_,_,_] => DT_imm {opc = STR_1, Rd = r20 l, Rn = r53 l,
                                 imm = list2int (bits 10 6 l)}
  | [0,1,1,0,1,_,_,_] => DT_imm {opc = LDR_1, Rd = r20 l, Rn = r53 l,
                                 imm = list2int (bits 10 6 l)}
  | [0,1,1,1,0,_,_,_] => DT_imm {opc = STRB_1, Rd = r20 l, Rn = r53 l,
                                 imm = list2int (bits 10 6 l)}
  | [0,1,1,1,1,_,_,_] => DT_imm {opc = LDRB_1, Rd = r20 l, Rn = r53 l,
                                 imm = list2int (bits 10 6 l)}
  | [1,0,0,0,0,_,_,_] => DT_imm {opc = STRH_1, Rd = r20 l, Rn = r53 l,
                                 imm = list2int (bits 10 6 l)}
  | [1,0,0,0,1,_,_,_] => DT_imm {opc = LDRH_1, Rd = r20 l, Rn = r53 l,
                                 imm = list2int (bits 10 6 l)}
  | [1,0,0,1,0,_,_,_] => STR_3 {Rd = r108 l, imm = list2int (bits 7 0 l)}
  | [1,0,0,1,1,_,_,_] => LDR_4 {Rd = r108 l, imm = list2int (bits 7 0 l)}
  | [1,0,1,0,0,_,_,_] => ADD_5 {Rd = r108 l, imm = list2int (bits 7 0 l)}
  | [1,0,1,0,1,_,_,_] => ADD_6 {Rd = r108 l, imm = list2int (bits 7 0 l)}
  | [1,0,1,1,0,0,0,0] => (if bit 7 l then SUB_4 else ADD_7)
                         (list2int (bits 6 0 l))
  | [1,0,1,1,0,1,0,r] => PUSH {R = r = 1, list = list2int (bits 7 0 l)}
  | [1,0,1,1,1,1,0,r] => POP  {R = r = 1, list = list2int (bits 7 0 l)}
  | [1,0,1,1,1,1,1,0] => UND_
  | [1,1,0,0,0,_,_,_] => STMIA_ {Rn = r108 l, list = list2int (bits 7 0 l)}
  | [1,1,0,0,1,_,_,_] => LDMIA_ {Rn = r108 l, list = list2int (bits 7 0 l)}
  | [1,1,0,1,1,1,1,0] => UND_
  | [1,1,0,1,1,1,1,1] => SWI_ (list2int (bits 7 0 l))
  | [1,1,0,1,_,_,_,_] => B_1 {cond = list2condition (bits 11 8 l),
                              imm = list2int (bits 10 0 l)}
  | [1,1,1,1,0,_,_,_] => BL_a (list2int (bits 10 0 l))
  | [1,1,1,1,1,_,_,_] => BL_b (list2int (bits 10 0 l))
  | _ => UND_;

(* ------------------------------------------------------------------------- *)

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

fun num_to_thumb n =
let val l = num2list 16 n
    val i = decode_thumb l
in
  case i of
    UND_ => if n = Arbnum.fromHexString "DE00" then
              Thumb UND_
            else
              ThumbData n
  | _ => Thumb i
end;

(* ------------------------------------------------------------------------- *)

local open Arbnum
  val max = pow(two, fromInt 32)
in
  fun num1comp n = (max - one) - n mod max
  fun num2comp n = (max - n mod max) mod max
  fun add32 a b = (a + b) mod max
end;

local
  fun num2imm(x,n) =
  let val x8 = Arbnum.mod(x,Arbnum.fromInt 256) in
    if x8 = x then
      (Arbnum.fromInt n, x8)
    else
      if n < 15 then
        num2imm(rol32 x 2, n + 1)
      else
        raise Parse
          "num2immediate: number cannot be represented as an immediate"
  end
in
  fun num2immediate n = num2imm(n, 0)
end;

fun ipow2 x = Word.toInt (Word.<<(Word.fromInt 1,Word.fromInt x));

local
  fun log2 x = Real.floor (Math.ln (Real.fromInt x) / Math.ln 2.0)
  fun int_len x = if x = 0 then 1 else log2 x + 1
in
fun validate_thumb x =
 let val y =
    case x of
      LSL_1  y => if int_len (#imm y) < 6 then NONE else SOME ("LSL", 5)
    | LSR_1  y => if int_len (#imm y) < 6 then NONE else SOME ("LSR", 5)
    | ASR_1  y => if int_len (#imm y) < 6 then NONE else SOME ("ASR", 5)
    | ADD_3  y => NONE
    | SUB_3  y => NONE
    | ADD_1  y => if int_len (#imm y) < 4 then NONE else SOME ("ADD", 3)
    | SUB_1  y => if int_len (#imm y) < 4 then NONE else SOME ("SUB", 3)
    | MOV_1  y => if int_len (#imm y) < 9 then NONE else SOME ("MOV", 8)
    | CMP_1  y => if int_len (#imm y) < 9 then NONE else SOME ("CMP", 8)
    | ADD_2  y => if int_len (#imm y) < 9 then NONE else SOME ("ADD", 8)
    | SUB_2  y => if int_len (#imm y) < 9 then NONE else SOME ("SUB", 8)
    | DP_    y => NONE
    | ADD_4  y => NONE
    | CMP_3  y => NONE
    | MOV_3  y => NONE
    | BX_    y => NONE
    | LDR_3  y => if int_len (#imm y) < 9 then NONE else SOME ("LDR", 8)
    | DT_    y => NONE
    | DT_imm y => if int_len (#imm y) < 6 then NONE else
                    SOME (opcode2string4 (#opc y), 5)
    | STR_3  y => if int_len (#imm y) < 9 then NONE else SOME ("STR", 8)
    | LDR_4  y => if int_len (#imm y) < 9 then NONE else SOME ("LDR", 8)
    | ADD_5  y => if int_len (#imm y) < 9 then NONE else SOME ("ADD", 8)
    | ADD_6  y => if int_len (#imm y) < 9 then NONE else SOME ("ADD", 8)
    | ADD_7  y => if int_len y < 8 then NONE else SOME ("ADD", 7)
    | SUB_4  y => if int_len y < 8 then NONE else SOME ("SUB", 7)
    | PUSH   y => if int_len (#list y) < 9 then NONE else SOME ("PUSH", 8)
    | POP    y => if int_len (#list y) < 9 then NONE else SOME ("POP", 8)
    | LDMIA_ y => if int_len (#list y) < 9 then NONE else SOME ("LDMIA", 8)
    | STMIA_ y => if int_len (#list y) < 9 then NONE else SOME ("STMIA", 8)
    | B_1    y => if int_len (#imm y) < 9 then NONE else SOME ("B", 8)
    | UND_     => NONE
    | SWI_   y => if int_len y < 9 then NONE else SOME ("SWI", 8)
    | B_2    y => if int_len y < 12 then NONE else SOME ("B", 11)
    | BL_    y => if int_len y < 23 then NONE else SOME ("BL", 22)
    | BL_a   y => if int_len y < 12 then NONE else SOME ("BL", 11)
    | BL_b   y => if int_len y < 12 then NONE else SOME ("BL", 11)
  in
    case y of
      NONE => x
    | SOME (s, n) => raise BadInstruction
        (s ^ " immediate too large: must be " ^ Int.toString n ^ "-bit word")
  end
end;

local
  val n24 = ipow2 24
in
  fun validate_instruction (Data n) = Data n
    | validate_instruction (ThumbData n) = ThumbData n
    | validate_instruction (Thumb i) = Thumb (validate_thumb i)
    | validate_instruction (ic as Instruction(i,c)) =
    case i of
      Br x => if #offset x <= n24 then ic else
                raise BadInstruction "Branch offset too large"
    | Data_proc x =>
       (case #op2 x of
          DpImmediate n =>
           (let val _ = num2immediate n in ic end handle _ =>
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
              end handle _ => raise BadInstruction
                    "Cannot represent the immediate value")
        | DpShiftImmediate y => if #Imm y < 32 then ic else
            raise BadInstruction "Immediate shift value too large"
        | DpShiftRegister y => ic)
    | Ldrh_strh x =>
       (case #offset x of
          DthImmediate n => if n < ipow2 8 then ic else
            raise BadInstruction "Offset too large"
        | _ => ic)
    | Ldr_str x =>
       (case #offset x of
          DtImmediate n => if n < ipow2 12 then ic else
            raise BadInstruction "Offset too large"
        | DtShiftImmediate y => if #Imm y < 32 then ic else
            raise BadInstruction "Immediate shift value too large")
    | Ldm_stm x => if #list x < ipow2 16 then ic else
                     raise BadInstruction "Block transfer list too long"
    | Msr x =>
       (case #Op x of
          MsrImmediate n =>
            (let val _ = num2immediate n in ic end handle _ =>
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

  fun compute_offset align sz line address =
    let open Arbnum
        val na = fromInt align
        val na2 = fromInt (Int.*(2, align))
        val exp_sz = fromInt (ipow2 sz)
        val jmp = add32 address (num2comp (line + na2))
        val offset = (jmp div na) mod exp_sz
    in
      if address = add32 (line + na2) (sign_extend sz 32 offset * na) then
        toInt offset
      else
        raise Data.Parse "Invalid branch instruction"
    end;

  fun branch_to_arm (c,link,address) line =
    let val offset = compute_offset 4 24 line address in
      Instruction(Br {L = link, offset = offset},c)
    end;

  fun branch_to_thumb (c,link,address) line =
    if link then
      Thumb (BL_ (compute_offset 2 22 line address))
    else
      if c = AL then
        Thumb (B_2 (compute_offset 2 11 line address))
      else
        Thumb (B_1 {cond = c, imm = compute_offset 2 8 line address})

  fun assembler_to_instruction a =
    case a of
      [Code c] => c
    | [Mark line,BranchN (c,link,address)] =>
         branch_to_arm (c,link,address) line
    | [Mark line,ThumbBranchN (c,link,address)] =>
         branch_to_thumb (c,link,address) line
    | [BranchN (c,link,address)] =>
         branch_to_arm (c,link,address) Arbnum.zero
    | [ThumbBranchN (c,link,address)] =>
         branch_to_thumb (c,link,address) Arbnum.zero
    | [Label s, BranchS (c,link,l)] =>
         if s = l then
           Instruction(Br {L = link,
             offset = Arbnum.toInt (Arbnum.fromHexString "FFFFFE")},c)
         else
           raise Data.Parse "Not an instruction"
    | [Label s, ThumbBranchS (c,link,l)] =>
         if s = l then
           if link then
             Thumb(BL_ (Arbnum.toInt (Arbnum.fromHexString "3FFFFE")))
           else
             if c = AL then
               Thumb (B_2 (Arbnum.toInt (Arbnum.fromHexString "7FE")))
             else
               Thumb (B_1 {cond = c,
                           imm = Arbnum.toInt (Arbnum.fromHexString "FE")})
         else
           raise Data.Parse "Not an instruction"
    | _ => raise Data.Parse "Not an instruction";
end;

fun invoke lexstream = let
  fun print_error (s,i:int,_) =
      TextIO.output(TextIO.stdErr, Int.toString i ^ ": " ^ s ^ "\n")
in
  #1 (armParser.parse(0,lexstream,print_error,()))
end;

fun string_to_code s = let
  val done = ref false
  val lexer = armParser.makeLexer
        (fn _ => if !done then "" else (s before done := true))
  val _ = armLex.UserDeclarations.pos := 1
in
  invoke lexer
end;

fun string_to_arm s =
  (validate_instruction o assembler_to_instruction o string_to_code) s;

fun read_stream strm = let
  val lexer = armParser.makeLexer (fn _ => TextIO.inputLine strm)
  val _ = armLex.UserDeclarations.pos := 1
in
  invoke lexer before TextIO.closeIn strm
end;

fun parse_arm fname = read_stream (TextIO.openIn fname);

(* ------------------------------------------------------------------------- *)

infix 9 <<;

fun op << (x,y) = let open Arbnum in
  x * pow(two, fromInt y)
end;

fun ibits h l n =
  let val x = ipow2 l
      val y = ipow2 (h + 1 - l)
  in
    Arbnum.fromInt ((n div x) mod y)
  end;

fun register_to_num (NReg n) = Arbnum.fromInt (register2int n)
  | register_to_num (VReg x) = raise Parse
      "register_to_num: register is a variable";

fun register_to_num_ (NReg_ n) = Arbnum.fromInt (register2int_ n)
  | register_to_num_ (VReg_ x) = raise Parse
      "register_to_num_: thumb register is a variable";

fun condition_to_num cond = Arbnum.fromInt
 (case cond of
    EQ => 0  | NE => 1  | CS => 2  | CC => 3
  | MI => 4  | PL => 5  | VS => 6  | VC => 7
  | HI => 8  | LS => 9  | GE => 10 | LT => 11
  | GT => 12 | LE => 13 | AL => 14 | NV => 15);

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

fun addr_mode3_to_num x = let open Arbnum
in
  case x of
    DthImmediate n => fromHexString "400000" +
                      ((ibits 7 4 n) << 8) + (ibits 3 0 n)
  | DthRegister r => register_to_num r
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

fun options2_to_num (l,p,u,w,s,h) =
let open Arbnum
in
  sbit p 24 + sbit u 23 + sbit w 21 +
  (if l then
     sbit true 20 + sbit s 6 + sbit h 5
   else
     sbit true 5)
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

fun opcode2_to_num opc =
  Arbnum.fromHexString
  (case opc of
     AND_  => "4000" | EOR_ => "4040" | LSL_2 => "4080" | LSR_2 => "40C0"
   | ASR_2 => "4100" | ADC_ => "4140" | SBC_  => "4180" | ROR_  => "41C0"
   | TST_  => "4200" | NEG_ => "4240" | CMP_2 => "4280" | CMN_  => "42C0"
   | ORR_  => "4300" | MUL_ => "4340" | BIC_  => "4380" | MVN_  => "43C0");

fun opcode3_to_num opc =
  Arbnum.fromHexString
  (case opc of
     STR_2 => "5000" | STRH_2 => "5200" | STRB_2 => "5400" | LDRSB_ => "5600"
   | LDR_2 => "5800" | LDRH_2 => "5A00" | LDRB_2 => "5C00" | LDRSH_ => "5E00");

fun opcode4_to_num opc =
  Arbnum.fromHexString
  (case opc of
     STR_1  => "6000" | LDR_1  => "6800"
   | STRB_1 => "7000" | LDRB_1 => "7800"
   | STRH_1 => "8000" | LDRH_1 => "8800");

fun thumb_to_num x = let open Arbnum in
  case x of
    LSL_1  y => fromInt (#imm y) << 6 +
                register_to_num_ (#Rm y) << 3 + register_to_num_ (#Rd y)
  | LSR_1  y => fromHexString "0800" + fromInt (#imm y) << 6 +
                register_to_num_ (#Rm y) << 3 + register_to_num_ (#Rd y)
  | ASR_1  y => fromHexString "1000" + fromInt (#imm y) << 6 +
                register_to_num_ (#Rm y) << 3 + register_to_num_ (#Rd y)
  | ADD_3  y => fromHexString "1800" + register_to_num_ (#Rm y) << 6 +
                register_to_num_ (#Rn y) << 3 + register_to_num_ (#Rd y)
  | SUB_3  y => fromHexString "1A00" + register_to_num_ (#Rm y) << 6 +
                register_to_num_ (#Rn y) << 3 + register_to_num_ (#Rd y)
  | ADD_1  y => fromHexString "1C00" + fromInt (#imm y) << 6 +
                register_to_num_ (#Rn y) << 3 + register_to_num_ (#Rd y)
  | SUB_1  y => fromHexString "1E00" + fromInt (#imm y) << 6 +
                register_to_num_ (#Rn y) << 3 + register_to_num_ (#Rd y)
  | MOV_1  y => fromHexString "2000" + register_to_num_ (#Rd y) << 8 +
                fromInt (#imm y)
  | CMP_1  y => fromHexString "2800" + register_to_num_ (#Rn y) << 8 +
                fromInt (#imm y)
  | ADD_2  y => fromHexString "3000" + register_to_num_ (#Rd y) << 8 +
                fromInt (#imm y)
  | SUB_2  y => fromHexString "3800" + register_to_num_ (#Rd y) << 8 +
                fromInt (#imm y)
  | DP_    y => opcode2_to_num (#opc y) + register_to_num_ (#Rm y) << 3 +
                register_to_num_ (#Rd y)
  | ADD_4  y => let val H1Rd = toInt (register_to_num (#Rd y)) in
                  fromHexString "4400" + ibits 3 3 H1Rd << 7 +
                  register_to_num (#Rm y) << 3 + ibits 2 0 H1Rd
                end
  | CMP_3  y => let val H1Rd = toInt (register_to_num (#Rd y)) in
                  fromHexString "4500" + ibits 3 3 H1Rd << 7 +
                  register_to_num (#Rm y) << 3 + ibits 2 0 H1Rd
                end
  | MOV_3  y => let val H1Rd = toInt (register_to_num (#Rd y)) in
                  fromHexString "4600" + ibits 3 3 H1Rd << 7 +
                  register_to_num (#Rm y) << 3 + ibits 2 0 H1Rd
                end
  | BX_    y => fromHexString "4700" + register_to_num y << 3
  | LDR_3  y => fromHexString "4800" + register_to_num_ (#Rd y) << 8 +
                fromInt (#imm y)
  | DT_    y => opcode3_to_num (#opc y) + register_to_num_ (#Rm y) << 6 +
                register_to_num_ (#Rn y) << 3 + register_to_num_ (#Rd y)
  | DT_imm y => opcode4_to_num (#opc y) + fromInt (#imm y) << 6 +
                register_to_num_ (#Rn y) << 3 + register_to_num_ (#Rd y)
  | STR_3  y => fromHexString "9000" + register_to_num_ (#Rd y) << 8 +
                fromInt (#imm y)
  | LDR_4  y => fromHexString "9800" + register_to_num_ (#Rd y) << 8 +
                fromInt (#imm y)
  | ADD_5  y => fromHexString "A000" + register_to_num_ (#Rd y) << 8 +
                fromInt (#imm y)
  | ADD_6  y => fromHexString "A800" + register_to_num_ (#Rd y) << 8 +
                fromInt (#imm y)
  | ADD_7  y => fromHexString "B000" + fromInt y
  | SUB_4  y => fromHexString "B080" + fromInt y
  | PUSH   y => fromHexString (if #R y then "B500" else "B400") +
                fromInt (#list y)
  | POP    y => fromHexString (if #R y then "BD00" else "BC00") +
                fromInt (#list y)
  | STMIA_ y => fromHexString "C000" + register_to_num_ (#Rn y) << 8 +
                fromInt (#list y)
  | LDMIA_ y => fromHexString "C800" + register_to_num_ (#Rn y) << 8 +
                fromInt (#list y)
  | B_1    y => fromHexString "D000" + condition_to_num (#cond y) << 8 +
                fromInt (#imm y)
  | UND_     => fromHexString "DE00"
  | SWI_   y => fromHexString "DF00" + fromInt y
  | B_2    y => fromHexString "E000" + fromInt y
  | BL_    y => (fromHexString "F800" + ibits 10 0 y) << 16 +
                 fromHexString "F000" + ibits 21 11 y
  | BL_a   y => fromHexString "F000" + fromInt y
  | BL_b   y => fromHexString "F800" + fromInt y
end;

fun arm_to_num (Data n) = n
  | arm_to_num (ThumbData n) = n
  | arm_to_num (Thumb x) = thumb_to_num x
  | arm_to_num (Instruction(x,c)) =
let open Arbnum
in
  condition_to_num c << 28 +
  (case x of
     Br y =>
       fromHexString (if #L y then "B000000" else "A000000") +
       fromInt (#offset y)
   | Bx y => fromHexString "1200010" + register_to_num y
   | Swi_ex y =>
       fromHexString "F000000" + fromInt y
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
       register_to_num (#Rd y) << 16 + register_to_num (#Rn y) << 12 +
       register_to_num (#Rs y) << 8 + register_to_num (#Rm y)
   | Ldrh_strh y =>
       fromHexString "90" +
       options2_to_num (#L y, #P y, #U y, #W y, #S y, #H y) +
       register_to_num (#Rn y) << 16 + register_to_num (#Rd y) << 12 +
       addr_mode3_to_num (#offset y)
   | Ldr_str y =>
       fromHexString "4000000" + (sbit (#L y) 20) +
       options_to_num (#P y, #U y, #B y, #W y) +
       register_to_num (#Rn y) << 16 + register_to_num (#Rd y) << 12 +
       addr_mode2_to_num (#offset y)
   | Ldm_stm y =>
       fromHexString "8000000" + (sbit (#L y) 20) +
       options_to_num (#P y, #U y, #S y, #W y) +
       register_to_num (#Rn y) << 16 + fromInt (#list y)
   | Swp y =>
       fromHexString "1000090" + (sbit (#B y) 22) +
       register_to_num (#Rn y) << 16 + register_to_num (#Rd y) << 12 +
       register_to_num (#Rm y)
   | Mrs y =>
       fromHexString "10F0000" + (sbit (#R y) 22) +
       register_to_num (#Rd y) << 12
   | Msr y =>
       fromHexString "120F000" + msr_psr_to_num (#R y, #bit19 y, #bit16 y) +
       msr_mode_to_num (#Op y)
   | Cdp y =>
       fromHexString "E000000" + fromInt (#Cop1 y) << 20 +
       register_to_num (#CRn y) << 16 + register_to_num (#CRd y) << 12 +
       fromInt (#CP y) << 8 + fromInt (#Cop2 y) << 5 + register_to_num (#CRm y)
   | Ldc_stc y =>
       fromHexString "C000000" + (sbit (#L y) 20) +
       options_to_num (#P y, #U y, #N y, #W y) +
       register_to_num (#Rn y) << 16 + register_to_num (#CRd y) << 12 +
       fromInt (#CP y) << 8 + fromInt (#offset y)
   | Mcr_mrc y =>
       fromHexString "E000010" + (sbit (#L y) 20) + fromInt (#Cop1 y) << 21 +
       register_to_num (#CRn y) << 16 + register_to_num (#Rd y) << 12 +
       fromInt (#CP y) << 8 + fromInt (#Cop2 y) << 5 + register_to_num (#CRm y)
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

fun shift_immediate2string (y:{Imm : int, Rm : vregister, Sh : shift}) =
  reg2string (#Rm y) ^
    (if #Imm y = 0 then toUpperString(
       case #Sh y of
         LSL => ""
       | LSR => ", lsr #32"
       | ASR => ", asr #32"
       | ROR => ", rrx")
     else
       ", " ^ shift2string (#Sh y) ^ " #" ^ Int.toString (#Imm y));

(* ------------------------------------------------------------------------- *)

local
  val n26 = ipow2 26
  fun offset2comp i = Int.mod(n26 - i,n26)
  fun abs_offset_string i j = let open Arbnum
            val x = sign_extend 24 32 (fromInt j)
        in
          "0x" ^ toHexString(add32 (i + fromInt 8) (x * fromInt 4))
        end;
  fun rel_offset_string i =
      let val j = Int.mod((i + 2) * 4,n26) in
        if j < n26 div 2 then
          Int.toString j
        else
          "-" ^ Int.toString (offset2comp j)
      end
  val err = Parse "br_to_string: not a branch instruction"
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
    | branch_to_string (ThumbBranchS(c,l,d)) =
        mnemonic false
          ("code16 b" ^ (if l then "l" else condition2string c)) ^ d
    | branch_to_string (BranchN(c,l,n)) =
        mnemonic false ("b" ^ (if l then "l" else "") ^ condition2string c) ^
          "0x" ^ Arbnum.toHexString n
    | branch_to_string (ThumbBranchN(c,l,n)) =
        mnemonic false ("code16 b" ^ (if l then "l" else condition2string c)) ^
          "0x" ^ Arbnum.toHexString n
    | branch_to_string _ = raise err
end;

local
  val err = Parse "bx_to_string: not a branch exchange instruction"
in
  fun bx_to_string a (Instruction(x,c)) =
   (case x of
      Bx y => (mnemonic a ("bx" ^ condition2string c)) ^ reg2string y
    | _ => raise err)
   | bx_to_string _ _ = raise err
end;

local
  val err = Parse "swi_ex_to_string: not a software interrupt instruction"
in
  fun swi_ex_to_string a (Instruction(x,c)) =
   (case x of
      Swi_ex y => (mnemonic a ("swi" ^ condition2string c)) ^ Int.toString y
    | _ => raise err)
   | swi_ex_to_string _ _ = raise err
end;

local
  fun addr_mode2string x =
    case x of
      DpImmediate n => "#" ^ Arbnum.toString n
    | DpShiftImmediate i => shift_immediate2string i
    | DpShiftRegister r =>
        reg2string (#Rm r) ^ ", " ^ shift2string (#Sh r) ^ " " ^
        reg2string (#Rs r)
  val err = Parse "data_proc_to_string: not a data processing instruction"
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
  val err = Parse "mla_mul_to_string: not a multiply instruction"
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
          ", #" ^ (if U then "" else "-") ^ Int.toString n
    | DtShiftImmediate i =>
        ", " ^ (if U then "" else "-") ^ shift_immediate2string i
  val err = Parse "ldr_str_to_string: not a load/store instruction"
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
  fun addr_mode3string U x =
    case x of
      DthImmediate n =>
        if n = 0 then "" else
          ", #" ^ (if U then "" else "-") ^ Int.toString n
    | DthRegister r => ", " ^ (if U then "" else "-") ^ reg2string r
  fun format_suffix (l,s,h) =
        case (l,s,h) of
          (true,false,_)    => "h"
        | (true,true,false) => "sb"
        | (true,true,true)  => "sh"
        | (false,_,_)       => "h"
  val err = Parse "ldrh_strh_to_string: not a load/store (half) instruction"
in
  fun ldrh_strh_to_string a (Instruction(x,c)) =
   (case x of
      Ldrh_strh y =>
        let val h = mnemonic a ((if #L y then "ldr" else "str") ^
                      condition2string c ^ (format_suffix (#L y, #S y, #H y)))
            val offset = addr_mode3string (#U y) (#offset y)
        in
          h ^ reg2string (#Rd y) ^ ", [" ^ reg2string (#Rn y) ^
          (if #P y then
             offset ^ "]" ^ (if #W y then "!" else "")
           else
             "]" ^ offset)
        end
    | _ => raise err)
   | ldrh_strh_to_string _ _ = raise err
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

  fun regn2string n = "r" ^ Int.toString n;

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
in
  fun reg_list2string l = blocks2string (make_blocks (
        List.take(num2list 16 (Arbnum.fromInt l),16))) "{"
end;

local
  fun mode2string p u =
    case (p,u) of
      (false,false) => "da"
    | (false,true)  => "ia"
    | (true,false)  => "db"
    | (true,true)   => "ib";
  val err = Parse "ldm_stm_to_string: not a block transfer instruction"
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
  | _ => raise Parse "swp_to_string: not a swap instruction")
 | swp_to_string _ _ = raise Parse "swp_to_string: not a swap instruction";

fun mrs_to_string a (Instruction(x,c)) =
 (case x of
    Mrs y =>
      let val h = mnemonic a ("mrs" ^ condition2string c)
      in
        h ^ reg2string (#Rd y) ^ ", " ^ (if #R y then "SPSR" else "CPSR")
      end
  | _ => raise Parse "mrs_to_string: not an mrs instruction")
 | mrs_to_string _ _ = raise Parse "mrs_to_string: not an mrs instruction";

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
  | _ => raise Parse "msr_to_string: not an msr instruction")
 | msr_to_string _ _ = raise Parse "msr_to_string: not an msr instruction";

fun cdp_to_string a (Instruction(x,c)) =
 (case x of
    Cdp y =>
      let val h = mnemonic a ("cdp" ^ condition2string c)
      in
        h ^ cp_num2string (#CP y) ^ ", " ^ Int.toString (#Cop1 y) ^ ", " ^
        cp_reg2string (#CRd y) ^ ", " ^ cp_reg2string (#CRn y) ^ ", " ^
        cp_reg2string (#CRm y) ^
        (if #Cop2 y = 0 then "" else ", " ^ Int.toString (#Cop2 y))
      end
  | _ => raise Parse "cdp_to_string: not a cdp instruction")
 | cdp_to_string _ _ = raise Parse "cdp_to_string: not a cdp instruction";

local
  val err = Parse "mcr_mrc_to_string: not an mcr or mrc instruction"
in
  fun mcr_mrc_to_string a (Instruction(x,c)) =
   (case x of
      Mcr_mrc y =>
        let val h = mnemonic a ((if #L y then "mrc" else "mcr") ^
                      condition2string c)
        in
          h ^ cp_num2string (#CP y) ^ ", " ^ Int.toString (#Cop1 y) ^ ", " ^
          reg2string (#Rd y) ^ ", " ^ cp_reg2string (#CRn y) ^ ", " ^
          cp_reg2string (#CRm y) ^
          (if # Cop2 y = 0 then "" else ", " ^ Int.toString (#Cop2 y))
        end
    | _ => raise err)
   | mcr_mrc_to_string _ _ = raise err
end;

local
  val err = Parse "ldc_stc_to_string: not an ldc or stc instruction"
in
  fun ldc_stc_to_string a (Instruction(x,c)) =
   (case x of
      Ldc_stc y =>
        let val h = mnemonic a ((if #L y then "ldc" else "stc") ^
                      condition2string c)
            val offset = if #offset y = 0 then "" else
                  (if #U y then ", #" else ", #-") ^
                     Int.toString (4 * #offset y)
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

fun align_opcode4 opc =
  case opc of
    STR_1  => 4 | LDR_1  => 4
  | STRB_1 => 1 | LDRB_1 => 1
  | STRH_1 => 2 | LDRH_1 => 2;

local
  fun offset2comp n i = Int.mod(n - i,n)
  fun abs_offset_string sz n i = let open Arbnum
            val x = sign_extend sz 32 (fromInt i)
        in
          "0x" ^ toHexString(add32 (n + fromInt 4) (x * fromInt 2))
        end;
  fun rel_offset_string n i =
      let val j = Int.mod((i + 1) * 2,n) in
        if j < n div 2 then
          Int.toString j
        else
          "-" ^ Int.toString (offset2comp n j)
      end
in
  fun thumb_target sz l i = 
    case l of
      SOME n => abs_offset_string sz n i
    | NONE   => rel_offset_string (ipow2 (sz + 1)) i ^ "; relative"
end;

fun thumb_to_string l a x =
  case x of
    LSL_1  y => mnemonic a "lsl" ^ reg2string_ (#Rd y) ^ ", " ^
                reg2string_ (#Rm y) ^ ", #" ^ Int.toString (#imm y)
  | LSR_1  y => mnemonic a "lsr" ^ reg2string_ (#Rd y) ^ ", " ^
                reg2string_ (#Rm y) ^ ", #" ^ Int.toString (#imm y)
  | ASR_1  y => mnemonic a "asr" ^ reg2string_ (#Rd y) ^ ", " ^
                reg2string_ (#Rm y) ^ ", #" ^ Int.toString (#imm y)
  | ADD_3  y => mnemonic a "add" ^ reg2string_ (#Rd y) ^ ", " ^
                reg2string_ (#Rn y) ^ ", " ^ reg2string_ (#Rm y)
  | SUB_3  y => mnemonic a "sub" ^ reg2string_ (#Rd y) ^ ", " ^
                reg2string_ (#Rn y) ^ ", " ^ reg2string_ (#Rm y)
  | ADD_1  y => mnemonic a "add" ^ reg2string_ (#Rd y) ^ ", " ^
                reg2string_ (#Rn y) ^ ", #" ^ Int.toString (#imm y)
  | SUB_1  y => mnemonic a "sub" ^ reg2string_ (#Rd y) ^ ", " ^
                reg2string_ (#Rn y) ^ ", #" ^ Int.toString (#imm y)
  | MOV_1  y => mnemonic a "mov" ^ reg2string_ (#Rd y) ^ ", #" ^
                Int.toString (#imm y)
  | CMP_1  y => mnemonic a "cmp" ^ reg2string_ (#Rn y) ^ ", #" ^
                Int.toString (#imm y)
  | ADD_2  y => mnemonic a "add" ^ reg2string_ (#Rd y) ^ ", #" ^
                Int.toString (#imm y)
  | SUB_2  y => mnemonic a "sub" ^ reg2string_ (#Rd y) ^ ", #" ^
                Int.toString (#imm y)
  | DP_    y => mnemonic a (opcode2string2 (#opc y)) ^ reg2string_ (#Rd y) ^
                ", " ^ reg2string_ (#Rm y)
  | ADD_4  y => mnemonic a "add" ^ reg2string (#Rd y) ^ ", " ^
                reg2string (#Rm y)
  | CMP_3  y => mnemonic a "cmp" ^ reg2string (#Rd y) ^ ", " ^
                reg2string (#Rm y)
  | MOV_3  y => mnemonic a "mov" ^ reg2string (#Rd y) ^ ", " ^
                reg2string (#Rm y)
  | BX_    y => mnemonic a "bx" ^ reg2string y
  | LDR_3  y => mnemonic a "ldr" ^ reg2string_ (#Rd y) ^ ", [pc, #" ^
                Int.toString (#imm y * 4) ^ "]"
  | DT_    y => mnemonic a (opcode2string3 (#opc y)) ^ reg2string_ (#Rd y) ^
                ", [" ^ reg2string_ (#Rn y) ^ ", " ^ reg2string_ (#Rm y) ^ "]"
  | DT_imm y => mnemonic a (opcode2string4 (#opc y)) ^ reg2string_ (#Rd y) ^
                ", [" ^ reg2string_ (#Rn y) ^ ", #" ^
                Int.toString (#imm y * align_opcode4 (#opc y)) ^ "]"
  | STR_3  y => mnemonic a "str" ^ reg2string_ (#Rd y) ^ ", [sp, #" ^
                Int.toString (#imm y * 4) ^ "]"
  | LDR_4  y => mnemonic a "ldr" ^ reg2string_ (#Rd y) ^ ", [sp, #" ^
                Int.toString (#imm y * 4) ^ "]"
  | ADD_5  y => mnemonic a "add" ^ reg2string_ (#Rd y) ^ ", pc, #" ^
                Int.toString (#imm y * 4)
  | ADD_6  y => mnemonic a "add" ^ reg2string_ (#Rd y) ^ ", sp, #" ^
                Int.toString (#imm y * 4)
  | ADD_7  y => mnemonic a "add" ^ "sp, sp, #" ^ Int.toString (y * 4)
  | SUB_4  y => mnemonic a "sub" ^ "sp, sp, #" ^ Int.toString (y * 4)
  | PUSH   y => mnemonic a "push" ^
                reg_list2string ((if #R y then 16384 else 0) + #list y)
  | POP    y => mnemonic a "pop" ^
                reg_list2string ((if #R y then 32768 else 0) + #list y)
  | LDMIA_ y => mnemonic a "ldmia" ^ reg2string_ (#Rn y) ^ "!, " ^
                reg_list2string (#list y)
  | STMIA_ y => mnemonic a "stmia" ^ reg2string_ (#Rn y) ^ "!, " ^
                reg_list2string (#list y)
  | B_1    y => mnemonic a ("b" ^ condition2string (#cond y)) ^
                thumb_target 8 l (#imm y)
  | UND_     => "0x" ^ Arbnum.toHexString (thumb_to_num x)
  | SWI_   y => mnemonic a "swi" ^ Int.toString y
  | B_2    y => mnemonic a "b" ^ thumb_target 11 l y
  | BL_    y => mnemonic a "bl" ^ thumb_target 22 l y
  | BL_a   y => mnemonic a "bl1" ^ Int.toString y
  | BL_b   y => mnemonic a "bl2" ^ Int.toString y;

fun arm_to_string l a (i as Instruction (x,c)) =
 (case x of
    Br y        => br_to_string l a i
  | Bx y        => bx_to_string a i
  | Swi_ex y    => swi_ex_to_string a i
  | Data_proc y => data_proc_to_string a i
  | Mla_mul y   => mla_mul_to_string a i
  | Ldrh_strh y => ldrh_strh_to_string a i
  | Ldr_str y   => ldr_str_to_string a i
  | Ldm_stm y   => ldm_stm_to_string a i
  | Swp y       => swp_to_string a i
  | Mrs y       => mrs_to_string a i
  | Msr y       => msr_to_string a i
  | Cdp y       => cdp_to_string a i
  | Mcr_mrc y   => mcr_mrc_to_string a i
  | Ldc_stc y   => ldc_stc_to_string a i
  | Undef       => "0x" ^ Arbnum.toHexString (arm_to_num i))
 | arm_to_string l a (Thumb x) = "code16 " ^ thumb_to_string l a x
 | arm_to_string _ _ (Data n) = "0x" ^ Arbnum.toHexString n
 | arm_to_string _ _ (ThumbData n) = "code16 0x" ^ Arbnum.toHexString n;

fun assembler_to_string l a lable =
  let val s = if isSome lable then (valOf lable) ^ ": " else "" in
    case a of
      Data.Code c         => s ^ arm_to_string l false c
    | Data.BranchS b      => s ^ branch_to_string a
    | Data.BranchN b      => s ^ branch_to_string a
    | Data.ThumbBranchS b => s ^ branch_to_string a
    | Data.ThumbBranchN b => s ^ branch_to_string a
    | _ => ""
  end;

(* ------------------------------------------------------------------------- *)

val encode_arm = arm_to_num o string_to_arm;

fun decode_arm i n = arm_to_string i false (num_to_arm n);
fun decode_arm_dec i n = decode_arm i (Arbnum.fromString n);
fun decode_arm_hex i n = decode_arm i (Arbnum.fromHexString n);

fun decode_thumb i n = arm_to_string i false (num_to_thumb n);
fun decode_thumb_dec i n = decode_thumb i (Arbnum.fromString n);
fun decode_thumb_hex i n = decode_thumb i (Arbnum.fromHexString n);

end;
