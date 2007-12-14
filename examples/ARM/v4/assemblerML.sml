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

val int2register = armLex.UserDeclarations.int2register;

fun register2int r =
  case r of
    R0  => 0  | R1  => 1  | R2  => 2  | R3  => 3
  | R4  => 4  | R5  => 5  | R6  => 6  | R7  => 7
  | R8  => 8  | R9  => 9  | R10 => 10 | R11 => 11
  | R12 => 12 | R13 => 13 | R14 => 14 | R15 => 15;

fun reg2string (NReg r) =
      let val n = register2int r in
        case n of
          13 => "sp"
        | 14 => "lr"
        | 15 => "pc"
        | _  => "r" ^ Int.toString n
      end
  | reg2string (VReg x) = x;

fun cp_reg2string (NReg r) = "c" ^ Int.toString (register2int r)
  | cp_reg2string (VReg x) = x;

fun cp_num2string n = "p" ^ Int.toString n;

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

val list2register = NReg o int2register o list2int;

fun list2opcode l =
  case list2int l of
    0  => AND | 1  => EOR | 2  => SUB | 3  => RSB
  | 4  => ADD | 5  => ADC | 6  => SBC | 7  => RSC
  | 8  => TST | 9  => TEQ | 10 => CMP | 11 => CMN
  | 12 => ORR | 13 => MOV | 14 => BIC | 15 => MVN
  | _ =>  raise Parse "list2opcode: not an opcode list";

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
    [0,0,1,1,0,_,1,0,_,_,_,_,1,1,1,1,_,_,_,_,_,_,_,_,_,_,_,_] => dec_msr l
  | [0,0,0,1,0,_,1,0,_,_,_,_,1,1,1,1,0,0,0,0,0,0,0,0,_,_,_,_] => dec_msr l
  | [0,0,0,1,0,_,0,0,1,1,1,1,_,_,_,_,_,0,0,0,0,0,0,0,0,0,0,0] => dec_mrs l
  | [0,0,0,0,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,1,0,0,1,_,_,_,_] => dec_mla_mul l
  | [0,0,0,1,0,_,0,0,_,_,_,_,_,_,_,_,0,0,0,0,1,0,0,1,_,_,_,_] => dec_swp l
  | [0,0,0,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,1,0,1,1,_,_,_,_] => dec_ldrh_strh l
  | [0,0,0,_,_,_,_,1,_,_,_,_,_,_,_,_,_,_,_,_,1,1,_,1,_,_,_,_] => dec_ldrh_strh l
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

fun ipow2 x = Word.toInt (Word.<<(Word.fromInt 1,Word.fromInt x))

local
  val n24 = ipow2 24
in
  fun validate_instruction (Data n) = Data n
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

  fun branch_to_arm (c,link,address) line =
        let open Arbnum
            val n4 = fromInt 4
            val n8 = fromInt 8
            val jmp = add32 address (num2comp (line + n8))
            val offset = (jmp div n4) mod (fromInt n24)
            val ok = (address =
                      add32 (line + n8) (sign_extend 24 32 offset * n4))
        in
           if ok then
             Instruction(Br {L = link, offset = toInt offset},c)
           else
             raise Data.Parse "Invalid branch instruction"
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

val armErr = ref TextIO.stdErr;

fun invoke lexstream = let
  fun print_error (s,i:int,_) =
      TextIO.output(!armErr, Int.toString i ^ ": " ^ s ^ "\n")
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

infix 0 <<;

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
   | Ldrh_strh y =>
       fromHexString "90" +
       options2_to_num (#L y, #P y, #U y, #W y, #S y, #H y) +
       (register_to_num (#Rn y) << 16) + (register_to_num (#Rd y) << 12) +
       addr_mode3_to_num (#offset y)
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
  val n25 = Word.toInt (Word.<<(Word.fromInt 1,Word.fromInt 25))
  val n26 = Word.toInt (Word.<<(Word.fromInt 1,Word.fromInt 26))
  fun offset2comp i = Int.mod(n26 - i,n26)
  fun abs_offset_string i j = let open Arbnum
            val x = sign_extend 24 32 (fromInt j)
        in
          "0x" ^ toHexString(add32 (i + fromInt 8) (x * fromInt 4))
        end;
  fun rel_offset_string i =
      let val j = Int.mod(Int.mod((i + 2) * 4,n26),n26) in
        if j < n25 then
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
          h ^ (if #L y then reg2string (#Rn y) ^ ", " else "") ^
          reg2string (#Rd y) ^ ", " ^ reg2string (#Rm y) ^ ", " ^
          reg2string (#Rs y) ^
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

  fun reg_list2string l = blocks2string (make_blocks (
        List.take(num2list 16 (Arbnum.fromInt l),16))) "{"

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

fun arm_to_string l a (i as Instruction (x,c)) =
 (case x of
    Br y        => br_to_string l a i
  | Swi_ex      => swi_ex_to_string c
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

end;
