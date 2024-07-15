structure arm_disassemblerLib :> arm_disassemblerLib =
struct

(* interactive use:
  app load ["arm_parserLib", "arm_encoderLib"];
*)

open HolKernel boolLib bossLib;
open armSyntax arm_astSyntax;

(* ------------------------------------------------------------------------- *)

val _ = numLib.temp_prefer_num();
val _ = wordsLib.prefer_word();

val ERR = Feedback.mk_HOL_ERR "arm_disassemblerLib";

(* ------------------------------------------------------------------------- *)

val eval = boolSyntax.rhs o Thm.concl o bossLib.EVAL;

val uint_of_word = wordsSyntax.uint_of_word;
val sint_of_term = Arbint.toInt o intSyntax.int_of_term;
val hex_of_word = Int.fmt StringCvt.HEX o uint_of_word;

fun mk_word2 i = wordsSyntax.mk_wordii (i,2);
fun mk_word4 i = wordsSyntax.mk_wordii (i,4);

val SP = mk_word4 13;
val AL = mk_word4 14;
val PC = mk_word4 15;

val is_T  = Term.term_eq T;
val is_F  = Term.term_eq F;
val is_SP = Term.term_eq SP;
val is_AL = Term.term_eq AL;
val is_PC = Term.term_eq PC;

fun is_0 tm = uint_of_word tm = 0;

val dest_strip = armSyntax.dest_strip;

fun i2l i =
let fun recurse n l =
          if n = 0 then List.rev l
                   else recurse (n div 2) ((n mod 2 = 1)::l)
in
  if i < 0 then
    raise ERR "i2l" "negative"
  else if i = 0 then
    [false]
  else
    recurse i []
end;

(* ------------------------------------------------------------------------- *)

val comma     = ", ";
val uppercase = String.map Char.toUpper;
val commy     = String.concat o Lib.separate comma;
fun square s  = String.concat ["[",s,"]"];
fun curly s   = String.concat ["{",s,"}"];
val scommy    = square o commy;
fun opt b c x = if b then x ^ c else x

fun code_line s1 s2 = (s1,s2) : string * string;
fun directive_line s1 s2 = code_line (uppercase s1) s2;

fun disassemble_ascii s = directive_line "ascii" (Lib.quote s);

local
  val tm_g = Parse.term_grammar ()
  val ty_g = Parse.type_grammar ()
in
  val term_to_string =
        PP.pp_to_string 70
          (Parse.mlower o term_pp.pp_term tm_g ty_g PPBackEnd.raw_terminal)
end

fun disassemble_byte l =
  l |> List.map term_to_string |> commy |> directive_line "byte"

fun disassemble_short l =
  l |> List.map term_to_string |> commy |> directive_line "short"

fun disassemble_word l =
  l |> List.map term_to_string |> commy |> directive_line "word"

(* ------------------------------------------------------------------------- *)

fun number tm =
let val s = term_to_string tm in
  if s = "ARB" then
    "UNPREDICTABLE"
  else
    String.extract(s,0,SOME (String.size s - 1))
end;

fun constant tm = "#" ^ number tm;
fun sign_constant (u,tm) = (if is_T u then "#" else "#-") ^ number tm;

fun offset tm =
let val s = tm |> integer_wordSyntax.mk_w2i |> eval |> term_to_string in
  if String.sub (s,0) = #"-" then
    "-#" ^ String.extract(s,1,SOME (String.size s - 1))
  else
    "+#" ^ s
end;

fun char_word4 c n =
let val _ = 0 <= n andalso n <= 15 orelse raise ERR "char_word4" "" in
  String.str c ^ Int.toString n
end;

fun reg 13 = "sp"
  | reg 14 = "lr"
  | reg 15 = "pc"
  | reg n = char_word4 #"r" n;

val register = reg o uint_of_word;
val cregister = (char_word4 #"c") o uint_of_word;
val coprocessor = (char_word4 #"p") o uint_of_word;
val rcommy = commy o List.map register;

local
  fun mk_blocks l =
  let
    fun blocks [] i ys = ys
      | blocks [false] i ys = ys
      | blocks [true] i [] = [(i,i)]
      | blocks [true] i (h::t) = ((fst h,i)::t)
      | blocks (false::false::xs) i ys = blocks (false::xs) (i + 1) ys
      | blocks (true::true::xs) i ys = blocks (true::xs) (i + 1) ys
      | blocks (false::true::xs) i ys =
          blocks (true::xs) (i + 1) ((i + 1,~1)::ys)
      | blocks (true::false::xs) i [] =
          blocks (false::xs) (i + 1) [(i,i)]
      | blocks (true::false::xs) i (h::t) =
          blocks (false::xs) (i + 1) ((fst h,i)::t)
  in
    List.rev (blocks l 0 (if hd l then [(0,~1)] else []))
  end

  fun reg_list s [] = s ^ "}"
    | reg_list s ((i,j)::xs) =
        reg_list (s ^ reg i ^
          (if i = j then
            ""
           else if i + 1 = j then
            comma ^ reg j
           else
            "-" ^ reg j) ^
          (if xs = [] then "" else comma)) xs
in
  val register_list =
        (reg_list "{") o mk_blocks o i2l o
        (fn i => i mod 0x10000) o uint_of_word
end;

fun full_condition tm =
  case uint_of_word tm
  of 0  => "eq"
   | 1  => "ne"
   | 2  => "cs"
   | 3  => "cc"
   | 4  => "mi"
   | 5  => "pl"
   | 6  => "vs"
   | 7  => "vc"
   | 8  => "hi"
   | 9  => "ls"
   | 10 => "ge"
   | 11 => "lt"
   | 12 => "gt"
   | 13 => "le"
   | 14 => "al"
   | _  => raise ERR "full_condition" "unexpected value";

fun condition tm =
  if Term.is_var tm then
    fst (Term.dest_var tm)
  else if is_AL tm orelse is_PC tm then
    ""
  else
    full_condition tm;

fun mnemonic (enc,cond,tm) s1 s2 =
let
  val q = if enc ~~ Encoding_Thumb2_tm andalso
             can arm_encoderLib.arm_encode
                 (arm_parserLib.Instruction (Encoding_Thumb_tm,cond,tm))
          then
            ".w"
          else
            ""
in
  code_line (s1 ^ condition cond ^ q) s2
end;

fun arm_expand_imm tm =
  ``(((7 >< 0) ^tm) #>> (2 * (w2n ((11 -- 8) ^tm)))) : word32``
    |> eval;

fun thumb_expand_imm tm =
  ``if (11 -- 10) ^tm = 0b00w then
      let imm8 = (7 >< 0) ^tm : word8 in
        case (9 >< 8) ^tm : word2
        of 0b00w => w2w imm8
         | 0b01w => if imm8 = 0w then ARB else
                      word32 [imm8; 0b00000000w; imm8; 0b00000000w]
         | 0b10w => if imm8 = 0w then ARB else
                      word32 [0b00000000w; imm8; 0b00000000w; imm8]
         | 0b11w => if imm8 = 0w then ARB else
                      word32 [imm8; imm8; imm8; imm8]
    else
      let unrotated_value = (7 :+ T) ((6 >< 0) ^tm) in
        (unrotated_value #>> w2n ((11 -- 7) ^tm))``
      |> eval;

fun shift tm =
  comma ^
  (case uint_of_word tm
   of 0 => "lsl "
    | 1 => "lsr "
    | 2 => "asr "
    | 3 => "ror "
    | _ => raise ERR "shift" "unexpected value");

fun disassemble_imm_shift (imm5,typ,rm) =
  case uint_of_word typ
  of 0 => if is_0 imm5 then
            register rm
          else
            register rm ^ shift typ ^ constant imm5
   | 1 => register rm ^ shift typ ^
            (if is_0 imm5 then "#32" else constant imm5)
   | 2 => register rm ^ shift typ ^
            (if is_0 imm5 then "#32" else constant imm5)
   | 3 => if is_0 imm5 then
            register rm ^ comma ^ "rrx"
          else
            register rm ^ shift typ ^ constant imm5
   | _ => raise ERR "disassemble_imm_shift" "unexpected value";

fun disassemble_mode1 thumb2 tm =
  case dest_strip tm
  of ("Mode1_immediate", [imm12]) =>
        imm12 |> (if thumb2 then thumb_expand_imm else arm_expand_imm)
              |> constant
   | ("Mode1_register", [imm5,typ,rm]) =>
        disassemble_imm_shift (imm5,typ,rm)
   | ("Mode1_register_shifted_register", [rs,typ,rm]) =>
       register rm ^ shift typ ^ register rs
   | _ => raise ERR "disassemble_mode1" "";

fun disassemble_mode2 (u,tm) =
  case dest_strip tm
  of ("Mode2_immediate", [imm12]) =>
         if is_T u andalso is_0 imm12 then
           ""
         else
           comma ^ sign_constant (u,imm12)
   | ("Mode2_register", [imm5,typ,rm]) =>
         comma ^ (if is_F u then "-" else "") ^
         disassemble_imm_shift (imm5,typ,rm)
   | _ => raise ERR "disassemble_mode2" "";

fun disassemble_mode3 (u,tm) =
  case dest_strip tm
  of ("Mode3_immediate", [imm12]) =>
         if is_T u andalso is_0 imm12 then
           ""
         else
           comma ^ sign_constant (u,imm12)
   | ("Mode3_register", [imm2,rm]) =>
        comma ^ (if is_F u then "-" else "") ^
        disassemble_imm_shift (imm2,``0w:word2``,rm)
   | _ => raise ERR "disassemble_mode3" "";

fun disassemble_mode5 (rn,p,u,w,imm8) =
let val imm32 = ``((w2w ^imm8) << 2) : word32`` |> eval in
  if is_T p then
    opt (is_T w) "!" (square
      (if is_0 imm32 then
         register rn
       else
         commy [register rn, sign_constant (u,imm32)]))
  else if is_T w then
    commy [square (register rn), sign_constant (u,imm32)]
  else if is_T u then
    commy [square (register rn), curly (number imm8)]
  else
    raise ERR "disassemble_mode5" "unexpected mode"
end;

fun rotation (n,rot) =
  case uint_of_word rot
  of 0 => register n
   | 1 => commy [register n, "ror #8"]
   | 2 => commy [register n, "ror #16"]
   | 3 => commy [register n, "ror #24"]
   | _ => raise ERR "rotation" "unexpected value";

fun data_processing
      (f : string -> string -> string * string) enc (opc,s,n,d,mode1) =
let
  val m1 = disassemble_mode1 (enc ~~ Encoding_Thumb2_tm) mode1
  val sflag = opt (is_T s) "s"
  fun arith x = f (sflag x) (commy [register d, register n, m1])
  fun move x = f (sflag x) (commy [register d, m1])
  fun test x = f x (commy [register n, m1])
in
  case uint_of_word opc
  of 0  => arith "and"
   | 1  => arith "eor"
   | 2  => arith "sub"
   | 3  => arith "rsb"
   | 4  => arith "add"
   | 5  => arith "adc"
   | 6  => arith "sbc"
   | 7  => arith "rsc"
   | 8  => test  "tst"
   | 9  => test  "teq"
   | 10 => test  "cmp"
   | 11 => test  "cmn"
   | 12 => arith "orr"
   | 13 => move  "mov"
   | 14 => arith "bic"
   | 15 => if enc ~~ Encoding_Thumb2_tm andalso not (is_PC n) then
             arith "orn"
           else
             move "mvn"
   | _  => raise ERR "register" "unexpected value"
end;

fun signed_halfword_multiply
      (f : string -> string -> string * string) (opc,M,N,d,a,m,n) =
  case (uint_of_word opc,is_T M,is_T N)
  of (0,false,false) => f "smlabb" (rcommy [d,n,m,a])
   | (0,false,true ) => f "smlatb" (rcommy [d,n,m,a])
   | (0,true, false) => f "smlabt" (rcommy [d,n,m,a])
   | (0,true, true ) => f "smlatt" (rcommy [d,n,m,a])
   | (1,false,false) => f "smlawb" (rcommy [d,n,m,a])
   | (1,false,true)  => f "smulwb" (rcommy [d,n,m])
   | (1,true, false) => f "smlawt" (rcommy [d,n,m,a])
   | (1,true, true)  => f "smulwt" (rcommy [d,n,m])
   | (2,false,false) => f "smlalbb" (rcommy [d,n,m,a])
   | (2,false,true ) => f "smlaltb" (rcommy [d,n,m,a])
   | (2,true, false) => f "smlalbt" (rcommy [d,n,m,a])
   | (2,true, true ) => f "smlaltt" (rcommy [d,n,m,a])
   | (3,false,false) => f "smulbb" (rcommy [d,n,m])
   | (3,false,true ) => f "smultb" (rcommy [d,n,m])
   | (3,true, false) => f "smulbt" (rcommy [d,n,m])
   | (3,true, true ) => f "smultt" (rcommy [d,n,m])
   | _ => raise ERR "signed_halfword_multiply" "unexpected value";

fun parallel_add_subtract (u,(opc1,opc2)) =
  case (is_T u,fst (dest_const opc1),fst (dest_const opc2))
  of (false,"Parallel_normal", "Parallel_add_16")               => "sadd16"
   | (false,"Parallel_normal", "Parallel_add_sub_exchange")     => "sasx"
   | (false,"Parallel_normal", "Parallel_sub_add_exchange")     => "ssax"
   | (false,"Parallel_normal", "Parallel_sub_16")               => "ssub16"
   | (false,"Parallel_normal", "Parallel_add_8")                => "sadd8"
   | (false,"Parallel_normal", "Parallel_sub_8")                => "ssub8"
   | (false,"Parallel_saturating", "Parallel_add_16")           => "qadd16"
   | (false,"Parallel_saturating", "Parallel_add_sub_exchange") => "qasx"
   | (false,"Parallel_saturating", "Parallel_sub_add_exchange") => "qsax"
   | (false,"Parallel_saturating", "Parallel_sub_16")           => "qsub16"
   | (false,"Parallel_saturating", "Parallel_add_8")            => "qadd8"
   | (false,"Parallel_saturating", "Parallel_sub_8")            => "qsub8"
   | (false,"Parallel_halving", "Parallel_add_16")              => "shadd16"
   | (false,"Parallel_halving", "Parallel_add_sub_exchange")    => "shasx"
   | (false,"Parallel_halving", "Parallel_sub_add_exchange")    => "shsax"
   | (false,"Parallel_halving", "Parallel_sub_16")              => "shsub16"
   | (false,"Parallel_halving", "Parallel_add_8")               => "shadd8"
   | (false,"Parallel_halving", "Parallel_sub_8")               => "shsub8"
   | (true, "Parallel_normal", "Parallel_add_16")               => "uadd16"
   | (true, "Parallel_normal", "Parallel_add_sub_exchange")     => "uasx"
   | (true, "Parallel_normal", "Parallel_sub_add_exchange")     => "usax"
   | (true, "Parallel_normal", "Parallel_sub_16")               => "usub16"
   | (true, "Parallel_normal", "Parallel_add_8")                => "uadd8"
   | (true, "Parallel_normal", "Parallel_sub_8")                => "usub8"
   | (true, "Parallel_saturating", "Parallel_add_16")           => "uqadd16"
   | (true, "Parallel_saturating", "Parallel_add_sub_exchange") => "uqasx"
   | (true, "Parallel_saturating", "Parallel_sub_add_exchange") => "uqsax"
   | (true, "Parallel_saturating", "Parallel_sub_16")           => "uqsub16"
   | (true, "Parallel_saturating", "Parallel_add_8")            => "uqadd8"
   | (true, "Parallel_saturating", "Parallel_sub_8")            => "uqsub8"
   | (true, "Parallel_halving", "Parallel_add_16")              => "uhadd16"
   | (true, "Parallel_halving", "Parallel_add_sub_exchange")    => "uhasx"
   | (true, "Parallel_halving", "Parallel_sub_add_exchange")    => "uhsax"
   | (true, "Parallel_halving", "Parallel_sub_16")              => "uhsub16"
   | (true, "Parallel_halving", "Parallel_add_8")               => "uhadd8"
   | (true, "Parallel_halving", "Parallel_sub_8")               => "uhsub8"
   | _ => raise ERR "parallel_add_subtract" "unexpected value";

fun msr_mask (r,mask) =
let fun odd n = n mod 2 = 1
    fun divodd n = (n div 2, odd n)
    val n = uint_of_word mask
    val (n,b0) = divodd n
    val (n,b1) = divodd n
    val (n,b2) = divodd n
    val b3 = odd n
in
  String.concat ((if is_T r then "spsr_" else "cpsr_")::
    (List.map (fn (b,c) => opt b c "") [(b3,"f"),(b2,"s"),(b1,"x"),(b0,"c")]))
end;

fun it_mask c0 mask =
let val n = uint_of_word mask in
  if c0 then
    case n
    of 8  => ""
     | 12 => "t"
     | 4  => "e"
     | 14 => "tt"
     | 6  => "et"
     | 10 => "te"
     | 2  => "ee"
     | 15 => "ttt"
     | 7  => "ett"
     | 11 => "tet"
     | 3  => "eet"
     | 13 => "tte"
     | 5  => "ete"
     | 9  => "tee"
     | 1  => "eee"
     | _ => raise ERR "it_mask" ""
  else
    case n
    of 8  => ""
     | 4  => "t"
     | 12 => "e"
     | 2  => "tt"
     | 10 => "et"
     | 6  => "te"
     | 14 => "ee"
     | 1  => "ttt"
     | 9  => "ett"
     | 5  => "tet"
     | 13 => "eet"
     | 3  => "tte"
     | 11 => "ete"
     | 7  => "tee"
     | 15 => "eee"
     | _ => raise ERR "it_mask" ""
end;

fun address f (p,u:term,w,n,t,mode:term) =
  opt (is_T w andalso is_T p) "!"
    (commy [register t,
      (if is_T p then
         [register n, f (u,mode)] |> String.concat |> square
       else
         String.concat [square (register n), f (u,mode)])]);

fun indexing (p,u) =
  (if is_T u then "i" else "d") ^
  (if is_T p then "b" else "a");

fun exclusive (n,imm8) =
  square
    (if is_0 imm8 then
       register n
     else
       commy [register n, ``(w2w ^imm8 << 2) : word32`` |> eval |> constant]);

fun hint (f : string -> string -> string * string) tm =
  case dest_strip tm
  of ("Hint_nop", [])                => f "nop" ""
   | ("Hint_yield", [])              => f "yield" ""
   | ("Hint_wait_for_event", [])     => f "wfe" ""
   | ("Hint_wait_for_interrupt", []) => f "wfi" ""
   | ("Hint_send_event", [])         => f "sev" ""
   | ("Hint_debug", [opt])           => f "dbg" (constant opt)
   | _ => raise ERR "hint" "";

fun barrier_option tm =
  case uint_of_word tm
  of 2  => "oshst"
   | 3  => "osh"
   | 6  => "nshst"
   | 7  => "nsh"
   | 10 => "ishst"
   | 11 => "ish"
   | 14 => "st"
   | _  => "sy";

(* ------------------------------------------------------------------------- *)

fun disassemble_branch (instr as (enc,_,tm)) =
let val f = mnemonic instr in
  case dest_strip (dest_Branch tm)
  of ("Branch_Target", [imm24]) =>
       f "b" (``if ^enc = Encoding_ARM then
                  sw2sw ^imm24 << 2 + 8w : word32
                else
                  sw2sw ^imm24 << 1 + 4w`` |> offset)
   | ("Branch_Exchange", [m]) =>
       f "bx" (register m)
   | ("Branch_Link_Exchange_Immediate", [h,toarm,imm24]) =>
       f (if (enc ~~ Encoding_ARM_tm) = is_F toarm then "blx" else "bl")
         (``let imm32 = (sw2sw ^imm24 << 2) +
                        (if ^enc = Encoding_ARM then 8w else 4w:word32) in
              if ^toarm then imm32 else (1 :+ ^h) imm32`` |> offset)
   | ("Branch_Link_Exchange_Register", [m]) =>
       f "blx" (register m)
   | ("Compare_Branch", [nzero,imm6,n]) =>
       f (if is_T nzero then "cbnz" else "cbz")
         (commy [register n, ``(w2w ^imm6 << 1) + 4w : word32`` |> offset])
   | ("Table_Branch_Byte", [n,h,m]) =>
       if is_T h then
         f "tbh" (scommy [register n, register m, "lsl #1"])
       else
         f "tbb" (scommy [register n, register m])
   | ("Check_Array", [n,m]) =>
       f "chka" (commy [register n,register m])
   | ("Handler_Branch_Link", [l,handler]) =>
       f (if is_T l then "hbl" else "hb") (constant handler)
   | ("Handler_Branch_Link_Parameter", [imm5,handler]) =>
       f "hblp" (commy [constant imm5, constant handler])
   | ("Handler_Branch_Parameter", [imm3,handler]) =>
       f "hbp" (commy [constant imm3, constant handler])
   | _ => raise ERR "disassemble_branch"
            ("cannot disassemble: " ^ term_to_string tm)
end;

fun disassemble_data_processing (instr as (enc,_,tm)) =
let val f = mnemonic instr
    fun ocommy b l x = rcommy (if b then l @ [x] else l)
in
  case dest_strip (dest_DataProcessing tm)
  of ("Data_Processing", [opc,s,n,d,mode1]) =>
        data_processing f enc (opc,s,n,d,mode1)
   | ("Move_Halfword", [h,d,imm16]) =>
        f (if is_T h then "movt" else "movw")
          (commy [register d, constant imm16])
   | ("Add_Sub", [a,n,d,imm12]) =>
        if enc ~~ Encoding_ARM_tm then
          f (if is_T a then "add" else "sub")
            (commy [register d, register n,
                    disassemble_mode1 false (mk_Mode1_immediate imm12)])
        else
          f (if enc ~~ Encoding_Thumb_tm then "add" else
               if is_T a then "addw" else "subw")
            (commy [register d, register n, constant imm12])
   | ("Multiply", [acc,s,d,a,m,n]) =>
        f ((if is_T acc then "mla" else "mul") ^ (if is_T s then "s" else ""))
          (ocommy (is_T acc) [d,n,m] a)
   | ("Multiply_Subtract", [d,a,m,n]) =>
        f "mls" (rcommy [d,n,m,a])
   | ("Signed_Halfword_Multiply", [opc,M,N,d,a,m,n]) =>
        signed_halfword_multiply f (opc,M,N,d,a,m,n)
   | ("Signed_Multiply_Dual", [d,a,m,M,N,n]) =>
        f ((if is_T M
            then if is_PC a then "smusd" else "smlsd"
            else if is_PC a then "smuad" else "smlad") ^
           (if is_T N then "x" else "")) (ocommy (not (is_PC a)) [d,n,m] a)
   | ("Signed_Multiply_Long_Dual", [dhi,dlo,m,M,N,n]) =>
        f ((if is_T M then "smlsld" else "smlald") ^
           (if is_T N then "x" else "")) (rcommy [dlo,dhi,n,m])
   | ("Signed_Most_Significant_Multiply", [d,a,m,r,n]) =>
        f ((if is_PC a then "smmul" else "smmla") ^
           (if is_T r then "r" else "")) (ocommy (not (is_PC a)) [d,n,m] a)
   | ("Signed_Most_Significant_Multiply_Subtract", [d,a,m,r,n]) =>
        f (if is_T r then "smmlsr" else "smmls") (rcommy [d,n,m,a])
   | ("Multiply_Long", [sgnd,a,s,dhi,dlo,m,n]) =>
        f ((if is_T sgnd then "s" else "u") ^
           (if is_T a then "mlal" else "mull") ^
           (if is_T s then "s" else "")) (rcommy [dlo,dhi,n,m])
   | ("Multiply_Accumulate_Accumulate", [dhi,dlo,m,n]) =>
        f "umaal" (rcommy [dlo,dhi,n,m])
   | ("Saturate", [u,sat,d,imm5,sh,n]) =>
        let
           val imm = constant (``if ^u then ^sat else ^sat + 1w`` |> eval)
           val imm = if is_T u then imm else if imm = "#0" then "#32" else imm
        in
           f (if is_T u then "usat" else "ssat")
             (commy [register d, imm,
               disassemble_imm_shift
                  (imm5,mk_word2 (if is_T sh then 2 else 0),n)])
        end
   | ("Saturate_16", [u,imm4,d,n]) =>
        let
           val imm = constant (``if ^u then ^imm4 else ^imm4 + 1w`` |> eval)
           val imm = if is_T u then imm else if imm = "#0" then "#16" else imm
        in
           f (if is_T u then "usat16" else "ssat16")
             (commy [register d, imm, register n])
        end
   | ("Saturating_Add_Subtract", [opc,n,d,m]) =>
        f (case uint_of_word opc
           of 0 => "qadd" | 1 => "qsub" | 2 => "qdadd" | 3 => "qdsub"
            | _ => raise ERR "disassemble_data_processing" "unexpected value")
          (rcommy [d,m,n])
   | ("Pack_Halfword", [n,d,imm5,t,m]) =>
        f (if is_T t then "pkhtb" else "pkhbt")
          (commy [register d, register n,
            disassemble_imm_shift (imm5,mk_word2 (if is_T t then 2 else 0),m)])
   | ("Extend_Byte", [u,n,d,rot,m]) =>
        f ((if is_T u then "u" else "s") ^
           (if is_PC n then "xtb" else "xtab"))
          (if is_PC n then
             commy [register d, rotation (m,rot)]
           else
             commy [register d, register n, rotation (m,rot)])
   | ("Extend_Byte_16", [u,n,d,rot,m]) =>
        f ((if is_T u then "u" else "s") ^
           (if is_PC n then "xtb16" else "xtab16"))
          (if is_PC n then
             commy [register d, rotation (m,rot)]
           else
             commy [register d, register n, rotation (m,rot)])
   | ("Extend_Halfword", [u,n,d,rot,m]) =>
        f ((if is_T u then "u" else "s") ^
           (if is_PC n then "xth" else "xtah"))
          (if is_PC n then
             commy [register d, rotation (m,rot)]
           else
             commy [register d, register n, rotation (m,rot)])
   | ("Bit_Field_Clear_Insert", [msb,d,lsb,n]) =>
        let
           val width = constant (``^msb - ^lsb + 1w`` |> eval)
           val width = if width = "#0" then "#32" else width
        in
          if is_PC n then
            f "bfc" (commy [register d, constant lsb, width])
          else
            f "bfi"
              (commy [register d, register n, constant lsb, width])
        end
   | ("Count_Leading_Zeroes", [d,m]) =>
        f "clz" (rcommy [d,m])
   | ("Reverse_Bits", [d,m]) =>
        f "rbit" (rcommy [d,m])
   | ("Byte_Reverse_Word", [d,m]) =>
        f "rev" (rcommy [d,m])
   | ("Byte_Reverse_Packed_Halfword", [d,m]) =>
        f "rev16" (rcommy [d,m])
   | ("Byte_Reverse_Signed_Halfword", [d,m]) =>
        f "revsh" (rcommy [d,m])
   | ("Bit_Field_Extract", [u,w,d,lsb,n]) =>
        let val width = ``^w + 1w`` |> eval in
          f (if is_T u then "ubfx" else "sbfx")
            (commy [register d, register n, constant lsb, constant width])
        end
   | ("Select_Bytes", [n,d,m]) =>
        f "sel" (rcommy [d,n,m])
   | ("Unsigned_Sum_Absolute_Differences", [d,a,m,n]) =>
        f (if is_PC a then "usad8" else "usada8")
          (ocommy (not (is_PC a)) [d,n,m] a)
   | ("Parallel_Add_Subtract", [u,opc,n,d,m]) =>
        f (parallel_add_subtract (u,pairTheory.dest_pair opc)) (rcommy [d,n,m])
   | ("Divide", [u,n,d,m]) =>
        f (if is_T u then "udiv" else "sdiv") (rcommy [d,n,m])
   | _ => raise ERR "disassemble_data_processing"
            ("cannot disassemble: " ^ term_to_string tm)
end;

fun disassemble_status_access (instr as (enc,_,tm)) =
let val f = mnemonic instr in
  case dest_strip (dest_StatusAccess tm)
  of ("Status_to_Register", [r,d]) =>
        f "mrs" (commy [register d, if is_T r then "spsr" else "cpsr"])
   | ("Immediate_to_Status", [r,mask,imm12]) =>
        f "msr" (commy [msr_mask (r,mask), imm12 |> arm_expand_imm |> constant])
   | ("Register_to_Status", [r,mask,n]) =>
        f "msr" (commy [msr_mask (r,mask), register n])
   | ("Change_Processor_State", [imod,A,I,F,mode]) =>
        let val effect = case uint_of_word imod
                         of 0 => ""
                          | 2 => "ie"
                          | 3 => "id"
                          | _ => raise ERR "disassemble_status_access"
                                   "unexpected value"
            fun optc x c = opt (is_T x) c ""
            val iflags = String.concat [optc A "a",optc I "i",optc F "f"]
        in
          f ("cps" ^ effect)
            (if effect = "" then
               constant (optionSyntax.dest_some mode)
             else if optionSyntax.is_some mode then
               commy [iflags, constant (optionSyntax.dest_some mode)]
             else
               iflags)
        end
   | ("Set_Endianness", [e]) =>
        f "setend" (if is_T e then "be" else "le")
   | _ => raise ERR "disassemble_status_access"
            ("cannot disassemble: " ^ term_to_string tm)
end;

fun disassemble_load_store (instr as (enc,_,tm)) =
let val f = mnemonic instr in
  case dest_strip (dest_LoadStore tm)
  of ("Load", [p,u,b,w,unpriv,n,t,mode2]) =>
       f (opt (is_T unpriv) "t" (if is_T b then "ldrb" else "ldr"))
         (address disassemble_mode2 (p,u,w,n,t,mode2))
   | ("Store", [p,u,b,w,unpriv,n,t,mode2]) =>
       f (opt (is_T unpriv) "t" (if is_T b then "strb" else "str"))
         (address disassemble_mode2 (p,u,w,n,t,mode2))
   | ("Load_Halfword", [p,u,w,s,h,unpriv,n,t,mode3]) =>
       f (opt (is_T unpriv) "t"
           (case (is_T s,is_T h)
            of (false, true ) => "ldrh"
             | (true,  false) => "ldrsb"
             | (true,  true ) => "ldrsh"
             | _ => raise ERR "disassemble_load_store" "unexpected value"))
         (address disassemble_mode3 (p,u,w,n,t,mode3))
   | ("Store_Halfword", [p,u,w,unpriv,n,t,mode3]) =>
       f (if is_T unpriv then "strht" else "strh")
         (address disassemble_mode3 (p,u,w,n,t,mode3))
   | ("Load_Dual", [p,u,w,n,t,t2,mode3]) =>
       f "ldrd"
         (commy [register t, address disassemble_mode3 (p,u,w,n,t2,mode3)])
   | ("Store_Dual", [p,u,w,n,t,t2,mode3]) =>
       f "strd"
         (commy [register t, address disassemble_mode3 (p,u,w,n,t2,mode3)])
   | ("Load_Multiple", [p,u,s,w,n,registers]) =>
       if is_F p andalso is_T u andalso is_T w andalso is_F s andalso is_SP n
       then
         f "pop" (register_list registers)
       else
         f ("ldm" ^ indexing (p,u))
           (commy [opt (is_T w) "!" (register n),
                   opt (is_T s) "^" (register_list registers)])
   | ("Store_Multiple", [p,u,s,w,n,registers]) =>
       if is_T p andalso is_F u andalso is_T w andalso is_F s andalso is_SP n
       then
         f "push" (register_list registers)
       else
         f ("stm" ^ indexing (p,u))
           (commy [opt (is_T w) "!" (register n),
                   opt (is_T s) "^" (register_list registers)])
   | ("Load_Exclusive", [n,t,imm8]) =>
       f "ldrex" (commy [register t, exclusive (n,imm8)])
   | ("Store_Exclusive", [n,d,t,imm8]) =>
       f "strex" (commy [register d, register t, exclusive (n,imm8)])
   | ("Load_Exclusive_Doubleword", [n,t,t2]) =>
       f "ldrexd" (commy [register t, register t2, square (register n)])
   | ("Store_Exclusive_Doubleword", [n,d,t,t2]) =>
       f "strexd"
         (commy [register d, register t, register t2, square (register n)])
   | ("Load_Exclusive_Halfword", [n,t]) =>
       f "ldrexh" (commy [register t, square (register n)])
   | ("Store_Exclusive_Halfword", [n,d,t]) =>
       f "strexh" (commy [register d, register t, square (register n)])
   | ("Load_Exclusive_Byte", [n,t]) =>
       f "ldrexb" (commy [register t, square (register n)])
   | ("Store_Exclusive_Byte", [n,d,t]) =>
       f "strexb" (commy [register d, register t, square (register n)])
   | ("Store_Return_State", [p,u,w,mode]) =>
       f ("srs" ^ indexing (p,u))
         (commy [opt (is_T w) "!" (register SP), constant mode])
   | ("Return_From_Exception", [p,u,w,n]) =>
       f ("rfe" ^ indexing (p,u)) (opt (is_T w) "!" (register n))
   | _ => raise ERR "disassemble_load_store"
            ("cannot disassemble: " ^ term_to_string tm)
end;

fun disassemble_miscellaneous (instr as (enc,_,tm)) =
let val f = mnemonic instr in
  case dest_strip (dest_Miscellaneous tm)
  of ("Hint", [h]) =>
        hint f h
   | ("Breakpoint", [imm16]) =>
        f "bkpt" (constant imm16)
   | ("Data_Memory_Barrier", [opt]) =>
        f "dmb" (barrier_option opt)
   | ("Data_Synchronization_Barrier", [opt]) =>
        f "dsb" (barrier_option opt)
   | ("Instruction_Synchronization_Barrier", [opt]) =>
        f "isb" "sy"
   | ("Swap", [b,n,t,t2]) =>
       f (opt (is_T b) "b" "swp")
         (commy [register t, register t2, square (register n)])
   | ("Preload_Data", [u,r,n,mode2]) =>
       f (opt (is_T r) "w" "pld")
         ([register n, disassemble_mode2 (u,mode2)] |> String.concat |> square)
   | ("Preload_Instruction", [u,n,mode2]) =>
       f "pli"
         ([register n, disassemble_mode2 (u,mode2)] |> String.concat |> square)
   | ("Supervisor_Call", [imm24]) =>
       f "svc" (constant imm24)
   | ("Secure_Monitor_Call", [imm4]) =>
       f "smc" (constant imm4)
   | ("Enterx_Leavex", [is_enterx]) =>
       f (if is_T is_enterx then "enterx" else "leavex") ""
   | ("Clear_Exclusive", []) =>
       f "clrex" ""
   | ("If_Then", [firstcond,mask]) =>
       f ("it" ^ it_mask ((uint_of_word firstcond) mod 2 = 1) mask)
         (full_condition firstcond)
   | _ => raise ERR "disassemble_miscellaneous"
            ("cannot encode: " ^ term_to_string tm)
end;

fun disassemble_coprocessor (instr as (enc,cond,tm)) =
let val f = mnemonic instr
    val v2 = opt (is_var cond orelse is_PC cond) "2"
    fun ocommy b l x = commy (if b then l @ [x] else l)
in
  case dest_strip (dest_Coprocessor tm)
  of ("Coprocessor_Load", [p,u,d,w,n,cd,coproc,imm8]) =>
        f (opt (is_T d) "l" (v2 "ldc"))
          (commy [coprocessor coproc, cregister cd,
                  disassemble_mode5 (n,p,u,w,imm8)])
   | ("Coprocessor_Store", [p,u,d,w,n,cd,coproc,imm8]) =>
        f (opt (is_T d) "l" (v2 "stc"))
          (commy [coprocessor coproc, cregister cd,
                  disassemble_mode5 (n,p,u,w,imm8)])
   | ("Coprocessor_Data_Processing", [opc1,n,d,coproc,opc2,m]) =>
        f (v2 "cdp")
          (ocommy (not (is_0 opc2))
            [coprocessor coproc, constant opc1, cregister d,
             cregister n, cregister m] (constant opc2))
   | ("Coprocessor_Transfer", [opc1,mrc,n,t,coproc,opc2,m]) =>
        f (v2 (if is_T mrc then "mrc" else "mcr"))
          (ocommy (not (is_0 opc2))
            [coprocessor coproc, constant opc1, register t,
             cregister n, cregister m] (constant opc2))
   | ("Coprocessor_Transfer_Two", [mrrc,t2,t,coproc,opc,m]) =>
        f (v2 (if is_T mrrc then "mrrc" else "mcrr"))
          (commy [coprocessor coproc, constant opc, register t,
                  register t2, cregister m])
   | _ => raise ERR "disassemble_coprocessor"
            ("cannot disassemble: " ^ term_to_string tm)
end;

(* ------------------------------------------------------------------------- *)

fun disassemble_instruction (instr as (enc,cond,tm)) =
  case dest_strip tm
  of ("Branch", [i]) =>
         disassemble_branch instr
   | ("DataProcessing", [i]) =>
         disassemble_data_processing instr
   | ("StatusAccess", [i]) =>
         disassemble_status_access instr
   | ("LoadStore", [i]) =>
         disassemble_load_store instr
   | ("Miscellaneous", [i]) =>
         disassemble_miscellaneous instr
   | ("Coprocessor", [i]) =>
         disassemble_coprocessor instr
   | ("Undefined", []) =>
        (case fst (dest_const enc)
         of "Encoding_ARM"    => let val c = hex_of_word cond in
                                   directive_line "word"  ("0x" ^ c ^ "6000010")
                                 end
          | "Encoding_Thumb"  => directive_line "short" "0xDE00"
          | "Encoding_Thumb2" => directive_line "word"  "0xF7F0A000"
          | _ => raise ERR "" "unexpected value")
   | _ => raise ERR "disassemble_instruction" ("cannot disassemble: " ^
            term_to_string (pairSyntax.mk_pair (enc,tm)));

(* ------------------------------------------------------------------------- *)

fun arm_disassemble (arm_parserLib.Ascii s)       = disassemble_ascii s
  | arm_disassemble (arm_parserLib.Byte l)        = disassemble_byte l
  | arm_disassemble (arm_parserLib.Short l)       = disassemble_short l
  | arm_disassemble (arm_parserLib.Word l)        = disassemble_word l
  | arm_disassemble (arm_parserLib.Instruction i) = disassemble_instruction i;

(*
val arm_disassemble_parse =
  List.map (arm_disassemble o
       (snd : Arbnum.num * arm_parserLib.arm_code -> arm_parserLib.arm_code));

val arm_disassemble_from_quote =
  arm_disassemble_parse o fst o arm_parserLib.arm_parse_from_quote;

val arm_disassemble_from_string =
  arm_disassemble_parse o fst o arm_parserLib.arm_parse_from_string;

val arm_disassemble_from_file =
  arm_disassemble_parse o fst o arm_parserLib.arm_parse_from_file;
*)

end
