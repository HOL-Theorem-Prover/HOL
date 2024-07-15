structure arm_parserLib :> arm_parserLib =
struct

(* interactive use:
  app load ["armSyntax", "arm_astSyntax", "integer_wordSyntax",
            "wordsLib", "intLib", "intSyntax"];
*)

open HolKernel boolLib bossLib intLib integer_wordTheory;
open armSyntax arm_astSyntax;

(* ------------------------------------------------------------------------- *)

val _ = numLib.temp_prefer_num();
val _ = wordsLib.prefer_word();

val ERR = Feedback.mk_HOL_ERR "arm_parserLib";

local
  val tm_g = Parse.term_grammar ()
  val ty_g = Parse.type_grammar ()
in
  val term_to_string =
        PP.pp_to_string 70
          (Parse.mlower o term_pp.pp_term tm_g ty_g PPBackEnd.raw_terminal)
end

fun quote_to_string l =
let fun recurse [] s = s
      | recurse (QUOTE q :: t) s = recurse t (s ^ q)
      | recurse (ANTIQUOTE q :: t) s = recurse t (s ^ q)
in
  recurse l ""
end;

(* ------------------------------------------------------------------------- *)

datatype instruction_mnemonic
  = ADC     | ADD    | ADDW    | ADR     | AND     | ASR
  | B       | BFC    | BFI     | BIC     | BKPT    | BL      | BLX | BX
  | CBZ     | CBNZ   | CDP     | CDP2    | CHKA    | CLREX   | CLZ | CMN
  | CMP     | CPS    | CPSIE   | CPSID
  | DBG     | DMB    | DSB
  | ENTERX  | EOR
  | HB      | HBL    | HBLP    | HBP
  | ISB     | IT
  | LDC     | LDCL   | LDC2    | LDC2L   | LDMIA   | LDMDA   | LDMDB   | LDMIB
  | LDR     | LDRB   | LDRBT   | LDRD    | LDREX   | LDREXB
  | LDREXD  | LDREXH | LDRH    | LDRHT   | LDRSB   | LDRSBT
  | LDRSH   | LDRSHT | LDRT    | LEAVEX  | LSL     | LSR
  | MCR     | MCR2   | MCRR    | MCRR2   | MLA     | MLS     | MOV | MOVT | MOVW
  | MRC     | MRC2   | MRRC    | MRRC2   | MRS     | MSR     | MUL | MVN
  | NOP
  | ORN     | ORR
  | PKHBT   | PKHTB  | PLD     | PLDW    | PLI     | POP     | PUSH
  | QADD    | QADD16 | QADD8   | QASX    | QDADD   | QDSUB   | QSAX
  | QSUB    | QSUB16 | QSUB8
  | RBIT    | REV    | REV16   | REVSH   | RFEIA   | RFEDA
  | RFEDB   | RFEIB  | ROR     | RRX     | RSB     | RSC
  | SADD16  | SADD8  | SASX    | SBC     | SBFX    | SDIV    | SEL
  | SETEND  | SEV    | SHADD16 | SHADD8  | SHASX   | SHSAX   | SHSUB16
  | SHSUB8  | SMC
  | SMLABB  | SMLABT  | SMLATB  | SMLATT
  | SMLALBB | SMLALBT | SMLALTB | SMLALTT
  | SMULBB  | SMULBT  | SMULTB  | SMULTT
  | SMLAWB  | SMLAWT  | SMULWB  | SMULWT
  | SMUAD   | SMUADX
  | SMUSD   | SMUSDX
  | SMLAD   | SMLADX
  | SMLALD  | SMLALDX
  | SMLSD   | SMLSDX
  | SMLSLD  | SMLSLDX
  | SMMUL   | SMMULR
  | SMMLA   | SMMLAR
  | SMMLS   | SMMLSR
  | SMULL   | SMLAL
  | SRSIA   | SRSDA  | SRSDB   | SRSIB   | SSAT    | SSAT16  | SSAX
  | SSUB16  | SSUB8  | STC     | STCL    | STC2    | STC2L
  | STMIA   | STMDA  | STMDB   | STMIB   | STR     | STRB    | STRBT
  | STRD    | STREX  | STREXB  | STREXD  | STREXH  | STRH    | STRHT
  | STRT    | SUB    | SUBW    | SVC
  | SWP     | SWPB   | SXTAB   | SXTAB16 | SXTAH   | SXTB    | SXTB16  | SXTH
  | TBB     | TBH    | TEQ     | TST
  | UADD16  | UADD8  | UASX    | UBFX    | UDIV    | UHADD16 | UHADD8
  | UHASX   | UHSAX  | UHSUB16 | UHSUB8  | UMAAL   | UMLAL   | UMULL
  | UQADD16 | UQADD8 | UQASX   | UQSAX   | UQSUB16 | UQSUB8  | USAD8
  | USADA8  | USAT   | USAT16  | USAX    | USUB16  | USUB8   | UXTAB
  | UXTAB16 | UXTAH  | UXTB    | UXTB16  | UXTH
  | WFE     | WFI
  | YIELD;

datatype arch = ARMv4 | ARMv4T
              | ARMv5T | ARMv5TE
              | ARMv6 | ARMv6K | ARMv6T2
              | ARMv7_A | ARMv7_R;

datatype qualifier = Narrow | Wide | Either;

datatype code = ARM_CODE | THUMB_CODE | THUMBX_CODE;

type instruction =
  {sflag : term, cond : term, qual : qualifier,
   mnemonic : instruction_mnemonic };

type state =
  {instruction : instruction option,
   code       : code,
   linenumber  : int,
   itstate     : term * bool list,
   arch        : arch,
   tokens      : Substring.substring list };

datatype 'a error_okay =
   Error of { origin_function : string, message : string } | Okay of 'a;

type 'a M = state -> ('a * state) error_okay;

infix >>= >>-;

val op >>= : 'a M * ('a -> 'b M) -> 'b M =
  fn (f,g) => fn s =>
    case f s
      of Error e    => Error e
       | Okay (x,t) => g x t;

val return : 'a -> 'a M = fn x => fn s => Okay (x,s);

val op >>- = fn (f,g) => f >>= (fn _ => g);

val raiseT : string * string -> 'a M =
  fn (x,y) => fn _ => Error { origin_function = x, message = y };

val tryT : 'a M -> ('a -> 'b M) -> (unit -> 'b M) -> 'b M =
  fn f => fn g => fn h => fn s =>
    case f s
      of Error e => h () s
       | Okay (x,t) => g x t;

val optionT : unit M -> unit M =
  fn f => tryT f return (fn _ => return ());

val readT  : (state -> 'a) -> 'a M = fn f => fn (s:state) => Okay (f s,s);
val writeT : (state -> state) -> unit M = fn f => fn (s:state) => Okay ((),f s);

val read_instruction = readT (#instruction);
val read_linenumber  = readT (#linenumber);
val read_itstate     = readT (#itstate);
val read_thumb       = readT (fn s => #code s <> ARM_CODE);
val read_thumbee     = readT (fn s => #code s = THUMBX_CODE);
val read_arch        = readT (#arch);
val read_tokens      = readT (#tokens);
val read_token       = read_tokens >>= (fn l => return (total hd l));

val read_cond : term M =
  read_instruction >>= (fn i => return (#cond (valOf i)));

val read_sflag : term M =
  read_instruction >>= (fn i => return (#sflag (valOf i)));

val read_qualifier : qualifier M =
  read_instruction >>= (fn i => return (#qual (valOf i)));

val read_mnemonic : instruction_mnemonic M =
  read_instruction >>= (fn i => return (#mnemonic (valOf i)));

val read_InITBlock : bool M =
  read_itstate >>= (fn (c,l) =>
    return (not (null l) andalso c !~ boolSyntax.arb));

val read_OutsideOrLastInITBlock : bool M =
  read_itstate >>= (fn (_,l) => return (length l <= 1));

val write_instruction = fn i => writeT (fn s =>
  { instruction = i,
    code        = #code s,
    linenumber  = #linenumber s,
    arch        = #arch s,
    itstate     = #itstate s,
    tokens      = #tokens s });

val write_cond = fn c => writeT (fn s =>
let val i = #instruction s in
  { instruction = if isSome i then
                    let val i = valOf i in
                      SOME { sflag = #sflag i, cond = c, qual = #qual i,
                            mnemonic = # mnemonic i }
                    end
                  else
                    raise ERR "write_cond" "no instruction",
    code        = #code s,
    linenumber  = #linenumber s,
    arch        = #arch s,
    itstate     = #itstate s,
    tokens      = #tokens s }
end);

val write_code = fn c => writeT (fn s =>
  { instruction = #instruction s,
    code        = c,
    linenumber  = #linenumber s,
    arch        = #arch s,
    itstate     = (boolSyntax.arb,[]),
    tokens      = #tokens s });

val write_arch = fn a => writeT (fn s =>
  { instruction = #instruction s,
    code        = if a = ARMv4 then ARM_CODE else #code s,
    linenumber  = #linenumber s,
    arch        = a,
    itstate     = (boolSyntax.arb,[]),
    tokens      = #tokens s });

val write_itcond = fn c => writeT (fn s =>
  { instruction = #instruction s,
    code        = #code s,
    linenumber  = #linenumber s,
    arch        = #arch s,
    itstate     = (c, snd (#itstate s)),
    tokens      = #tokens s });

val write_itlist = fn l => writeT (fn s =>
  { instruction = #instruction s,
    code        = #code s,
    linenumber  = #linenumber s,
    arch        = #arch s,
    itstate     = (fst (#itstate s), l),
    tokens      = #tokens s });

val write_token = fn t => writeT (fn s =>
  { instruction = #instruction s,
    code        = #code s,
    linenumber  = #linenumber s,
    arch        = #arch s,
    itstate     = #itstate s,
    tokens      = t::tl (#tokens s) });

val next_linenumber = writeT (fn s =>
  { instruction = #instruction s,
    code        = #code s,
    linenumber  = #linenumber s + 1,
    arch        = #arch s,
    itstate     = #itstate s,
    tokens      = #tokens s });

val next_itstate = writeT (fn s =>
  { instruction = #instruction s,
    code        = #code s,
    linenumber  = #linenumber s,
    arch        = #arch s,
    itstate     = let val (c,l) = #itstate s in
                    if length l < 2 then
                      (boolSyntax.arb,[])
                    else
                      (c, tl l)
                  end,
    tokens      = #tokens s });

val next_token = writeT (fn s =>
  { instruction = #instruction s,
    code        = #code s,
    linenumber  = #linenumber s,
    arch        = #arch s,
    itstate     = #itstate s,
    tokens      = case #tokens s of [] => [] | h::t => t });

datatype shift = ROR_shift | LSR_shift | ASR_shift | LSL_shift | RRX_shift;

fun syntax_errorT (e,g) : 'a M =
  read_linenumber >>=
  (fn n => raiseT ("parse " ^ e,
        "syntax error at line " ^ Int.toString n ^
        ": expecting " ^ e ^ " got " ^ g));

fun other_errorT (e,m) : 'a M =
  read_linenumber >>=
  (fn n => raiseT (e, "error at line " ^ Int.toString n ^ ": " ^ m));

val assertT : bool -> (string * string) -> 'a M -> 'a M =
  fn b => fn x => fn f =>
    if b then f else other_errorT x;

(* ------------------------------------------------------------------------- *)

fun whitespace c = Char.isSpace c andalso c <> #"\n";
fun alphanum c = Char.isAlphaNum c orelse mem c (explode "._'");
fun variable c = alphanum c andalso not (Char.isDigit c);
val isBinDigit = Lib.C mem (explode "01");
val isOctDigit = Lib.C mem (explode "01234567");

val lower_explode = map Char.toLower o Substring.explode;
val lower_string = String.implode o lower_explode;
val lower_substring = Substring.full o lower_string;

local
  val sstr = Substring.full o String.str

  fun split_at_end_quote s =
  let fun recurse i =
        case (total Substring.sub (s,i),total Substring.sub (s,i + 1))
        of (NONE, SOME #"\"")   => i + 1
         | (SOME c, SOME #"\"") => if c <> #"\\" then i + 1 else recurse (i + 1)
         | (_, SOME c)          => recurse (i + 1)
         | _                    => i + 1
  in
    Substring.splitAt (s,Int.min (recurse ~1 + 1, Substring.size s))
  end

  fun skip_block left right s =
  let
    val sleft  = String.size left
    val sright = String.size right

    fun recurse n (ls,rs) =
        let val (l,r) = Substring.position left rs
            val (ll,rl) = Substring.position right l
        in
          if Substring.isPrefix right rl orelse Substring.size r < sleft then
            if n = 0 orelse Substring.size rl < sright then
              (Substring.span (ls,ll), Substring.span(rl,r))
            else let val (lrl,rrl) = Substring.splitAt (rl,sright) in
              recurse (n - 1)
                (Substring.span (ls,Substring.span (ll,lrl)),
                 Substring.span (rrl,r))
            end
          else let val (lr,rr) = Substring.splitAt (r,sleft) in
            recurse (n + 1) (Substring.span (ls,Substring.span (l,lr)), rr)
          end
        end
  in
    recurse 0 (Substring.slice(s,0,SOME 0), s)
  end

  fun skip_to_newline s = snd (Substring.splitl (not o curry (op =) #"\n") s)

  fun get_newlines s =
        s |> Substring.explode
          |> List.filter (curry (op =) #"\n")
          |> map sstr

  fun lex s a =
  let val s0 = Substring.dropl whitespace s in
    case Substring.getc s0
      of SOME (#"/",s1) =>
           (case Substring.getc s1
            of SOME (#"*",s2) =>
                 let val (s3,s4) = skip_block "/*" "*/" s2
                     val _ = Substring.isPrefix "*/" s4 orelse
                               raise ERR "lex" "missing closing */"
                 in
                   lex (Substring.triml 2 s4) (get_newlines s3 @ a)
                 end
             | SOME (#"/",s2) => lex (skip_to_newline s0) a
             | _ => lex s1 ((sstr #"/")::a))
       | SOME (#"(",s1) =>
           (case Substring.getc s1
            of SOME (#"*",s2) =>
                 let val (s3,s4) = skip_block "(*" "*)" s2
                     val _ = Substring.isPrefix "*)" s4 orelse
                               raise ERR "lex" "missing closing *)"
                 in
                   lex (Substring.triml 2 s4) (get_newlines s3 @ a)
                 end
             | _ => lex s1 ((sstr #"(")::a))
       | SOME (#"@",s1) => lex (skip_to_newline s0) a
       | SOME (#";",s1) => lex (skip_to_newline s0) a
       | SOME (#"\"",s1) =>
           let val (l,r) = split_at_end_quote s1 in
             lex r (Substring.full ("\"" ^ Substring.string l)::a)
           end
       | SOME (c,s1) =>
           if alphanum c then
             let val (l,r) = Substring.splitl alphanum s0 in
               lex r (l::a)
             end
           else
             lex s1 ((sstr c)::a)
       | NONE => List.rev a
  end
in
  fun arm_lex s = lex (Substring.full s) []
end;

val arm_lex_quote = arm_lex o quote_to_string;

(* ------------------------------------------------------------------------- *)

fun arm_parse (f:'a M) s =
let val init = { instruction = NONE,
                 code = ARM_CODE,
                 arch = ARMv7_A,
                 linenumber = 1,
                 itstate = (boolSyntax.arb,[]),
                 tokens = arm_lex s }
in
  case f init
    of Error e    => raise ERR (#origin_function e) (#message e)
     | Okay (v,t) => v
end;

fun arm_parse_quote f q = arm_parse f (quote_to_string q);

fun expr i = if i < 0 then "-" ^ Int.toString (Int.abs i) else Int.toString i;

(* ------------------------------------------------------------------------- *)

val eval = rhs o concl o EVAL;

fun cast_var ty v = mk_var (fst (dest_var v),ty);

fun mk_bool b    = if b then T else F;
fun mk_word2 i   = wordsSyntax.mk_wordii (i,2);
fun mk_word3 i   = wordsSyntax.mk_wordii (i,3);
fun mk_word4 i   = wordsSyntax.mk_wordii (i,4);
fun mk_word5 i   = wordsSyntax.mk_wordii (i,5);
fun mk_word6 i   = wordsSyntax.mk_wordii (i,6);
fun mk_word8 i   = wordsSyntax.mk_wordii (i,8);
fun mk_word12 i  = wordsSyntax.mk_wordii (i,12);
fun mk_word16 i  = wordsSyntax.mk_wordii (i,16);
fun mk_word24 i  = wordsSyntax.mk_wordii (i,24);
fun mk_word32 n  = wordsSyntax.mk_wordi (n,32);
val mk_integer   = intSyntax.mk_injected o numSyntax.mk_numeral;
val uint_of_word = wordsSyntax.uint_of_word;

fun sint_of_term tm =
  tm |> intSyntax.int_of_term |> Arbint.toInt
  handle Overflow => raise ERR "sint_of_term"
                       ("integer " ^ term_to_string tm ^ " too large")
       | HOL_ERR _ => raise ERR "sint_of_term"
                       ("could not convert ``" ^ term_to_string tm ^
                        "`` to an integer");

fun list_to_int l =
let fun recurse [] a = a
      | recurse (h::t) a = recurse t (if h = 1 then 2 * a + 1 else 2 * a)
in
  recurse l 0
end;

val is_T   = term_eq T;
val is_F   = term_eq F;
val is_R9  = term_eq (mk_word4 9);
val is_R10 = term_eq (mk_word4 10);
val is_SP  = term_eq (mk_word4 13);
val is_AL  = term_eq (mk_word4 14);
val is_PC  = term_eq (mk_word4 15);

infix pow

fun op pow (x,y) =
  if y mod 2 = 1 then
    x * (x pow (y - 1))
  else
    if y = 0 then
      1
    else
      (x * x) pow (y div 2);

fun bit i n = n div (2 pow i) mod 2 = 1;

fun int_to_word n tm =
let val r = eval (integer_wordSyntax.mk_i2w (tm,n))
    val _ = mk_disj (mk_eq (tm,integer_wordSyntax.mk_w2i r),
                     mk_eq (tm,r |> wordsSyntax.mk_w2n
                                 |> intSyntax.mk_injected))
              |> EVAL |> EQT_ELIM
            handle HOL_ERR _ => raise ERR "int_to_word"
              ("Failed to convert integer " ^ term_to_string tm ^
               " to a signed " ^
               (n |> fcpLib.index_to_num |> Arbnum.toString) ^ "-bit word")
in
  r
end;

fun uint_to_word n tm =
let val r = eval (integer_wordSyntax.mk_i2w (tm,n))
    val _ = mk_eq (tm,r |> wordsSyntax.mk_w2n |> intSyntax.mk_injected)
              |> EVAL |> EQT_ELIM
            handle HOL_ERR _ => raise ERR "uint_to_word"
              ("Failed to convert integer " ^ term_to_string tm ^
               " to an unsigned " ^
               (n |> fcpLib.index_to_num |> Arbnum.toString) ^ "-bit word")
in
  r
end;

local
  val n4    = Arbnum.fromInt 4
  val n128  = Arbnum.fromInt 128
  val n256  = Arbnum.fromInt 256
  val msb30 = Arbnum.pow (Arbnum.two, Arbnum.fromInt 30)
  val msb32 = Arbnum.pow (Arbnum.two, Arbnum.fromInt 32)

  fun rol_two32 n =
        let val n' = Arbnum.mod (Arbnum.*(n,n4), msb32) in
          Arbnum.+(n',Arbnum.div (n, msb30))
        end

  fun num_to_imm x n =
    let val x' = Arbnum.mod (x,n256) in
      if x' = x then
        (n, x')
      else
        if n < 15 then
          num_to_imm (rol_two32 x) (n + 1)
        else
          raise ERR "num_to_imm" "cannot be represented as an immediate"
    end

  fun num_to_immediate n =
        let open Arbnum
            val (s,n) = num_to_imm n 0
        in
          (fromInt s * n256) + n
        end

  fun num_to_bytes n =
        let val (r,b0) = Arbnum.divmod (n, n256)
            val (r,b1) = Arbnum.divmod (r, n256)
            val (r,b2) = Arbnum.divmod (r, n256)
        in
          (Arbnum.mod (r,n256), b2, b1, b0)
        end

  fun num_to_thumb2_immediate n =
        let val error = "cannot be represented as an Thumb2 immediate"
            val (b3,b2,b1,b0) = num_to_bytes n
            fun is_zero x = x = Arbnum.zero
            fun imm (x,y) = Arbnum.+(Arbnum.*(Arbnum.fromInt x,n256),y)
        in
          case (is_zero b3, is_zero b2, is_zero b1, is_zero b0)
          of (true,true,true,_) =>
                b0
           | (true,false,true,false) =>
                if b2 = b0 then imm (1,b0) else
                  raise ERR "num_to_thumb2_immediate" error
           | (false,true,false,true) =>
                if b3 = b1 then imm (2,b1) else
                  raise ERR "num_to_thumb2_immediate" error
           | (false,false,false,false) =>
                if b3 = b2 andalso b2 = b1 andalso b1 = b0 then imm (3,b0) else
                  raise ERR "num_to_thumb2_immediate" error
           | _ =>
              let val m = Arbnum.log2 n
                  val lsr_n = funpow (Arbnum.toInt m + 1 - 8) Arbnum.div2 n
                  val s = Arbnum.fromInt (31 - Arbnum.toInt m + 8)
              in
                if Arbnum.<(lsr_n, n256) then
                  Arbnum.+(Arbnum.*(s,n128),Arbnum.mod (lsr_n,n128))
                else
                  raise ERR "num_to_thumb2_immediate" error
              end
        end

  fun int_to_imm f tm =
        (tm |> int_to_word ``:32``
            |> wordsSyntax.dest_n2w
            |> fst
            |> numSyntax.dest_numeral
            |> f
            |> Arbnum.toInt
            |> mk_word12) handle HOL_ERR _ =>
              raise ERR "int_to_immediate"
                ("cannot represent " ^ term_to_string tm ^
                 " as a mode1 immediate")
in
  val int_to_mode1_immediate        = int_to_imm num_to_immediate
  val int_to_thumb2_mode1_immediate = int_to_imm num_to_thumb2_immediate
end;

fun offset_to_imm24 i =
  if 0 <= i then
    mk_word24 i
  else
    i |> Int.~
      |> mk_word24
      |> wordsSyntax.mk_word_2comp
      |> eval;

(* ------------------------------------------------------------------------- *)

local
  val mnemonic_strings =
  [("adc", ADC), ("add", ADD), ("addw", ADDW), ("adr", ADR), ("and", AND),
   ("asr", ASR),
   ("b", B), ("bfc", BFC), ("bfi", BFI), ("bic", BIC), ("bkpt", BKPT),
   ("bl", BL), ("blx", BLX), ("bx", BX),
   ("cbz", CBZ), ("cbnz", CBNZ), ("cdp", CDP), ("cdp2", CDP2), ("chka", CHKA),
   ("clrex", CLREX),
   ("clz", CLZ), ("cmn", CMN), ("cmp", CMP),
   ("cps", CPS), ("cpsie", CPSIE), ("cpsid", CPSID),
   ("dbg", DBG), ("dmb", DMB), ("dsb", DSB),
   ("enterx",ENTERX), ("eor", EOR),
   ("hb", HB), ("hbl", HBL), ("hblp", HBLP), ("hbp", HBP),
   ("isb", ISB), ("it", IT),
   ("ldc", LDC), ("ldcl", LDCL), ("ldc2", LDC2), ("ldc2l", LDC2L),
   ("ldm", LDMIA), ("ldmia", LDMIA), ("ldmfd", LDMIA),
   ("ldmda", LDMDA), ("ldmfa", LDMDA),
   ("ldmdb", LDMDB), ("ldmea", LDMDB),
   ("ldmib", LDMIB), ("ldmed", LDMIB),
   ("ldr", LDR), ("ldrb", LDRB),
   ("ldrbt", LDRBT), ("ldrht", LDRHT),
   ("ldrd", LDRD), ("ldrex", LDREX), ("ldrexb", LDREXB), ("ldrexd", LDREXD),
   ("ldrexh", LDREXH), ("ldrh", LDRH),
   ("ldrsb", LDRSB), ("ldrsbt", LDRSBT), ("ldrsh", LDRSH), ("ldrsht", LDRSHT),
   ("ldrt", LDRT),
   ("leavex", LEAVEX), ("lsl", LSL), ("lsr", LSR),
   ("mcr", MCR), ("mcr2", MCR2), ("mcrr", MCRR), ("mcrr2", MCRR2), ("mla", MLA),
   ("mls", MLS), ("mov", MOV), ("movt", MOVT), ("movw", MOVW),
   ("mrc", MRC), ("mrc2", MRC2), ("mrrc", MRRC), ("mrrc2", MRRC2), ("mrs", MRS),
   ("msr", MSR), ("mul", MUL), ("mvn", MVN),
   ("nop", NOP),
   ("orn", ORN), ("orr", ORR),
   ("pkhbt", PKHBT), ("pkhtb", PKHTB), ("pld", PLD), ("pldw", PLDW),
   ("pli", PLI), ("pop", POP), ("push", PUSH),
   ("qadd", QADD), ("qadd16", QADD16), ("qadd8", QADD8), ("qasx", QASX),
   ("qdadd", QDADD), ("qdsub", QDSUB), ("qsax", QSAX),
   ("qsub", QSUB), ("qsub16", QSUB16), ("qsub8", QSUB8),
   ("rbit", RBIT), ("rev", REV), ("rev16", REV16), ("revsh", REVSH),
   ("rfe", RFEIA), ("rfeia", RFEIA), ("rfeda", RFEDA), ("rfedb", RFEDB),
   ("rfeib", RFEIB), ("ror", ROR), ("rrx", RRX), ("rsb", RSB), ("rsc", RSC),
   ("sadd16", SADD16), ("sadd8", SADD8), ("sasx", SASX), ("sbc", SBC),
   ("sbfx", SBFX), ("sdiv", SDIV), ("sel", SEL),
   ("setend", SETEND), ("sev", SEV), ("shadd16", SHADD16), ("shadd8", SHADD8),
   ("shasx", SHASX), ("shsax", SHSAX), ("shsub16", SHSUB16),
   ("shsub8", SHSUB8), ("smc", SMC), ("smlabb", SMLABB), ("smlabt", SMLABT),
   ("smlatb", SMLATB), ("smlatt", SMLATT),
   ("smlad", SMLAD), ("smladx", SMLADX), ("smlal", SMLAL), ("smlalbb", SMLALBB),
   ("smlalbt", SMLALBT), ("smlaltb", SMLALTB), ("smlaltt", SMLALTT),
   ("smlald", SMLALD), ("smlaldx", SMLALDX),
   ("smlawb", SMLAWB), ("smlawt", SMLAWT),
   ("smlsd", SMLSD), ("smlsdx", SMLSDX), ("smlsld", SMLSLD),
   ("smlsldx", SMLSLDX), ("smmla", SMMLA), ("smmlar", SMMLAR), ("smmls", SMMLS),
   ("smmlsr", SMMLSR), ("smmul", SMMUL), ("smmulr", SMMULR), ("smuad", SMUAD),
   ("smuadx", SMUADX), ("smulbb", SMULBB),
   ("smulbt", SMULBT), ("smultb", SMULTB), ("smultt", SMULTT), ("smull", SMULL),
   ("smulwb", SMULWB), ("smulwt", SMULWT), ("smusd", SMUSD), ("smusdx", SMUSDX),
   ("srs", SRSIA), ("srsia", SRSIA), ("srsda", SRSDA), ("srsdb", SRSDB),
   ("srsib", SRSIB), ("ssat", SSAT), ("ssat16", SSAT16), ("ssax", SSAX),
   ("ssub16", SSUB16), ("ssub8", SSUB8), ("stc", STC), ("stcl", STCL),
   ("stc2", STC2), ("stc2l", STC2L),
   ("stm", STMIA), ("stmia", STMIA), ("stmea", STMIA),
   ("stmda", STMDA), ("stmed", STMDA),
   ("stmdb", STMDB), ("stmfd", STMDB),
   ("stmib", STMIB), ("stmfa", STMIB),
   ("str", STR), ("strb", STRB),
   ("strbt", STRBT), ("strd", STRD), ("strex", STREX), ("strexb", STREXB),
   ("strexd", STREXD), ("strexh", STREXH), ("strh", STRH),
   ("strht", STRHT), ("strt", STRT), ("sub", SUB), ("subw", SUBW),
   ("svc", SVC), ("swp", SWP), ("swpb", SWPB), ("sxtab", SXTAB),
   ("sxtab16", SXTAB16), ("sxtah", SXTAH), ("sxtb", SXTB), ("sxtb16", SXTB16),
   ("sxth", SXTH),
   ("tbb", TBB), ("tbh", TBH), ("teq", TEQ), ("tst", TST),
   ("uadd16", UADD16), ("uadd8", UADD8), ("uasx", UASX), ("ubfx", UBFX),
   ("udiv", UDIV), ("uhadd16", UHADD16), ("uhadd8", UHADD8),
   ("uhasx", UHASX), ("uhsax", UHSAX), ("uhsub16", UHSUB16),
   ("uhsub8", UHSUB8), ("umaal", UMAAL), ("umlal", UMLAL), ("umull", UMULL),
   ("uqadd16", UQADD16), ("uqadd8", UQADD8), ("uqasx", UQASX),
   ("uqsax", UQSAX), ("uqsub16", UQSUB16), ("uqsub8", UQSUB8), ("usad8", USAD8),
   ("usada8", USADA8), ("usax", USAX), ("usat", USAT), ("usat16", USAT16),
   ("usub16", USUB16), ("usub8", USUB8), ("uxtab", UXTAB),
   ("uxtab16", UXTAB16), ("uxtah", UXTAH),
   ("uxtb", UXTB), ("uxtb16", UXTB16), ("uxth", UXTH),
   ("wfe", WFE), ("wfi", WFI),
   ("yield", YIELD)];

  fun mnemonic_compare ((x,_),(y,_)) =
        Int.compare (String.size y, String.size x)

  val mnemonic_strings = Listsort.sort mnemonic_compare mnemonic_strings
in
  fun find_mnemonic s =
    let fun find_prefix [] = NONE
          | find_prefix ((l,r)::t) =
              if Substring.isPrefix l s andalso
                 (l <> "bl" orelse Lib.mem (Substring.size s) [2, 4])
              then
                SOME (Substring.triml (String.size l) s,r)
              else
                find_prefix t
    in
      find_prefix mnemonic_strings
    end
end;

fun condition_to_word4 s =
  mk_word4
    (case s
     of "eq" => 0
      | "ne" => 1
      | "cs" => 2
      | "hs" => 2
      | "cc" => 3
      | "lo" => 3
      | "mi" => 4
      | "pl" => 5
      | "vs" => 6
      | "vc" => 7
      | "hi" => 8
      | "ls" => 9
      | "ge" => 10
      | "lt" => 11
      | "gt" => 12
      | "le" => 13
      | "al" => 14
      | _    => raise ERR "condition_to_word4" (s ^ " is not a condition"));

fun opposite_condition (tm1,tm2) =
let val n1 = uint_of_word tm1
    val n2 = uint_of_word tm2
in
  not (n1 = 14 orelse n2 = 14) andalso
  n1 div 2 = n2 div 2 andalso n1 mod 2 <> n2 mod 2
end;

local
  val condition_strings =
    ["eq","ne","cs","hs","cc","lo","mi","pl","vs",
     "vc","hi","ls","ge","lt","gt","le","al"]
in
  fun find_condition s =
  let fun find_prefix [] = NONE
        | find_prefix (l::t) =
            if Substring.isPrefix l s then
              SOME (l,Substring.triml 2 s)
            else
              find_prefix t
  in
    find_prefix condition_strings
  end
end;

(* ------------------------------------------------------------------------- *)

val has_thumb2 = Lib.C mem [ARMv6T2, ARMv7_A, ARMv7_R];
val has_dsp    = not o Lib.C mem [ARMv4, ARMv4T, ARMv5T];

fun version_number ARMv4   = 4
  | version_number ARMv4T  = 4
  | version_number ARMv5T  = 5
  | version_number ARMv5TE = 5
  | version_number ARMv6   = 6
  | version_number ARMv6K  = 6
  | version_number ARMv6T2 = 6
  | version_number _       = 7;

fun word_aligned (tm1,i) =
  can EQT_ELIM (armSyntax.mk_aligned (tm1,numSyntax.term_of_int i) |> EVAL);

fun word_lower_same (tm1,tm2) =
  can EQT_ELIM (wordsSyntax.mk_word_ls (tm1,tm2) |> EVAL);

fun narrow_register tm =
  type_of tm = ``:word4`` andalso
  (is_var tm orelse word_lower_same (tm,mk_word4 7));

val narrow_registers = Lib.all narrow_register;

val arch_version : int M =
  read_arch >>= (fn arch => return (version_number arch));

val arch_okay : string * string -> (arch -> bool) -> 'a M -> 'a M =
  fn s => fn P => fn f =>
    read_arch >>= (fn arch => assertT (P arch) s f);

val not_narrow : string -> 'a M -> 'a M =
  fn s => fn f =>
    read_qualifier >>= (fn q =>
      assertT (q <> Narrow) (s,"not available as narrow thumb instruction") f);

val thumb2_okay : string -> 'a M -> 'a M =
  fn s => fn f =>
    not_narrow s
    (read_thumb >>= (fn thumb =>
       arch_okay (s,"Thumb2 only")
         (fn a => thumb andalso has_thumb2 a) f));

val thumb2_or_arm_okay : string -> (term -> 'a M) -> 'a M =
  fn s => fn f =>
    read_thumb >>= (fn thumb =>
      if thumb then
        not_narrow s (arch_okay (s,"requires Thumb2") has_thumb2
          (f Encoding_Thumb2_tm))
      else
        f Encoding_ARM_tm);

val thumb_or_arm_okay : (term -> 'a M) -> 'a M =
  fn f =>
    read_thumb >>= (fn thumb =>
      if thumb then
        f Encoding_Thumb_tm
      else
        f Encoding_ARM_tm);

fun need_t2 s =
  arch_okay (s,"requires architecture with Thumb2 support") has_thumb2;

fun need_dsp s =
  arch_okay (s,"requires architecture with DSP support") has_dsp;

fun need_v5 s =
  arch_okay (s,"requires architecture version >= 5")
    (fn a => version_number a >= 5);

fun need_v6 s =
  arch_okay (s,"requires architecture version >= 6")
    (fn a => version_number a >= 6);

fun need_v7 s =
  arch_okay (s,"requires architecture version >= 7")
    (fn a => version_number a >= 7);

(* ------------------------------------------------------------------------- *)

val arm_parse_variable : hol_type -> term M =
  fn ty =>
    read_token >>=
    (fn h =>
       case h
         of NONE   => syntax_errorT ("variable", "end-of-input")
          | SOME s => if variable (Substring.sub (s,0)) then
                        next_token >>- return (mk_var (Substring.string s,ty))
                      else
                        syntax_errorT ("variable", Substring.string s));

fun char_list_to_word4 l x =
  case l
  of [#"0"]       => return (mk_word4 0)
   | [#"1"]       => return (mk_word4 1)
   | [#"2"]       => return (mk_word4 2)
   | [#"3"]       => return (mk_word4 3)
   | [#"4"]       => return (mk_word4 4)
   | [#"5"]       => return (mk_word4 5)
   | [#"6"]       => return (mk_word4 6)
   | [#"7"]       => return (mk_word4 7)
   | [#"8"]       => return (mk_word4 8)
   | [#"9"]       => return (mk_word4 9)
   | [#"1", #"0"] => return (mk_word4 10)
   | [#"1", #"1"] => return (mk_word4 11)
   | [#"1", #"2"] => return (mk_word4 12)
   | [#"1", #"3"] => return (mk_word4 13)
   | [#"1", #"4"] => return (mk_word4 14)
   | [#"1", #"5"] => return (mk_word4 15)
   | _ => syntax_errorT x;

val arm_parse_register : term M =
  read_token >>=
  (fn h =>
     case h
       of NONE   => syntax_errorT ("register", "end-of-input")
        | SOME h => next_token >>-
           (case lower_explode h
            of #"r"::l => char_list_to_word4 l ("register", Substring.string h)
             | [#"s", #"p"] => return (mk_word4 13)
             | [#"l", #"r"] => return (mk_word4 14)
             | [#"p", #"c"] => return (mk_word4 15)
             | _ => syntax_errorT ("register", Substring.string h)));

val arm_parse_coprocessor : term M =
  read_token >>=
  (fn h =>
     case h
       of NONE   => syntax_errorT ("coprocessor", "end-of-input")
        | SOME h => next_token >>-
           (case lower_explode h
            of #"p"::l => char_list_to_word4 l
                            ("coprocessor", Substring.string h)
             | _ => syntax_errorT ("coprocessor", Substring.string h)));

val arm_parse_cregister : term M =
  read_token >>=
  (fn h =>
     case h
       of NONE   => syntax_errorT ("coprocessor register", "end-of-input")
        | SOME h => next_token >>-
           (case lower_explode h
            of #"c"::l => char_list_to_word4 l
                            ("coprocessor register", Substring.string h)
             | _ => syntax_errorT
                            ("coprocessor register", Substring.string h)));

val arm_parse_number : term M =
  read_token >>=
  (fn h =>
     case h
       of NONE   => syntax_errorT ("register", "end-of-input")
        | SOME h => next_token >>-
            let fun number P f l =
                      if Lib.all P l then
                        return (mk_integer (f (implode l)))
                      else
                        syntax_errorT ("number", Substring.string h)
            in
              case Substring.explode h
              of [#"0"] => return intSyntax.zero_tm
               | (#"0"::(#"b"::cs)) =>
                   number isBinDigit Arbnum.fromBinString cs
               | (#"0"::(#"x"::cs)) =>
                   number Char.isHexDigit Arbnum.fromHexString cs
               | #"0"::cs =>
                   number isOctDigit Arbnum.fromOctString cs
               | c::cs =>
                   number Char.isDigit Arbnum.fromString (c::cs)
               | _ => syntax_errorT ("number", Substring.string h)
            end);

val arm_parse_string : string -> unit M =
  fn s =>
    read_token >>=
    (fn h =>
       case h
         of NONE   => syntax_errorT (s, "end-of-input")
          | SOME h => if String.compare (lower_string h, s) = EQUAL then
                        next_token
                      else
                        syntax_errorT (s, Substring.string h));

val arm_parse_hash    = arm_parse_string "#";
val arm_parse_plus    = arm_parse_string "+";
val arm_parse_minus   = arm_parse_string "-";
val arm_parse_comma   = arm_parse_string ",";
val arm_parse_lbrace  = arm_parse_string "{";
val arm_parse_rbrace  = arm_parse_string "}";
val arm_parse_lsquare = arm_parse_string "[";
val arm_parse_rsquare = arm_parse_string "]";
val arm_parse_exclaim = arm_parse_string "!";
val arm_parse_colon   = arm_parse_string ":";
val arm_parse_hat     = arm_parse_string "^";

val arm_parse_strings : string list -> string M =
  fn l =>
    read_token >>=
    (fn h =>
       case h
         of NONE   => syntax_errorT (quote (String.concat (Lib.commafy l)),
                                     "end-of-input")
          | SOME h => let val s = lower_string h in
                        if mem s l then
                          next_token >>- return s
                        else
                          syntax_errorT
                            ("``" ^ (String.concat (Lib.commafy l) ^ "``"),
                             Substring.string h)
                      end);

val arm_parse_string_const : string M =
  read_token >>=
  (fn h =>
     case h
       of NONE   => syntax_errorT ("string", "end-of-input")
        | SOME h => let val s = Substring.size h in
                      if s >= 2 andalso
                         Substring.sub (h,0) = #"\"" andalso
                         Substring.sub (h,s - 1) = #"\""
                      then
                        next_token >>-
                          return
                            (Substring.string (h |> Substring.triml 1
                                                 |> Substring.trimr 1))
                      else
                        syntax_errorT ("string", Substring.string h)
                    end);

val arm_parse_endline : unit M =
  read_token >>=
  (fn h =>
     case h
       of NONE   => return ()
        | SOME h => if Substring.compare (Substring.full "\n", h) = EQUAL then
                      next_token >>- next_linenumber
                    else
                      syntax_errorT
                        ("newline or end-of-input", Substring.string h));

val arm_parse_endoffile : bool M =
  read_token >>= (fn h => return (not (isSome h)));

val arm_parse_plus_minus : bool M =
  tryT arm_parse_plus  (fn _ => return true) (fn _ =>
  tryT arm_parse_minus (fn _ => return false)
                       (fn _ => return true));

val arm_parse_signed_number : term M =
  arm_parse_plus_minus >>=
  (fn pos =>
     arm_parse_number >>=
     (fn i => return (if pos then i else intSyntax.mk_negated i)));

val arm_parse_constant : term M =
  arm_parse_hash >>- arm_parse_signed_number;

val arm_parse_branch_offset : term M =
  tryT arm_parse_plus
    (fn _ => arm_parse_hash >>- arm_parse_number >>= return)
    (fn _ => tryT arm_parse_minus
       (fn _ => arm_parse_hash >>- arm_parse_number >>=
          (return o intSyntax.mk_negated))
       (fn _ => arm_parse_variable ``:int``));

(* ------------------------------------------------------------------------- *)

local
  val has_sflags =
    [AND,EOR,ADC,SBC,ORR,BIC,ADD,SUB,RSB,RSC,MOV,MVN,ORN,
     LSL,LSR,ASR,ROR,RRX,MUL]

  val arm_only_sflags = [MLA,UMULL,UMLAL,SMULL,SMLAL]
in
  val arm_parse_sflag : instruction_mnemonic -> term M =
    fn m =>
      read_token >>=
      (fn t =>
         case t
         of NONE => return F
          | SOME h =>
               read_thumb >>=
               (fn thumb =>
                  if (mem m has_sflags orelse not thumb andalso
                      mem m arm_only_sflags) andalso Substring.isPrefix "s" h
                  then
                    write_token (Substring.triml 1 h) >>- return T
                  else
                    return (mk_bool (mem m [TST,CMN,TEQ,CMP]))))
end;

local
  fun then_else s =
    let val (te,r) = Substring.splitl (fn c => c = #"t" orelse c = #"e") s
        val lte = Substring.explode te
    in
      (true::(List.map (fn c => case c of #"t" => true | _ => false) lte), r)
    end
in
  val arm_parse_it_conditions : unit M =
        read_InITBlock >>= (fn InITBlock =>
          assertT (not InITBlock)
            ("arm_parse_it_conditions",
             "IT instruction not allowed in IT block")
            (read_token >>=
             (fn t =>
                case t
                of NONE => return ()
                 | SOME h =>
                     let val (te,r) = then_else h in
                       assertT (length te <= 4)
                         ("arm_parse_it_conditions", "unknown mnemonic")
                         (write_token r >>- write_itlist te)
                     end)))
end;

local
  val coproc2 = [CDP2, STC2, STC2L, LDC2, LDC2L, MRC2, MRRC2, MCR2, MCRR2]

  val is_unconditional = not o (Lib.C mem
        ([PLI, CLREX, DSB, DMB, ISB, PLD, PLDW,
          SRSIA, SRSDA, SRSDB, SRSIB,
          RFEIA, RFEDA, RFEDB, RFEIB,
          SETEND, CPS, CPSIE, CPSID] @ coproc2))

  val is_thumb_unconditional = not o (Lib.C mem [SETEND, CPS, CBZ, CBNZ, IT])
in
  val arm_parse_condition : instruction_mnemonic -> term M =
    fn m =>
      read_token >>=
      (fn t =>
         case t
         of NONE => return (mk_word4 14)
          | SOME h =>
             read_thumb >>= (fn thumb =>
               case find_condition h
               of SOME (s,r) =>
                   if thumb then
                     read_arch >>= (fn arch =>
                     read_itstate >>= (fn (itcond,l) =>
                     let val outside = null l in
                       assertT
                         (s = "al" orelse m = B orelse
                          has_thumb2 arch andalso
                          is_thumb_unconditional m andalso not outside)
                         ("arm_parse_condition",
                          "condition suffix not allowed or outside IT block")
                         (let val cond = condition_to_word4 s
                              val cond' = if m = B andalso not outside orelse
                                             mem m coproc2
                                          then
                                            mk_var (s,``:word4``)
                                          else
                                            cond
                          in
                            assertT
                              (outside orelse
                               (m <> B orelse length l = 1) andalso
                               if hd l then
                                 itcond ~~ cond
                               else
                                 opposite_condition (itcond,cond))
                              ("arm_parse_condition",
                               "wrong condition in IT block or branch not\
                               \ last in IT block")
                              (write_token r >>- return cond')
                          end)
                     end))
                   else
                     assertT
                       (s = "al" orelse m <> BKPT andalso is_unconditional m)
                       ("arm_parse_condition", "condition suffix not allowed")
                       (write_token r >>- return (condition_to_word4 s))
                | NONE =>
                    if thumb then
                      read_itstate >>= (fn (itcond,l) =>
                         assertT (null l orelse hd l andalso is_AL itcond)
                           ("arm_parse_condition",
                            "condition suffix missing in IT block")
                           (return
                              (mk_word4 (if mem m coproc2 then 15 else 14))))
                    else
                      return
                        (mk_word4 (if is_unconditional m then 14 else 15))))
end;

val arm_parse_qualifier : instruction_mnemonic -> qualifier M =
  fn m =>
    read_token >>=
    (fn t =>
       case t
       of NONE => return Either
        | SOME h =>
            (read_arch  >>= (fn arch =>
             read_thumb >>= (fn thumb =>
               if Substring.compare (Substring.full "", h) = EQUAL then
                 next_token >>-
                 return (if thumb andalso m <> BL then
                           if m <> BLX andalso not (has_thumb2 arch) then
                             Narrow
                           else
                             Either
                         else
                           Wide)
               else if not (thumb andalso has_thumb2 arch) then
                 other_errorT ("arm_parse_qualifier",
                   "unexpected trailing characters: " ^ Substring.string h)
               else if Substring.compare (Substring.full ".n", h) = EQUAL then
                 next_token >>-return Narrow
               else if Substring.compare (Substring.full ".w", h) = EQUAL then
                 next_token >>- return Wide
               else
                 other_errorT ("arm_parse_qualifier",
                   "unexpected trailing characters: " ^ Substring.string h)))));

val arm_parse_mnemonic : instruction_mnemonic M =
  read_token >>=
  (fn t =>
     case t
     of NONE => syntax_errorT ("mnemonic", "end-of-input")
      | SOME h =>
          let val lh = lower_substring h in
            case find_mnemonic lh
            of SOME (r,M) =>
                (write_token r >>-
                 (if M = IT then
                    arm_parse_it_conditions >>-
                    arm_parse_string "" >>-
                    write_instruction
                      (SOME {sflag = F, cond = mk_word4 14,
                             qual = Narrow, mnemonic = M}) >>-
                      return M
                  else
                    arm_parse_sflag M >>= (fn sflag =>
                    arm_parse_condition M >>= (fn cond =>
                    arm_parse_qualifier M >>= (fn qual =>
                      let val i = {sflag = sflag, cond = cond,
                                   qual = qual, mnemonic = M}
                      in
                        write_instruction (SOME i) >>- return M
                      end)))))
             | NONE => syntax_errorT ("mnemonic", Substring.string h)
          end);

(* ------------------------------------------------------------------------- *)

fun pick_enc_ee thumb narrow_okay ee =
  if thumb then
    if narrow_okay then
      if ee then
        Encoding_ThumbEE_tm
      else
        Encoding_Thumb_tm
    else
      Encoding_Thumb2_tm
  else
    Encoding_ARM_tm;

fun pick_enc thumb narrow_okay =
  if thumb then
    if narrow_okay then
      Encoding_Thumb_tm
    else
      Encoding_Thumb2_tm
  else
    Encoding_ARM_tm;

fun pick_var_enc thumb q narrow_okay =
  if thumb then
    case q
    of Narrow => Encoding_Thumb_tm
     | Wide   => Encoding_Thumb2_tm
     | Either => if narrow_okay then
                   genvar ``:Encoding``
                 else
                   Encoding_Thumb2_tm
  else
    Encoding_ARM_tm;

(* ------------------------------------------------------------------------- *)

fun dp_opcode AND = mk_word4 0
  | dp_opcode EOR = mk_word4 1
  | dp_opcode SUB = mk_word4 2
  | dp_opcode RSB = mk_word4 3
  | dp_opcode ADD = mk_word4 4
  | dp_opcode ADC = mk_word4 5
  | dp_opcode SBC = mk_word4 6
  | dp_opcode RSC = mk_word4 7
  | dp_opcode TST = mk_word4 8
  | dp_opcode TEQ = mk_word4 9
  | dp_opcode CMP = mk_word4 10
  | dp_opcode CMN = mk_word4 11
  | dp_opcode ORR = mk_word4 12
  | dp_opcode MOV = mk_word4 13
  | dp_opcode BIC = mk_word4 14
  | dp_opcode MVN = mk_word4 15
  | dp_opcode ORN = mk_word4 15
  | dp_opcode _   = raise ERR "dp_opcode" "";

fun swap_opcode m =
  case m
    of ADD => SUB | SUB => ADD
     | ADC => SBC | SBC => ADC
     | CMN => CMP | CMP => CMN
     | MOV => MVN | MVN => MOV
     | BIC => AND | AND => BIC
     | _   => raise ERR "swap_opcode" "cannot swap opcode";

fun int_one_comp tm =
  intSyntax.mk_negated (intSyntax.mk_plus (tm, intSyntax.one_tm));

fun mode1_immediate1 thumb m i =
  if thumb then
    (dp_opcode m,int_to_thumb2_mode1_immediate i)
    handle HOL_ERR {message,origin_function,...} =>
      (dp_opcode (swap_opcode m),int_to_thumb2_mode1_immediate (int_one_comp i))
         handle HOL_ERR _ => raise ERR origin_function message
  else
    (dp_opcode m,int_to_mode1_immediate i)
    handle HOL_ERR {message,origin_function,...} =>
      (dp_opcode (swap_opcode m),int_to_mode1_immediate (int_one_comp i))
         handle HOL_ERR _ => raise ERR origin_function message;

fun mode1_immediate2 thumb m i =
  if thumb then
    (dp_opcode m,int_to_thumb2_mode1_immediate i)
    handle HOL_ERR {message,origin_function,...} =>
      (dp_opcode (swap_opcode m),
       int_to_thumb2_mode1_immediate (intSyntax.mk_negated i))
         handle HOL_ERR _ => raise ERR origin_function message
  else
    (dp_opcode m,int_to_mode1_immediate i)
    handle HOL_ERR {message,origin_function,...} =>
      (dp_opcode (swap_opcode m),
       int_to_mode1_immediate (intSyntax.mk_negated i))
         handle HOL_ERR _ => raise ERR origin_function message;

fun mode1_register rm = mk_Mode1_register (mk_word5 0,mk_word2 0,rm);

fun is_mode1_register mode1 =
  is_Mode1_register mode1 andalso
  let val (sh,typ,_) = dest_Mode1_register mode1 in
    sh ~~ mk_word5 0 andalso typ ~~ mk_word2 0
  end;

fun shift_to_word2 LSL_shift = mk_word2 0
  | shift_to_word2 LSR_shift = mk_word2 1
  | shift_to_word2 ASR_shift = mk_word2 2
  | shift_to_word2 ROR_shift = mk_word2 3
  | shift_to_word2 RRX_shift = mk_word2 3;

fun shift_type LSL = shift_to_word2 LSL_shift
  | shift_type ASR = shift_to_word2 ASR_shift
  | shift_type LSR = shift_to_word2 LSR_shift
  | shift_type ROR = shift_to_word2 ROR_shift
  | shift_type RRX = shift_to_word2 RRX_shift
  | shift_type _ = raise ERR "shift_type" "";

val arm_parse_shift : shift M =
  read_token >>=
  (fn h =>
     case h
     of NONE => syntax_errorT ("shift", "end-of-input")
      | SOME s =>
         (next_token >>-
          (case lower_string s
           of "asr" => return ASR_shift
            | "lsl" => return LSL_shift
            | "lsr" => return LSR_shift
            | "ror" => return ROR_shift
            | "rrx" => return RRX_shift
            | _     => syntax_errorT ("shift",Substring.string s))));

val arm_parse_mode1_shift : term -> term M =
  fn rm =>
    arm_parse_shift >>= (fn s =>
      let val stype = shift_to_word2 s
          val szero = mk_word5 0
      in
        if s = RRX_shift then
          return (mk_Mode1_register (szero,stype,rm))
        else
          tryT arm_parse_constant
            (fn i =>
               let val shift32 = i ~~ ``32i``
                   val imm5 = if shift32 then
                                szero
                              else
                                uint_to_word ``:5`` i
                   val stype = if not shift32 andalso imm5 ~~ szero then
                                 mk_word2 0
                               else
                                 stype
               in
                 assertT (not shift32 orelse mem s [LSR_shift,ASR_shift])
                   ("arm_parse_mode1_shift", "cannot shift by 32")
                   (return (mk_Mode1_register (imm5,stype,rm)))
               end handle HOL_ERR {message,...} =>
                 other_errorT ("arm_parse_mode1_shift", message))
            (fn _ =>
               arm_parse_register >>= (fn rs =>
                 return (mk_Mode1_register_shifted_register (rs,stype,rm))))
      end);

val arm_parse_comma_mode1_shift : term -> term M =
  fn rm =>
    tryT arm_parse_comma
      (fn _ => arm_parse_mode1_shift rm)
      (fn _ => return (mode1_register rm));

fun assertT_thumb s q narrow_okay wide_okay f =
  assertT (case q
           of Narrow => narrow_okay
            | Either => narrow_okay orelse wide_okay
            | Wide   => wide_okay)
     (s,"not a valid Thumb instruction") f;

(* ....................................................................... *)

fun add_sub_literal m (rd,i) =
  read_thumb >>= (fn thumb =>
    if thumb then
      read_qualifier >>= (fn q =>
        let val v = sint_of_term i
            val imm12 = mk_word12 (Int.abs v)
            val narrow_okay = q <> Wide andalso narrow_register rd andalso
                              v mod 4 = 0 andalso
                              if m = ADD then
                                0 <= v andalso v <= 1020
                              else
                                ~1020 <= v andalso v <= 0
            val wide_okay = ~4095 <= v andalso v <= 4095
            val add = narrow_okay orelse
                      if 0 <= v andalso not (i ~~ ``-0i``) then
                        m = ADD
                      else
                        m <> ADD
        in
          assertT_thumb "add_sub_literal" q narrow_okay wide_okay
            (return (pick_enc true narrow_okay,
               mk_Add_Sub (mk_bool add,mk_word4 15,rd,imm12)))
        end handle HOL_ERR {message,...} =>
              other_errorT ("arm_parse_add_sub", message))
    else
      let val (opc,imm12) = mode1_immediate2 false m i in
        return (Encoding_ARM_tm,
          mk_Add_Sub (mk_bool (opc ~~ mk_word4 4),mk_word4 15,rd,imm12))
      end handle HOL_ERR {message,...} =>
            other_errorT ("arm_parse_add_sub", message));

fun narrow_okay_imm m i (rd,rn) =
let val v = sint_of_term i handle HOL_ERR _ => 1024 in
  if m = ADD orelse m = SUB then
    if is_SP rn then
      v mod 4 = 0 andalso
      if is_SP rd then
        ~508 <= v andalso v <= 508
      else
        narrow_register rd andalso ~1020 <= v andalso v <= 1020 andalso
        fst (mode1_immediate2 false m i) ~~ dp_opcode ADD
    else
      narrow_register rn andalso
      if rd ~~ rn then
        ~255 <= v andalso v <= 255
      else
        ~7 <= v andalso v <= 7
  else
    m = RSB andalso v = 0 andalso narrow_registers [rd,rn]
end

fun narrow_okay_reg m q sflag has_thumb2 InITBlock OutsideOrLastInITBlock
                    (rd,rn,rm,mode1) =
  q <> Wide andalso
  is_mode1_register mode1 andalso
  (case m
   of ADD => if narrow_registers [rd,rn] then
               sflag = not InITBlock andalso narrow_register rm orelse
               not sflag andalso rd ~~ rn andalso
               (not (narrow_register rm) orelse has_thumb2)
             else
               not sflag andalso rd ~~ rn andalso
               (not (is_PC rd) orelse OutsideOrLastInITBlock)
    | SUB => sflag = not InITBlock andalso narrow_registers [rd,rn,rm]
    | RSC => false
    | RSB => false
    | ORN => false
    | _   => sflag = not InITBlock andalso rd ~~ rn andalso
             narrow_registers [rn,rm]);

fun wide_okay_reg m mode1 =
  m <> RSC andalso not (is_Mode1_register_shifted_register mode1);

fun data_processing_immediate m (rd,rn,i) =
  read_sflag >>= (fn sflag =>
    if (m = ADD orelse m = SUB) andalso is_F sflag andalso is_PC rn then
      add_sub_literal m (rd,i)
    else
      read_thumb >>= (fn thumb =>
        if thumb then
          read_qualifier >>= (fn q =>
          read_InITBlock >>= (fn InITBlock =>
            let val thumb_sflag = mk_bool (not InITBlock andalso
                                           not (is_SP rn))
                val narrow_okay = q <> Wide andalso thumb_sflag ~~ sflag
                                    andalso narrow_okay_imm m i (rd,rn)
                val enc = pick_enc true narrow_okay
                val (opc,imm12) =
                       mode1_immediate2 (enc ~~ Encoding_Thumb2_tm) m i
            in
              assertT_thumb "data_processing_immediate" q narrow_okay (m <> RSC)
                (return (enc,
                   mk_Data_Processing
                     (opc,sflag,rn,rd,mk_Mode1_immediate imm12)))
            end handle HOL_ERR {message,...} =>
              other_errorT ("data_processing_immediate", message)))
        else
          assertT (m <> ORN)
            ("data_processing_immediate", "not a valid ARM instruction")
            (let val (opc,imm12) = mode1_immediate2 false m i in
              return (Encoding_ARM_tm,
                mk_Data_Processing (opc,sflag,rn,rd,mk_Mode1_immediate imm12))
             end)));

fun data_processing_register m (rd,rn,rm,mode1) =
  read_thumb >>= (fn thumb =>
  read_sflag >>= (fn sflag =>
    if thumb then
      read_arch >>= (fn arch =>
      read_qualifier >>= (fn q =>
      read_InITBlock >>= (fn InITBlock =>
      read_OutsideOrLastInITBlock >>= (fn OutsideOrLastInITBlock =>
        let val mode1'      = mode1_register rn
            val thumb_test  = narrow_okay_reg m q (is_T sflag) (has_thumb2 arch)
                                InITBlock OutsideOrLastInITBlock
            val narrow_okay = thumb_test (rd,rn,rm,mode1)
            val swap_okay   = not narrow_okay andalso
                              m <> SUB andalso is_mode1_register mode1 andalso
                              thumb_test (rd,rm,rn,mode1')
            val wide_okay   = wide_okay_reg m mode1
            val (mode1,rn)  = if swap_okay then (mode1',rm) else (mode1,rn)
            val narrow_okay = narrow_okay orelse swap_okay
        in
          assertT_thumb "data_processing_register" q narrow_okay wide_okay
            (return (pick_enc true narrow_okay,
               mk_Data_Processing (dp_opcode m,sflag,rn,rd,mode1)))
        end handle HOL_ERR {message,...} =>
              other_errorT ("data_processing_register", message)))))
    else
      assertT (m <> ORN)
        ("data_processing_immediate", "not a valid ARM instruction")
        (return (Encoding_ARM_tm,
           mk_Data_Processing (dp_opcode m,sflag,rn,rd,mode1)))));

fun is_data_processing3 m =
  case m
  of ADD => true | SUB => true | RSB => true | RSC => true | ORN => true
   | AND => true | EOR => true | ADC => true | SBC => true | ORR => true
   | BIC => true | _ => false;

val arm_parse_data_processing3 : instruction_mnemonic -> (term * term) M =
  fn m =>
    arm_parse_register >>= (fn rd =>
    arm_parse_comma >>-
    tryT arm_parse_constant
      (fn i => data_processing_immediate m (rd,rd,i))
      (fn _ =>
         arm_parse_register >>= (fn rn =>
         tryT arm_parse_comma
           (fn _ =>
              tryT arm_parse_constant
                (fn i => data_processing_immediate m (rd,rn,i))
                (fn _ =>
                  tryT arm_parse_register
                    (fn rm =>
                       arm_parse_comma_mode1_shift rm >>= (fn mode1 =>
                           data_processing_register m (rd,rn,rm,mode1)))
                    (fn _ =>
                       (tryT (arm_parse_mode1_shift rn) return
                          (fn _ => return (mode1_register rn))) >>=
                       (fn mode1 =>
                          data_processing_register m (rd,rd,rn,mode1)))))
           (fn _ =>
              data_processing_register m (rd,rd,rn,mode1_register rn)))));

(* ....................................................................... *)

fun narrow_okay_imm m i rdn =
let val v = sint_of_term i handle HOL_ERR _ => 1024 in
  (m = CMP orelse m = MOV) andalso
  0 <= v andalso v <= 255 andalso
  narrow_register rdn
end;

fun narrow_okay_reg m (rdn,rm,mode1) =
  if m = MOV then
    if is_Mode1_register_shifted_register mode1 then
      let val (rs,typ,_) = dest_Mode1_register_shifted_register mode1 in
        rdn ~~ rm andalso narrow_registers [rdn,rs]
      end
    else
      let val (imm5,typ,_) = dest_Mode1_register mode1 in
        if narrow_registers [rdn,rm] then
          typ !~ mk_word2 3
        else
          typ ~~ mk_word2 0 andalso imm5 ~~ mk_word5 0
      end
  else
    m <> TEQ andalso is_mode1_register mode1 andalso narrow_registers [rdn,rm];

fun wide_okay_reg m (rm,mode1) =
  not (is_PC rm) andalso (m = MOV orelse is_Mode1_register mode1);

fun move_test_immediate m (rdn,i) =
  read_thumb >>= (fn thumb =>
  read_sflag >>= (fn sflag =>
    if thumb then
      read_qualifier >>= (fn q =>
      read_InITBlock >>= (fn InITBlock =>
        let val thumb_sflag = mk_bool (not InITBlock orelse
                                       m <> MOV andalso m <> MVN)
            val narrow_okay = q <> Wide andalso thumb_sflag ~~ sflag andalso
                              narrow_okay_imm m i rdn
            val enc = pick_enc true narrow_okay
            val (opc,imm12) = mode1_immediate2 (enc ~~ Encoding_Thumb2_tm) m i
            val r15 = mk_word4 15
            val (rd,rn) = if mem m [MOV,MVN] then (rdn,r15) else (r15,rdn)
        in
          assertT_thumb "move_test_immediate" q narrow_okay true
            (return (enc,
               mk_Data_Processing (opc,sflag,rn,rd,mk_Mode1_immediate imm12)))
        end handle HOL_ERR {message,...} =>
          other_errorT ("data_processing_immediate", message)))
    else
      let val (opc,imm12) = mode1_immediate2 false m i
          val r0 = mk_word4 0
          val (rd,rn) = if m = MOV orelse m = MVN then (rdn,r0) else (r0,rdn)
      in
        return (Encoding_ARM_tm,
          mk_Data_Processing (opc,sflag,rn,rd,mk_Mode1_immediate imm12))
      end));

fun move_test_reg m (rdn,rm,mode1) =
  read_thumb >>= (fn thumb =>
  read_sflag >>= (fn sflag =>
    if thumb then
      read_qualifier >>= (fn q =>
      read_InITBlock >>= (fn InITBlock =>
      read_OutsideOrLastInITBlock >>= (fn OutsideOrLastInITBlock =>
      arch_version >>= (fn version =>
        let val thumb_sflag = mk_bool (m <> MOV andalso m <> MVN orelse
                                       not InITBlock andalso
                                       narrow_registers [rdn,rm] andalso
                                       (m <> MOV orelse version < 6 orelse
                                        is_T sflag))
            val narrow_okay = q <> Wide andalso thumb_sflag ~~ sflag andalso
                              (OutsideOrLastInITBlock orelse not (is_PC rdn))
                              andalso narrow_okay_reg m (rdn,rm,mode1)
            val wide_okay = wide_okay_reg m (rm,mode1)
            val r15 = mk_word4 15
            val (rd,rn) = if mem m [MOV,MVN] then (rdn,r15) else (r15,rdn)
        in
          assertT_thumb "data_processing_register" q narrow_okay wide_okay
            (return (pick_enc true narrow_okay,
               mk_Data_Processing (dp_opcode m,sflag,rn,rd,mode1)))
        end handle HOL_ERR {message,...} =>
              other_errorT ("data_processing_register", message)))))
    else
      let val r0 = mk_word4 0
          val (rd,rn) = if mem m [MOV,MVN] then (rdn,r0) else (r0,rdn)
      in
        return (Encoding_ARM_tm,
          mk_Data_Processing (dp_opcode m,sflag,rn,rd,mode1))
      end));

fun is_data_processing2 m =
  case m
  of MOV => true | CMP => true | TST => true | MVN => true | CMN => true
   | TEQ => true | _ => false;

val arm_parse_data_processing2 : instruction_mnemonic -> (term * term) M =
  fn m =>
    arm_parse_register >>= (fn rdn =>
    arm_parse_comma >>-
    tryT arm_parse_constant
      (fn i => move_test_immediate m (rdn,i))
      (fn _ =>
         arm_parse_register >>= (fn rm =>
         arm_parse_comma_mode1_shift rm >>= (fn mode1 =>
           move_test_reg m (rdn,rm,mode1)))));

(* ....................................................................... *)

fun shift_immediate m thumb q InITBlock sflag (rd,rm,i) =
let val v = sint_of_term i
    val wide_okay = 1 <= v andalso v <= (if mem m [LSR,ASR] then 32 else 31)
    val narrow_okay = q <> Wide andalso wide_okay andalso m <> ROR andalso
                      mk_bool InITBlock !~ sflag andalso
                      narrow_registers [rd,rm]
    val imm5 = mk_word5 (if v = 32 then 0 else Int.abs v)
    val rn = mk_word4 (if thumb then 15 else 0)
in
  assertT wide_okay
    ("shift_immediate",
     "shift must be in range 1-31 (lsl and ror) or 1-32 (lsr and asr)")
    (assertT_thumb "shift_immediate" q narrow_okay wide_okay
      (return (pick_enc thumb narrow_okay,
         mk_Data_Processing (dp_opcode MOV,sflag,rn,rd,
           mk_Mode1_register (imm5,shift_type m,rm)))))
end handle HOL_ERR {message,...} => other_errorT ("shift_immediate", message);

fun shift_register m thumb q InITBlock sflag (rd,rn,rm) =
let val narrow_okay = q <> Wide andalso rd ~~ rn andalso
                      mk_bool InITBlock !~ sflag andalso
                      narrow_registers [rd,rn,rm]
    val rn' = mk_word4 (if thumb then 15 else 0)
in
  assertT_thumb "shift_register" q narrow_okay true
   (return (pick_enc thumb narrow_okay,
      mk_Data_Processing (dp_opcode MOV,sflag,rn',rd,
        mk_Mode1_register_shifted_register (rm,shift_type m,rn))))
end handle HOL_ERR {message,...} => other_errorT ("shift_register", message);

val arm_parse_mov_shift : instruction_mnemonic -> (term * term) M =
  fn m =>
    arm_parse_register >>= (fn rd =>
    arm_parse_comma >>-
    read_thumb >>= (fn thumb =>
    read_qualifier >>= (fn q =>
    read_sflag >>= (fn sflag =>
    read_InITBlock >>= (fn InITBlock =>
    tryT arm_parse_constant
      (fn i => shift_immediate m thumb q InITBlock sflag (rd,rd,i))
      (fn _ =>
         arm_parse_register >>= (fn rn =>
         tryT arm_parse_comma
           (fn _ =>
              tryT arm_parse_constant
                (fn i => shift_immediate m thumb q InITBlock sflag (rd,rn,i))
                (fn _ =>
                   arm_parse_register >>= (fn rm =>
                     shift_register m thumb q InITBlock sflag (rd,rn,rm))))
           (fn _ => shift_register m thumb q InITBlock sflag (rd,rd,rn)))))))));

val arm_parse_rrx : (term * term) M =
  thumb2_or_arm_okay "arm_parse_rrx"
    (fn enc =>
       arm_parse_register >>= (fn rd =>
       tryT arm_parse_comma
         (fn _ => arm_parse_register)
         (fn _ => return rd) >>=
       (fn rm =>
          read_sflag >>= (fn sflag =>
            return (enc,
              mk_Data_Processing (dp_opcode MOV,sflag,mk_word4 0,rd,
                mk_Mode1_register (mk_word5 0,shift_type RRX,rm)))))));

(* ------------------------------------------------------------------------- *)

val arm_parse_mov_halfword : term -> (term * term) M =
  fn high =>
    need_t2 "arm_parse_mov_halfword"
      (thumb2_or_arm_okay "arm_parse_mov_halfword"
        (fn enc =>
           arm_parse_register >>= (fn rd =>
           arm_parse_comma >>-
           arm_parse_constant >>= (fn i =>
           let val imm16 = uint_to_word ``:16`` i in
             return (enc,mk_Move_Halfword (high,rd,imm16))
           end handle HOL_ERR {message,...} =>
             other_errorT ("arm_parse_mov_halfword", message)))));

val arm_parse_addw_subw : term -> (term * term) M =
  fn add =>
    thumb2_okay "arm_parse_addw_subw"
      (arm_parse_register >>= (fn rd =>
       arm_parse_comma >>-
       tryT arm_parse_register
         (fn rn => arm_parse_comma >>- return rn)
         (fn _ => return rd) >>= (fn rn =>
       arm_parse_constant >>= (fn i =>
         let val (add,i) = if intSyntax.is_negated i then
                             (if is_T add then F else T,
                                intSyntax.dest_negated i)
                           else
                             (add,i)
             val imm12 = uint_to_word ``:12`` i
         in
           return (Encoding_Thumb2_tm, mk_Add_Sub (add,rn,rd,imm12))
         end handle HOL_ERR {message,...} =>
           other_errorT ("arm_parse_addw_subw", message)))));

val arm_parse_adr : (term * term) M =
  arm_parse_register >>= (fn rd =>
  arm_parse_comma >>-
  arm_parse_branch_offset >>= (fn i =>
  read_thumb >>= (fn thumb =>
    if is_var i then
      read_qualifier >>= (fn q =>
        return
          (pick_var_enc thumb q (narrow_register rd),
           mk_Add_Sub (boolSyntax.arb,mk_word4 15,rd,cast_var ``:word12`` i)))
    else
      if thumb then
        read_qualifier >>= (fn q =>
          let val offset = sint_of_term i - 4
              val narrow_okay = q <> Wide andalso narrow_register rd andalso
                                offset mod 4 = 0 andalso
                                0 <= offset andalso offset <= 1020
              val wide_okay = q <> Narrow andalso
                              ~4095 <= offset andalso offset <= 4095
          in
            if narrow_okay orelse wide_okay then
              return
                (if narrow_okay then Encoding_Thumb_tm else Encoding_Thumb2_tm,
                 mk_Add_Sub (mk_bool (0 <= offset andalso not (i ~~ ``-0i``)),
                   mk_word4 15,rd,mk_word12 offset))
            else
              other_errorT ("arm_parse_adr",
                 "bad register, unaligned or offset beyond permitted range")
          end handle HOL_ERR {message,...} =>
            other_errorT ("arm_parse_adr", message))
      else
        let open intSyntax
            val offset = eval (mk_minus(i, ``8i``))
            val absoffset = eval (mk_absval offset)
        in
          return (Encoding_ARM_tm,
            mk_Add_Sub (mk_bool (not (is_negated offset)),mk_word4 15,rd,
                        int_to_mode1_immediate absoffset))
        end handle HOL_ERR {message, ...} =>
          other_errorT ("arm_parse_adr", message))));

(* ------------------------------------------------------------------------- *)

val arm_parse_branch_target : (term * term) M =
  arm_parse_branch_offset >>= (fn i =>
  read_thumb >>= (fn thumb =>
  read_qualifier >>= (fn q =>
    if is_var i then
      return (pick_var_enc thumb q true,
        mk_Branch_Target (cast_var ``:word24`` i))
    else
      if thumb then
        read_cond >>= (fn cond =>
          let val offset = sint_of_term i - 4
              val narrow_okay = q <> Wide andalso
                                if is_var cond orelse is_AL cond then
                                  ~2048 <= offset andalso offset <= 2046
                                else
                                  ~256 <= offset andalso offset <= 254
              val wide_okay = if is_var cond orelse is_AL cond then
                                ~16777216 <= offset andalso offset <= 16777214
                              else
                                ~1048576 <= offset andalso offset <= 1048574
          in
            assertT (offset mod 2 = 0)
              ("arm_parse_branch_target",
               "branch offset not half-word aligned")
            (assertT_thumb "arm_parse_branch_target" q narrow_okay wide_okay
              (return (pick_enc true narrow_okay,
                 mk_Branch_Target (offset_to_imm24 (offset div 2)))))
          end handle HOL_ERR {message,...} =>
                other_errorT ("arm_parse_branch_target", message))
      else
        let val offset = sint_of_term i - 8 in
          assertT (offset mod 4 = 0)
            ("arm_parse_branch_target", "branch offset not word aligned")
            (assertT (~33554432 <= offset andalso offset <= 33554428)
               ("arm_parse_branch_target", "offset beyond permitted range")
               (return (Encoding_ARM_tm,
                  mk_Branch_Target (offset_to_imm24 (offset div 4)))))
        end handle HOL_ERR {message,...} =>
          other_errorT ("arm_parse_branch_target", message))));

val arm_parse_branch_link : (term * term) M =
  arm_parse_branch_offset >>= (fn i =>
  read_thumb >>= (fn thumb =>
    if thumb then
      read_OutsideOrLastInITBlock >>= (fn OutsideOrLastInITBlock =>
      read_qualifier >>= (fn q =>
        assertT (q <> Narrow andalso OutsideOrLastInITBlock)
          ("arm_parse_branch_link",
           "must be wide, and outside or last in IT block")
          (if is_var i then
             return (Encoding_Thumb2_tm,
               mk_Branch_Link_Exchange_Immediate
                 (boolSyntax.arb,F,cast_var ``:word24`` i))
           else
             let val offset = sint_of_term i - 4
                 val H = mk_bool ((offset div 2) mod 2 = 1)
             in
               assertT (offset mod 2 = 0)
                 ("arm_parse_branch_target",
                  "branch offset not half-word aligned")
               (assertT (~16777216 <= offset andalso offset <= 16777214)
                 ("arm_parse_branch_target", "offset beyond permitted range")
                 (return (Encoding_Thumb2_tm,
                    mk_Branch_Link_Exchange_Immediate
                      (H,F,offset_to_imm24 (offset div 4)))))
             end handle HOL_ERR {message,...} =>
               other_errorT ("arm_parse_branch_link", message))))
      else
        if is_var i then
          return (Encoding_ARM_tm,
            mk_Branch_Link_Exchange_Immediate
              (boolSyntax.arb,T,cast_var ``:word24`` i))
        else
          let val offset = sint_of_term i - 8 in
            assertT (offset mod 4 = 0)
              ("arm_parse_branch_target", "branch offset not word aligned")
            (assertT (~33554432 <= offset andalso offset <= 33554428)
              ("arm_parse_branch_target", "offset beyond permitted range")
              (return (Encoding_ARM_tm,
                mk_Branch_Link_Exchange_Immediate
                  (F,T,offset_to_imm24 (offset div 4)))))
          end handle HOL_ERR {message,...} =>
            other_errorT ("arm_parse_branch_link", message)));

val arm_parse_branch_link_exchange : (term * term) M =
  need_v5 "arm_parse_branch_link_exchange"
    (tryT arm_parse_register
       (fn rm =>
          read_thumb >>= (fn thumb =>
            if thumb then
              read_OutsideOrLastInITBlock >>= (fn OutsideOrLastInITBlock =>
              read_qualifier >>= (fn q =>
                 assertT (q <> Wide andalso OutsideOrLastInITBlock)
                   ("arm_parse_branch_link_exchange",
                    "must be narrow, and outside or last in IT block")
                   (return (Encoding_Thumb_tm,
                      mk_Branch_Link_Exchange_Register rm))))
            else
              return (Encoding_ARM_tm, mk_Branch_Link_Exchange_Register rm)))
       (fn _ =>
         arm_parse_branch_offset >>= (fn i =>
         read_thumb >>= (fn thumb =>
          if thumb then
            read_OutsideOrLastInITBlock >>= (fn OutsideOrLastInITBlock =>
            read_qualifier >>= (fn q =>
              assertT (q <> Narrow andalso OutsideOrLastInITBlock)
                ("arm_parse_branch_target",
                 "must be wide, and outside or last in IT block")
                (if is_var i then
                   return (Encoding_Thumb2_tm,
                     mk_Branch_Link_Exchange_Immediate
                       (F,T,cast_var ``:word24`` i))
                 else
                   let val offset = sint_of_term i - 4 in
                     assertT (offset mod 4 = 0)
                       ("arm_parse_branch_target",
                        "branch offset not word aligned")
                     (assertT (~16777216 <= offset andalso offset <= 16777212)
                       ("arm_parse_branch_target",
                        "offset beyond permitted range")
                       (return (Encoding_Thumb2_tm,
                          mk_Branch_Link_Exchange_Immediate
                            (F,T,offset_to_imm24 (offset div 4)))))
                   end handle HOL_ERR {message,...} =>
                     other_errorT ("arm_parse_branch_link_exchange", message))))
          else
            read_cond >>= (fn cond =>
              assertT (is_AL cond)
                ("arm_parse_branch_link_exchange", "must be uncoditional")
                (write_cond (mk_word4 15) >>-
                 (if is_var i then
                    return (Encoding_ARM_tm,
                      mk_Branch_Link_Exchange_Immediate
                        (boolSyntax.arb,F,cast_var ``:word24`` i))
                  else
                    let val offset = sint_of_term i - 8
                        val H = mk_bool ((offset div 2) mod 2 = 1)
                    in
                      assertT (offset mod 2 = 0)
                        ("arm_parse_branch_target",
                         "branch offset not half-word aligned")
                      (assertT (~33554432 <= offset andalso offset <= 33554430)
                        ("arm_parse_branch_target",
                         "offset beyond permitted range")
                        (return (Encoding_ARM_tm,
                           mk_Branch_Link_Exchange_Immediate
                             (H,F,offset_to_imm24 (offset div 4)))))
                    end handle HOL_ERR {message,...} =>
                      other_errorT
                        ("arm_parse_branch_link_exchange", message))))))));

val arm_parse_bx : (term * term) M =
  thumb_or_arm_okay (fn enc =>
  arm_parse_register >>= (fn rm =>
  read_OutsideOrLastInITBlock >>= (fn OutsideOrLastInITBlock =>
    assertT (enc ~~ Encoding_ARM_tm orelse OutsideOrLastInITBlock)
      ("arm_parse_bx", "must be outside or last in IT block")
      (return (enc,mk_Branch_Exchange rm)))));

val arm_parse_setend : (term * term) M =
  need_v6 "arm_parse_setend"
    (thumb_or_arm_okay
      (fn enc =>
         tryT (arm_parse_string "be") (K (return T)) (fn _ =>
               arm_parse_string "le" >>- return F) >>= (fn bigend =>
           return (enc,mk_Set_Endianness bigend))));

val arm_parse_cbz_cbnz : term -> (term * term) M =
  fn nonzero =>
    thumb2_okay "arm_parse_cnz"
      (read_qualifier >>= (fn q =>
        assertT (q <> Wide)
          ("arm_parse_cbz_cbnz", "wide version not available")
          (arm_parse_register >>= (fn rn =>
            assertT (narrow_register rn)
              ("arm_parse_cbz_cbnz", "register must be r0-r7")
              (arm_parse_comma >>-
               arm_parse_branch_offset >>= (fn i =>
                 if is_var i then
                   return (Encoding_Thumb_tm,
                     mk_Compare_Branch (nonzero,cast_var ``:word6`` i,
                       mk_word3 (uint_of_word rn)))
                 else
                   let val offset = sint_of_term i - 4 in
                     assertT (offset mod 2 = 0)
                       ("arm_parse_cbz_cbnz", "offset not half-word aligned")
                     (assertT (0 <= offset andalso offset <= 126)
                       ("arm_parse_cbz_cbnz", "offset beyond permitted range")
                       (return (Encoding_Thumb_tm,
                          mk_Compare_Branch (nonzero,
                            mk_word6 (Int.abs (offset div 2)),
                            mk_word3 (uint_of_word rn)))))
                   end handle HOL_ERR {message,...} =>
                     other_errorT ("arm_parse_cbz_cbnz", message)))))));

val arm_parse_clz : (term * term) M =
  need_v5 "arm_parse_clz"
    (thumb2_or_arm_okay "arm_parse_clz"
      (fn enc =>
         arm_parse_register >>= (fn rd =>
         arm_parse_comma >>-
         arm_parse_register >>= (fn rm =>
           return (enc,mk_Count_Leading_Zeroes (rd,rm))))));

val arm_parse_clrex : (term * term) M =
  read_thumb >>= (fn thumb =>
  read_qualifier >>= (fn q =>
    arch_okay ("arm_parse_clrex", "not supported by architecture")
      (fn a => if thumb then
                 q <> Narrow andalso version_number a >= 7
               else
                 a = ARMv6K orelse version_number a >= 7)
      (return (if thumb then Encoding_Thumb2_tm else Encoding_ARM_tm,
               mk_Miscellaneous Clear_Exclusive_tm))));

local
  fun mk_it_mask (cond,l) =
  let val cond0 = wordsSyntax.mk_index (cond,numSyntax.zero_tm) |> eval
      val (c0,nc0) = if is_T cond0 then (1,0) else (0,1)
  in
    mk_word4 (list_to_int
      (case l
         of []                  => [1  , 0  , 0  , 0]
          | [true]              => [c0 , 1  , 0  , 0]
          | [false]             => [nc0, 1  , 0  , 0]
          | [true,true]         => [c0 , c0 , 1  , 0]
          | [false,true]        => [nc0, c0 , 1  , 0]
          | [true,false]        => [c0 , nc0, 1  , 0]
          | [false,false]       => [nc0, nc0, 1  , 0]
          | [true,true,true]    => [c0 , c0 , c0 , 1]
          | [false,true,true]   => [nc0, c0 , c0 , 1]
          | [true,false,true]   => [c0 , nc0, c0 , 1]
          | [false,false,true]  => [nc0, nc0, c0 , 1]
          | [true,true,false]   => [c0 , c0 , nc0, 1]
          | [false,true,false]  => [nc0, c0 , nc0, 1]
          | [true,false,false]  => [c0 , nc0, nc0, 1]
          | [false,false,false] => [nc0, nc0, nc0, 1]
          | _ => raise ERR "mk_it_mask" ""))
  end

  fun is_then "then" = true
    | is_then "t"    = true
    | is_then "else" = false
    | is_then "e"    = false
    | is_then _ = raise ERR "mk_itstate" "unexpected input"

in
  fun calc_itstate (c,s) = let
        val toks = String.tokens (equal #"-") s
        val l = Lib.mapfilter is_then toks
        val itstate =
              case l
              of [] => mk_word8 0
               | (b::t) => let
                    val cond = condition_to_word4 c
                    val mask = mk_it_mask (cond,t)
                    val cond = if b then
                                 cond
                               else
                                 wordsSyntax.mk_word_xor (mk_word4 1,cond)
                  in
                    eval (wordsSyntax.mk_word_concat (cond,mask))
                  end
      in
        uint_of_word itstate
      end

  val arm_parse_it : (term * term) M =
    need_t2 "arm_parse_it"
      (read_thumb >>= (fn thumb =>
       read_qualifier >>= (fn q =>
         assertT (thumb andalso q <> Wide)
           ("arm_parse_it", "only available as narrow thumb instruction")
           (read_token >>=
            (fn h =>
              case h
                of NONE => syntax_errorT ("condition","end-of_input")
                 | SOME s =>
                     case find_condition s
                       of SOME (c,r) =>
                            if Substring.compare (r,Substring.full "") = EQUAL
                            then
                              let val cond = condition_to_word4 c in
                                read_itstate >>= (fn (_,l) =>
                                assertT (not (is_AL cond) orelse Lib.all I l)
                                  ("arm_parse_it",
                                   "Cannot have -else- cases for AL condition")
                                  (write_itcond cond >>-
                                   next_token >>-
                                   tryT arm_parse_exclaim
                                     (K (return boolSyntax.arb))
                                     (K (return Encoding_Thumb_tm)) >>=
                                     (fn enc =>
                                       return (enc,
                                         mk_If_Then
                                           (cond,mk_it_mask (cond,tl l))))))
                              end
                            else
                              syntax_errorT ("condition",Substring.string s)
                        | NONE =>
                            syntax_errorT ("condition",Substring.string s))))));
end;

val arm_parse_tbb : (term * term) M =
  thumb2_okay "arm_parse_tbb"
    (arm_parse_lsquare >>-
     arm_parse_register >>= (fn rn =>
     arm_parse_comma >>-
     arm_parse_register >>= (fn rm =>
     arm_parse_rsquare >>-
     read_OutsideOrLastInITBlock >>= (fn OutsideOrLastInITBlock =>
       assertT OutsideOrLastInITBlock
         ("arm_parse_tbb", "must be outside or last in IT block")
         (return (Encoding_Thumb2_tm,mk_Table_Branch_Byte (rn,F,rm)))))));

val arm_parse_tbh : (term * term) M =
  thumb2_okay "arm_parse_tbb"
    (arm_parse_lsquare >>-
     arm_parse_register >>= (fn rn =>
     arm_parse_comma >>-
     arm_parse_register >>= (fn rm =>
     arm_parse_comma >>-
     arm_parse_string "lsl" >>-
     arm_parse_constant >>= (fn i =>
       let val v = sint_of_term i in
         if v = 1 then
           arm_parse_rsquare >>-
           read_OutsideOrLastInITBlock >>= (fn OutsideOrLastInITBlock =>
           assertT OutsideOrLastInITBlock
             ("arm_parse_tbh", "must be outside or last in IT block")
             (return (Encoding_Thumb2_tm,mk_Table_Branch_Byte (rn,T,rm))))
         else
           syntax_errorT ("#1","#" ^ term_to_string i)
       end handle HOL_ERR {message,...} =>
             other_errorT ("arm_parse_tbh", message)))));

val arm_parse_mul : (term * term) M =
  arm_parse_register >>= (fn rd =>
  arm_parse_comma >>-
  arm_parse_register >>= (fn rn =>
  tryT arm_parse_comma
      (fn _ => arm_parse_register >>= (fn rm => return (rd,rn,rm)))
      (fn _ => return (rd,rd,rn)) >>=
    (fn (rd,rn,rm) =>
       read_thumb >>= (fn thumb =>
       read_sflag >>= (fn sflag =>
         if thumb then
           read_InITBlock >>= (fn InITBlock =>
           read_qualifier >>= (fn q =>
             let val thumb_sflag = mk_bool (not InITBlock)
                 val narrow_okay =
                     q <> Wide andalso thumb_sflag ~~ sflag andalso
                     (rd ~~ rn orelse rd ~~ rm) andalso
                     narrow_registers [rn,rm]
                 val wide_okay = is_F sflag
                 val (rn,rm) = if narrow_okay andalso rd !~ rm
                               then (rm,rn) else (rn,rm)
             in
               assertT_thumb "arm_parse_mul" q narrow_okay wide_okay
                 (return (pick_enc true narrow_okay,
                    mk_Multiply (F,sflag,rd,mk_word4 0,rm,rn)))
             end))
         else
           return
             (Encoding_ARM_tm, mk_Multiply (F,sflag,rd,mk_word4 0,rm,rn)))))));

local
  fun pas SADD16  = (F,Parallel_normal_tm,Parallel_add_16_tm)
    | pas SASX    = (F,Parallel_normal_tm,Parallel_add_sub_exchange_tm)
    | pas SSAX    = (F,Parallel_normal_tm,Parallel_sub_add_exchange_tm)
    | pas SSUB16  = (F,Parallel_normal_tm,Parallel_sub_16_tm)
    | pas SADD8   = (F,Parallel_normal_tm,Parallel_add_8_tm)
    | pas SSUB8   = (F,Parallel_normal_tm,Parallel_sub_8_tm)
    | pas QADD16  = (F,Parallel_saturating_tm,Parallel_add_16_tm)
    | pas QASX    = (F,Parallel_saturating_tm,Parallel_add_sub_exchange_tm)
    | pas QSAX    = (F,Parallel_saturating_tm,Parallel_sub_add_exchange_tm)
    | pas QSUB16  = (F,Parallel_saturating_tm,Parallel_sub_16_tm)
    | pas QADD8   = (F,Parallel_saturating_tm,Parallel_add_8_tm)
    | pas QSUB8   = (F,Parallel_saturating_tm,Parallel_sub_8_tm)
    | pas SHADD16 = (F,Parallel_halving_tm,Parallel_add_16_tm)
    | pas SHASX   = (F,Parallel_halving_tm,Parallel_add_sub_exchange_tm)
    | pas SHSAX   = (F,Parallel_halving_tm,Parallel_sub_add_exchange_tm)
    | pas SHSUB16 = (F,Parallel_halving_tm,Parallel_sub_16_tm)
    | pas SHADD8  = (F,Parallel_halving_tm,Parallel_add_8_tm)
    | pas SHSUB8  = (F,Parallel_halving_tm,Parallel_sub_8_tm)
    | pas UADD16  = (T,Parallel_normal_tm,Parallel_add_16_tm)
    | pas UASX    = (T,Parallel_normal_tm,Parallel_add_sub_exchange_tm)
    | pas USAX    = (T,Parallel_normal_tm,Parallel_sub_add_exchange_tm)
    | pas USUB16  = (T,Parallel_normal_tm,Parallel_sub_16_tm)
    | pas UADD8   = (T,Parallel_normal_tm,Parallel_add_8_tm)
    | pas USUB8   = (T,Parallel_normal_tm,Parallel_sub_8_tm)
    | pas UQADD16 = (T,Parallel_saturating_tm,Parallel_add_16_tm)
    | pas UQASX   = (T,Parallel_saturating_tm,Parallel_add_sub_exchange_tm)
    | pas UQSAX   = (T,Parallel_saturating_tm,Parallel_sub_add_exchange_tm)
    | pas UQSUB16 = (T,Parallel_saturating_tm,Parallel_sub_16_tm)
    | pas UQADD8  = (T,Parallel_saturating_tm,Parallel_add_8_tm)
    | pas UQSUB8  = (T,Parallel_saturating_tm,Parallel_sub_8_tm)
    | pas UHADD16 = (T,Parallel_halving_tm,Parallel_add_16_tm)
    | pas UHASX   = (T,Parallel_halving_tm,Parallel_add_sub_exchange_tm)
    | pas UHSAX   = (T,Parallel_halving_tm,Parallel_sub_add_exchange_tm)
    | pas UHSUB16 = (T,Parallel_halving_tm,Parallel_sub_16_tm)
    | pas UHADD8  = (T,Parallel_halving_tm,Parallel_add_8_tm)
    | pas UHSUB8  = (T,Parallel_halving_tm,Parallel_sub_8_tm)
    | pas _       = raise ERR "pas" "unknown mnemonic"
in
  val is_par_add_sub = Lib.can pas

  fun is_thumb2_3 m = is_par_add_sub m orelse mem m
    [SMULBB, SMULBT, SMULTB, SMULTT, SMULWB, SMULWT, SMUAD,
     SMUADX, SMUSD, SMUSDX, SMMUL, SMMULR, SEL, USAD8,
     QADD, QSUB, QDADD, QDSUB];

  val is_thumb2_4 = Lib.C mem
    [MLA, MLS, UMULL, UMLAL, SMULL, SMLAL, UMAAL, SMLABB, SMLABT, SMLATB,
     SMLATT, SMLAWB, SMLAWT, SMLALBB, SMLALBT, SMLALTB, SMLALTT, SMLAD,
     SMLADX, SMLSD, SMLSDX, SMLALD, SMLALDX, SMLSLD, SMLSLDX, SMMLA, SMMLAR,
     SMMLS, SMMLSR, USADA8];

  fun par_add_sub m =
    let val (u,t1,t2) = pas m in (u, pairSyntax.mk_pair (t1,t2)) end
end;

val arm_parse_thumb2_3 : (term * term) M =
  thumb2_or_arm_okay "arm_parse_thumb2_3"
   (fn enc =>
    arm_parse_register >>= (fn rd =>
    arm_parse_comma >>-
    arm_parse_register >>= (fn rn =>
    tryT arm_parse_comma
       (fn _ => arm_parse_register >>= (fn rm => return (rd,rn,rm)))
       (fn _ => return (rd,rd,rn)) >>= (fn (rd,rn,rm) =>
    read_mnemonic >>= (fn m =>
      let val r0  = mk_word4 0
          val r15 = mk_word4 15
          fun v6 (tm:term) = need_v6 "arm_parse_thumb2_3" (return (enc,tm))
          fun dsp (tm:term) = need_dsp "arm_parse_thumb2_3" (return (enc,tm))
          val return_mk_shm = dsp o mk_Signed_Halfword_Multiply
          fun return_mk_pas () =
                 let val (u,opc) = par_add_sub m in
                   v6 (mk_Parallel_Add_Subtract (u,opc,rn,rd,rm))
                 end
      in
        case m
        of SMULBB => return_mk_shm (mk_word2 3,F,F,rd,r0,rm,rn)
         | SMULTB => return_mk_shm (mk_word2 3,F,T,rd,r0,rm,rn)
         | SMULBT => return_mk_shm (mk_word2 3,T,F,rd,r0,rm,rn)
         | SMULTT => return_mk_shm (mk_word2 3,T,T,rd,r0,rm,rn)
         | SMULWB => return_mk_shm (mk_word2 1,F,T,rd,r0,rm,rn)
         | SMULWT => return_mk_shm (mk_word2 1,T,T,rd,r0,rm,rn)
         | SMUAD  => v6 (mk_Signed_Multiply_Dual (rd,r15,rm,F,F,rn))
         | SMUADX => v6 (mk_Signed_Multiply_Dual (rd,r15,rm,F,T,rn))
         | SMUSD  => v6 (mk_Signed_Multiply_Dual (rd,r15,rm,T,F,rn))
         | SMUSDX => v6 (mk_Signed_Multiply_Dual (rd,r15,rm,T,T,rn))
         | SMMUL  => v6 (mk_Signed_Most_Significant_Multiply (rd,r15,rm,F,rn))
         | SMMULR => v6 (mk_Signed_Most_Significant_Multiply (rd,r15,rm,T,rn))
         | SEL    => v6 (mk_Select_Bytes (rn,rd,rm))
         | USAD8  => v6 (mk_Unsigned_Sum_Absolute_Differences (rd,r15,rm,rn))
         | QADD   => dsp (mk_Saturating_Add_Subtract (mk_word2 0,rm,rd,rn))
         | QSUB   => dsp (mk_Saturating_Add_Subtract (mk_word2 1,rm,rd,rn))
         | QDADD  => dsp (mk_Saturating_Add_Subtract (mk_word2 2,rm,rd,rn))
         | QDSUB  => dsp (mk_Saturating_Add_Subtract (mk_word2 3,rm,rd,rn))
         | _      => if is_par_add_sub m then return_mk_pas () else
                       raise ERR "arm_parse_thumb2_3" "unknown mnemonic"
      end)))));

val arm_parse_thumb2_4 : (term * term) M =
  thumb2_or_arm_okay "arm_parse_thumb2_4"
   (fn enc =>
    arm_parse_register >>= (fn rd =>
    arm_parse_comma >>-
    arm_parse_register >>= (fn rn =>
    arm_parse_comma >>-
    arm_parse_register >>= (fn rm =>
    arm_parse_comma >>-
    arm_parse_register >>= (fn ra =>
    read_sflag >>= (fn sflag =>
    read_mnemonic >>= (fn m =>
      let fun t2 (tm:term) = need_t2 "arm_parse_thumb2_4" (return (enc,tm))
          fun v6 (tm:term) = need_v6 "arm_parse_thumb2_4" (return (enc,tm))
          fun return_mk_shm x = need_dsp "arm_parse_thumb2_4"
                (return (enc,mk_Signed_Halfword_Multiply x))
      in
        case m
        of MLA     => return (enc,mk_Multiply (T,sflag,rd,ra,rm,rn))
         | MLS     => t2 (mk_Multiply_Subtract (rd,ra,rm,rn))
         | UMULL   => return (enc,mk_Multiply_Long (F,F,sflag,rn,rd,ra,rm))
         | UMLAL   => return (enc,mk_Multiply_Long (F,T,sflag,rn,rd,ra,rm))
         | SMULL   => return (enc,mk_Multiply_Long (T,F,sflag,rn,rd,ra,rm))
         | SMLAL   => return (enc,mk_Multiply_Long (T,T,sflag,rn,rd,ra,rm))
         | UMAAL   => v6 (mk_Multiply_Accumulate_Accumulate (rn,rd,ra,rm))
         | SMLABB  => return_mk_shm (mk_word2 0,F,F,rd,ra,rm,rn)
         | SMLATB  => return_mk_shm (mk_word2 0,F,T,rd,ra,rm,rn)
         | SMLABT  => return_mk_shm (mk_word2 0,T,F,rd,ra,rm,rn)
         | SMLATT  => return_mk_shm (mk_word2 0,T,T,rd,ra,rm,rn)
         | SMLAWB  => return_mk_shm (mk_word2 1,F,F,rd,ra,rm,rn)
         | SMLAWT  => return_mk_shm (mk_word2 1,T,F,rd,ra,rm,rn)
         | SMLALBB => return_mk_shm (mk_word2 2,F,F,rd,ra,rm,rn)
         | SMLALTB => return_mk_shm (mk_word2 2,F,T,rd,ra,rm,rn)
         | SMLALBT => return_mk_shm (mk_word2 2,T,F,rd,ra,rm,rn)
         | SMLALTT => return_mk_shm (mk_word2 2,T,T,rd,ra,rm,rn)
         | SMLAD   => v6 (mk_Signed_Multiply_Dual (rd,ra,rm,F,F,rn))
         | SMLADX  => v6 (mk_Signed_Multiply_Dual (rd,ra,rm,F,T,rn))
         | SMLSD   => v6 (mk_Signed_Multiply_Dual (rd,ra,rm,T,F,rn))
         | SMLSDX  => v6 (mk_Signed_Multiply_Dual (rd,ra,rm,T,T,rn))
         | SMLALD  => v6 (mk_Signed_Multiply_Long_Dual (rn,rd,ra,F,F,rm))
         | SMLALDX => v6 (mk_Signed_Multiply_Long_Dual (rn,rd,ra,F,T,rm))
         | SMLSLD  => v6 (mk_Signed_Multiply_Long_Dual (rn,rd,ra,T,F,rm))
         | SMLSLDX => v6 (mk_Signed_Multiply_Long_Dual (rn,rd,ra,T,T,rm))
         | SMMLA   => v6 (mk_Signed_Most_Significant_Multiply (rd,ra,rm,F,rn))
         | SMMLAR  => v6 (mk_Signed_Most_Significant_Multiply (rd,ra,rm,T,rn))
         | SMMLS   => v6 (mk_Signed_Most_Significant_Multiply_Subtract
                        (rd,ra,rm,F,rn))
         | SMMLSR  => v6 (mk_Signed_Most_Significant_Multiply_Subtract
                        (rd,ra,rm,T,rn))
         | USADA8  => v6 (mk_Unsigned_Sum_Absolute_Differences (rd,ra,rm,rn))
         | _       => raise ERR "arm_parse_thumb2_4" "unknown mnemonic"
      end)))))));

val arm_parse_div : term -> (term * term) M =
  fn u =>
    arch_okay ("arm_parse_div", "only supported by ARMv7-R")
      (curry (op =) ARMv7_R)
      (read_thumb >>= (fn thumb =>
         assertT thumb ("arm_parse_div", "Thumb2 instruction only")
           (arm_parse_register >>= (fn rd =>
            arm_parse_comma >>-
            arm_parse_register >>= (fn rn =>
            tryT arm_parse_comma
              (fn _ => arm_parse_register >>= (fn rm => return (rd,rn,rm)))
              (fn _ => return (rd,rd,rn)) >>=
            (fn (rd,rn,rm) =>
              return (Encoding_Thumb2_tm,mk_Divide (u,rn,rd,rm))))))));

val arm_parse_pkh : term -> (term * term) M =
  fn tbform =>
    thumb2_or_arm_okay "arm_parse_pkh"
      (fn enc =>
         need_v6 "arm_parse_pkh"
         (arm_parse_register >>= (fn rd =>
          arm_parse_comma >>-
          arm_parse_register >>= (fn rn =>
          tryT (arm_parse_comma >>- arm_parse_register)
            (fn rm => return (rd,rn,rm))
            (fn _ => return (rd,rd,rn)) >>=
          (fn (rd,rn,rm) =>
             tryT arm_parse_comma
               (fn _ =>
                  arm_parse_string (if is_T tbform then "asr" else "lsl") >>-
                  arm_parse_constant >>= (fn i =>
                    let val imm5 = if is_T tbform andalso i ~~ ``32i`` then
                                     mk_word5 0
                                   else
                                     uint_to_word ``:5`` i
                    in
                      return (enc,mk_Pack_Halfword (rn,rd,imm5,tbform,rm))
                    end handle HOL_ERR {message,...} =>
                      other_errorT ("arm_parse_pkh", message)))
               (fn _ =>
                 if is_T tbform then
                   return (enc,mk_Pack_Halfword (rm,rd,mk_word5 0,F,rn))
                 else
                   return (enc,mk_Pack_Halfword (rn,rd,mk_word5 0,F,rm))))))));

(* ------------------------------------------------------------------------- *)

val arm_parse_mode2_shift : bool -> qualifier -> term -> term M =
  fn thumb => fn q => fn rm =>
    tryT arm_parse_comma
      (fn _ =>
         arm_parse_shift >>= (fn s =>
         assertT (q <> Narrow andalso (not thumb orelse s = LSL_shift))
           ("arm_parse_mode2_shift", "shift not available")
           (if s = RRX_shift then
              return (mk_Mode2_register (mk_word5 0, shift_to_word2 s, rm))
            else
              arm_parse_constant >>= (fn i =>
                let val v = sint_of_term i
                    val stype = shift_to_word2 (if v = 0 then LSL_shift else s)
                    val imm5 = mk_word5 (if v = 32 then 0 else Int.abs v)
                    val max = if thumb then 3 else
                                if mem s [LSR_shift,ASR_shift] then 32 else 31
                in
                  assertT (0 <= v andalso v <= max)
                    ("arm_parse_mode2_shift", "shift out of range")
                    (return (mk_Mode2_register (imm5, stype, rm)))
                end handle HOL_ERR {message,...} =>
                  other_errorT ("arm_parse_mode2_shift", message)))))
      (fn _ =>
        return (mk_Mode2_register (mk_word5 0, shift_to_word2 LSL_shift, rm)));

val arm_parse_mode2_offset :
  (bool * bool * term * term * term * term) -> (term * term) M =
  fn (ld,indx,byte,unpriv,rt,rn) =>
    read_thumb >>= (fn thumb =>
    read_thumbee >>= (fn thumbee =>
    read_qualifier >>= (fn q =>
    assertT (indx orelse q <> Narrow)
      ("arm_parse_mode2_offset",
       "post indexing not possible for narrow Thumb instruction")
      (tryT arm_parse_constant
        (fn i =>
          (if indx then
             arm_parse_rsquare >>-
             tryT arm_parse_exclaim (K (return T)) (K (return F))
           else
             return (mk_bool (thumb orelse not thumb andalso is_T unpriv))) >>=
          (fn w =>
             let val v = sint_of_term i
                 val u = mk_bool (0 <= v andalso not (i ~~ ``-0i``))
                 val thumbee_okay = thumbee andalso q <> Wide andalso
                                    narrow_register rt andalso is_F byte andalso
                                    is_F w andalso v mod 4 = 0 andalso
                                    if ld then
                                      is_R9 rn andalso 0 <= v andalso v <= 252
                                        orelse
                                      is_R10 rn andalso 0 <= v andalso v <= 124
                                        orelse
                                      narrow_register rn andalso ~28 <= v
                                       andalso v <= 124
                                    else
                                      0 <= v andalso
                                      (is_R9 rn andalso v <= 252 orelse
                                       narrow_register rn andalso v <= 124)
                 val narrow_okay = q <> Wide andalso narrow_register rt andalso
                                   is_F w andalso 0 <= v andalso
                                   if is_T byte then
                                     narrow_register rn andalso v <= 31
                                   else
                                     v mod 4 = 0 andalso
                                     if is_SP rn orelse ld andalso is_PC rn
                                     then
                                       is_F byte andalso v <= 1020
                                     else
                                       narrow_register rn andalso v <= 124
                 val narrow_or_thumbee = thumbee_okay orelse narrow_okay
                 val wide_okay = ~255 <= v andalso
                                 if indx andalso is_T u andalso is_F w then
                                   v <= 4095
                                 else
                                   v <= 255 andalso not (is_T byte andalso
                                     is_PC rt andalso indx andalso is_F u
                                     andalso is_F w)
                 val arm_okay = ~4095 <= v andalso v <= 4095
                 val imm12 = mk_word12 (Int.abs v)
             in
               assertT
                 (q = Narrow andalso narrow_or_thumbee orelse
                  q <> Narrow andalso thumb andalso wide_okay orelse
                  not thumb andalso arm_okay)
                 ("arm_parse_mode2_offset",
                  "invalid argument(s) (check registers, alignment and range)")
                 (return
                    (pick_enc_ee thumb narrow_or_thumbee
                       (not narrow_okay andalso thumbee_okay),
                     (if ld then mk_Load else mk_Store)
                        (mk_bool indx,u,byte,w,unpriv,rn,rt,
                         mk_Mode2_immediate imm12)))
             end handle HOL_ERR {message,...} =>
               other_errorT ("arm_parse_mode2_offset", message)))
        (fn _ =>
           arm_parse_plus_minus >>= (fn pos =>
           arm_parse_register >>= (fn rm =>
           arm_parse_mode2_shift thumb q rm >>= (fn mode2 =>
             (if indx then
               arm_parse_rsquare >>-
               tryT arm_parse_exclaim (K (return T)) (K (return F))
             else
               return
                 (mk_bool (thumb orelse not thumb andalso is_T unpriv))) >>=
             (fn w =>
                let val (sh,_,_) = dest_Mode2_register mode2
                    val narrow_okay = q <> Wide andalso indx andalso
                                      narrow_registers [rt,rn,rm] andalso
                                      sh ~~ mk_word5 (if thumbee then 2 else 0)
                                      andalso is_F w
                in
                  assertT ((not thumb orelse pos andalso is_F w) andalso
                           (q <> Narrow orelse narrow_okay))
                    ("arm_parse_mode2_offset", "invalid argument(s)")
                    (return
                      (pick_enc_ee thumb narrow_okay thumbee,
                     (if ld then mk_Load else mk_Store)
                        (mk_bool indx,mk_bool pos,byte,w,unpriv,rn,rt,mode2)))
                end)))))))));

val arm_parse_mode2 : bool -> term -> (term * term) M =
  fn ld => fn byte =>
    arm_parse_register >>= (fn rt =>
    arm_parse_comma >>-
    read_thumb >>= (fn thumb =>
    read_qualifier >>= (fn q =>
    tryT arm_parse_lsquare
      (fn _ =>
         arm_parse_register >>= (fn rn =>
         tryT arm_parse_comma
           (fn _ => arm_parse_mode2_offset (ld,true,byte,F,rt,rn))
           (fn _ =>
              arm_parse_rsquare >>-
              tryT arm_parse_comma
                (fn _ => arm_parse_mode2_offset (ld,false,byte,F,rt,rn))
                (fn _ =>
                   let val narrow_okay = q <> Wide andalso narrow_register rt
                                           andalso (narrow_register rn orelse
                                                    is_F byte andalso is_SP rn)
                   in
                     assertT (q <> Narrow orelse narrow_okay)
                       ("arm_parse_mode2",
                        "invalid register(s) for narrow Thumb instruction")
                       (return
                          (pick_enc thumb narrow_okay,
                           (if ld then mk_Load else mk_Store)
                             (T,T,byte,F,F,rn,rt,
                              mk_Mode2_immediate (mk_word12 0))))
                   end))))
      (fn _ =>
        arm_parse_branch_offset >>= (fn i =>
         let val narrow_okay = narrow_register rt andalso is_F byte in
           assertT (ld andalso (q <> Narrow orelse narrow_okay))
             ("arm_parse_mode2", "not a valid instruction")
             (if is_var i then
                return
                  (pick_var_enc thumb q narrow_okay,
                   mk_Load (T,boolSyntax.arb,byte,F,F,mk_word4 15,rt,
                            cast_var ``:addressing_mode2`` i))
              else
                let val v = sint_of_term i - (if thumb then 4 else 8)
                    val narrow_okay = q <> Wide andalso v mod 4 = 0 andalso
                                      0 <= v andalso v <= 1020
                    val wide_okay = q <> Narrow andalso ~4095 <= v andalso
                                    v <= 4095
                    val mode2 = mk_Mode2_immediate (mk_word12 (Int.abs v))
                in
                  assertT (not thumb orelse narrow_okay orelse wide_okay)
                    ("arm_parse_mode2", "not a valid instruction")
                    (return
                       (pick_enc thumb narrow_okay,
                        mk_Load (T,mk_bool (0 <= v andalso not (i ~~ ``-0i``)),
                                 byte,F,F,mk_word4 15,rt,mode2)))
                end handle HOL_ERR {message,...} =>
                  other_errorT ("arm_parse_mode2", message))
         end)))) >>= (fn result =>
    read_OutsideOrLastInITBlock >>= (fn OutsideOrLastInITBlock =>
      assertT (not (is_PC rt) orelse OutsideOrLastInITBlock)
        ("arm_parse_mode2", "must be outside or last in IT block")
        (return result))));

val arm_parse_mode2_unpriv : bool -> term -> (term * term) M =
  fn ld => fn byte =>
    thumb2_or_arm_okay "arm_parse_mode2_unpriv"
      (fn enc =>
        arm_parse_register >>= (fn rt =>
        arm_parse_comma >>-
        arm_parse_lsquare >>-
        arm_parse_register >>= (fn rn =>
        tryT arm_parse_comma
          (fn _ =>
             (arm_parse_constant >>= (fn i =>
              arm_parse_rsquare >>-
                let val v = sint_of_term i
                    val mode2 = mk_Mode2_immediate (mk_word12 (Int.abs v))
                in
                  assertT (enc ~~ Encoding_Thumb2_tm andalso
                           0 <= v andalso v <= 255)
                    ("arm_parse_mode2_unpriv",
                     "must be Thumb2 with offset in range 0-255")
                    (return (enc,
                       if ld then
                         mk_Load (T,T,byte,F,T,rn,rt,mode2)
                       else
                         mk_Store (T,T,byte,F,T,rn,rt,mode2)))
                end handle HOL_ERR {message,...} =>
                  other_errorT ("arm_parse_mode2_unpriv", message))))
           (fn _ =>
              arm_parse_rsquare >>-
              tryT arm_parse_comma
                (fn _ =>
                   assertT (enc ~~ Encoding_ARM_tm)
                     ("arm_parse_mode2_unpriv", "unexpected comma")
                     (arm_parse_mode2_offset (ld,false,byte,T,rt,rn)))
                (fn _ =>
                  return (enc,
                   (if ld then mk_Load else mk_Store)
                      (mk_bool (enc ~~ Encoding_Thumb2_tm),T,byte,F,T,rn,rt,
                       mk_Mode2_immediate (mk_word12 0))))))));

(* ------------------------------------------------------------------------- *)

val mode3_register = curry mk_Mode3_register (mk_word2 0);

val arm_parse_mode3_shift : bool -> qualifier -> term -> term M =
  fn thumb => fn q => fn rm =>
    tryT arm_parse_comma
      (fn _ =>
         assertT (thumb andalso q <> Narrow)
           ("arm_parse_mode3_shift", "unexpected comma")
           (arm_parse_string "lsl" >>-
            arm_parse_constant >>= (fn i =>
              let val imm2 = uint_to_word ``:2`` i in
                return (mk_Mode3_register (imm2, rm))
              end handle HOL_ERR {message,...} =>
                other_errorT ("arm_parse_mode3_shift", message))))
      (fn _ => return (mode3_register rm));

val arm_parse_mode3_offset :
  ((term * term) option * bool * term * term * term) -> (term * term) M =
  fn (opt,indx,unpriv,rt,rn) =>
    read_thumb >>= (fn thumb =>
    read_qualifier >>= (fn q =>
    assertT (indx orelse q <> Narrow)
      ("arm_parse_mode3_offset",
       "post indexing not possible for narrow Thumb instruction")
      (tryT arm_parse_constant
        (fn i =>
          (if indx then
             arm_parse_rsquare >>-
             tryT arm_parse_exclaim (K (return T)) (K (return F))
           else
             return (mk_bool thumb)) >>=
          (fn w =>
             let val v = sint_of_term i
                 val u = mk_bool (0 <= v andalso not (i ~~ ``-0i``))
                 val narrow_okay = q <> Wide andalso narrow_registers [rt,rn]
                                     andalso is_F w andalso v mod 2 = 0 andalso
                                   0 <= v andalso v <= 62 andalso
                                   case opt of
                                     SOME (s,h) => is_F s andalso is_T h
                                   | NONE => true
                 val wide_okay = ~255 <= v andalso
                                 if indx andalso is_T u andalso is_F w then
                                   v <= 4095
                                 else
                                   v <= 255 andalso not (is_PC rt andalso
                                     indx andalso is_F u andalso is_F w)
                 val arm_okay = ~255 <= v andalso v <= 255
                 val imm12 = mk_word12 (Int.abs v)
             in
               assertT
                 (q = Narrow andalso narrow_okay orelse
                  q <> Narrow andalso thumb andalso wide_okay orelse
                  not thumb andalso arm_okay)
                 ("arm_parse_mode3_offset",
                  "invalid argument(s) (check registers, alignment and range)")
                 (return
                    (pick_enc thumb narrow_okay,
                     case opt
                     of SOME (signed,half) =>
                          mk_Load_Halfword
                            (mk_bool indx,u,w,signed,half,unpriv,rn,rt,
                             mk_Mode3_immediate imm12)
                      | NONE =>
                          mk_Store_Halfword (mk_bool indx,u,w,unpriv,rn,rt,
                            mk_Mode3_immediate imm12)))
             end handle HOL_ERR {message,...} =>
               other_errorT ("arm_parse_mode3_offset", message)))
        (fn _ =>
           arm_parse_plus_minus >>= (fn pos =>
           arm_parse_register >>= (fn rm =>
           arm_parse_mode3_shift thumb q rm >>= (fn mode3 =>
           read_thumbee >>= (fn thumbee =>
             (if indx then
               arm_parse_rsquare >>-
               tryT arm_parse_exclaim (K (return T)) (K (return F))
             else
               return (mk_bool thumb)) >>=
             (fn w =>
                let val (sh,_) = dest_Mode3_register mode3
                    val narrow_okay = q <> Wide andalso indx andalso
                                      narrow_registers [rt,rn,rm] andalso
                                      sh ~~ mk_word2 (if thumbee then 1 else 0)
                                      andalso is_F w
                in
                  assertT ((not thumb orelse pos andalso is_F w) andalso
                           (q <> Narrow orelse narrow_okay))
                    ("arm_parse_mode3_offset", "invalid argument(s)")
                    (return
                      (pick_enc_ee thumb narrow_okay thumbee,
                       case opt
                       of SOME (signed,half) =>
                            mk_Load_Halfword
                              (mk_bool indx,mk_bool pos,w,signed,half,unpriv,
                               rn,rt,mode3)
                        | NONE =>
                            mk_Store_Halfword
                              (mk_bool indx,mk_bool pos,w,unpriv,rn,rt,mode3)))
                end)))))))));

val arm_parse_mode3 : (term * term) option -> (term * term) M =
  fn opt =>
    arm_parse_register >>= (fn rt =>
    arm_parse_comma >>-
    read_thumb >>= (fn thumb =>
    read_qualifier >>= (fn q =>
    tryT arm_parse_lsquare
      (fn _ =>
         arm_parse_register >>= (fn rn =>
         tryT arm_parse_comma
           (fn _ => arm_parse_mode3_offset (opt,true,F,rt,rn))
           (fn _ =>
              arm_parse_rsquare >>-
              tryT arm_parse_comma
                (fn _ => arm_parse_mode3_offset (opt,false,F,rt,rn))
                (fn _ =>
                   let val narrow_okay = q <> Wide andalso
                                         narrow_registers [rt,rn] andalso
                                         case opt of
                                           SOME (s,h) => is_F s andalso is_T h
                                         | NONE => true
                   in
                     assertT (q <> Narrow orelse narrow_okay)
                       ("arm_parse_mode3", "invalid narrow Thumb instruction")
                       (return
                          (pick_enc thumb narrow_okay,
                           case opt
                           of SOME (signed,half) =>
                                mk_Load_Halfword
                                  (T,T,F,signed,half,F,rn,rt,
                                   mk_Mode3_immediate (mk_word12 0))
                            | NONE =>
                                mk_Store_Halfword
                                  (T,T,F,F,rn,rt,
                                   mk_Mode3_immediate (mk_word12 0))))
                   end))))
      (fn _ =>
        arm_parse_branch_offset >>= (fn i =>
        assertT (isSome opt andalso q <> Narrow)
          ("arm_parse_mode3", "not a valid instruction")
          (let val (signed,half) = case opt
                                   of SOME x => x
                                    | _ => (boolSyntax.arb,boolSyntax.arb)
           in
             if is_var i then
               return
                 (if thumb then Encoding_Thumb2_tm else Encoding_ARM_tm,
                  mk_Load_Halfword (T,boolSyntax.arb,F,signed,half,F,
                    mk_word4 15,rt,cast_var ``:addressing_mode3`` i))
             else
               let val v = sint_of_term i - (if thumb then 4 else 8)
                   val wide_okay = thumb andalso ~4095 <= v andalso v <= 4095
                   val arm_okay = not thumb andalso ~255 <= v andalso v <= 255
                   val mode3 = mk_Mode3_immediate (mk_word12 (Int.abs v))
               in
                 assertT (wide_okay orelse arm_okay)
                   ("arm_parse_mode3", "offset beyond permitted range")
                   (return
                      (if thumb then Encoding_Thumb2_tm else Encoding_ARM_tm,
                       mk_Load_Halfword (T,
                         mk_bool (0 <= v andalso not (i ~~ ``-0i``)),F,
                         signed,half,F,mk_word4 15,rt,mode3)))
               end handle HOL_ERR {message,...} =>
                 other_errorT ("arm_parse_mode3", message)
           end))))));

val arm_parse_mode3_unpriv : (term * term) option -> (term * term) M =
  fn opt =>
    thumb2_or_arm_okay "arm_parse_mode3_unpriv"
      (fn enc =>
        arm_parse_register >>= (fn rt =>
        arm_parse_comma >>-
        arm_parse_lsquare >>-
        arm_parse_register >>= (fn rn =>
        tryT arm_parse_comma
          (fn _ =>
             (arm_parse_constant >>= (fn i =>
              arm_parse_rsquare >>-
                let val v = sint_of_term i
                    val mode3 = mk_Mode3_immediate (mk_word12 (Int.abs v))
                in
                  assertT (enc ~~ Encoding_Thumb2_tm andalso
                           0 <= v andalso v <= 255)
                    ("arm_parse_mode3_unpriv",
                     "must be Thumb2 with offset in range 0-255")
                    (return (enc,
                       case opt
                       of SOME (signed,half) =>
                            mk_Load_Halfword (T,T,F,signed,half,T,rn,rt,mode3)
                        | NONE =>
                            mk_Store_Halfword (T,T,F,T,rn,rt,mode3)))
                end handle HOL_ERR {message,...} =>
                  other_errorT ("arm_parse_mode3_unpriv", message))))
           (fn _ =>
            arm_parse_rsquare >>-
            tryT arm_parse_comma
              (fn _ =>
                 assertT (enc ~~ Encoding_ARM_tm)
                   ("arm_parse_mode3_unpriv", "unexpected comma")
                   (tryT (arm_parse_plus_minus >>= (fn pos =>
                          arm_parse_register >>= (fn rm => return (pos,rm))))
                      (fn (pos,rm) =>
                         return
                           (mk_bool pos, mk_Mode3_register (mk_word2 0,rm)))
                      (fn _ =>
                        arm_parse_constant >>= (fn i =>
                         let val v = sint_of_term i in
                           assertT (~255 <= v andalso v <= 255)
                             ("arm_parse_mode3_unpriv",
                              "offset must be in range -255-255")
                             (return
                               (mk_bool (0 <= v andalso not (i ~~ ``-0i``)),
                                mk_Mode3_immediate (mk_word12 (Int.abs v))))
                         end handle HOL_ERR {message,...} =>
                           other_errorT ("arm_parse_mode3_unpriv", message)))))
              (fn _ => return (T,mk_Mode3_immediate (mk_word12 0))) >>=
            (fn (add,tm) =>
               let val thumb = enc ~~ Encoding_Thumb2_tm
                   val indx = mk_bool thumb
                   val w = mk_bool (not thumb)
               in
                 return (enc,
                   case opt
                   of SOME (signed,half) =>
                        mk_Load_Halfword (indx,add,w,signed,half,T,rn,rt,tm)
                    | NONE =>
                        mk_Store_Halfword (indx,add,w,T,rn,rt,tm))
               end)))));

(* ------------------------------------------------------------------------- *)

val arm_parse_mode3_dual_offset : bool -> (term * term) M =
  fn thumb =>
    tryT arm_parse_constant
      (fn i =>
         let val offset = sint_of_term i in
           if thumb then
             assertT (offset mod 4 = 0)
               ("arm_parse_mode3_dual_offset", "offset must be word aligned")
               (assertT (~1020 <= offset andalso offset <= 1020)
                  ("arm_parse_mode3_dual_offset",
                    "offset beyond permitted range (-1020 to +1020)")
                  (return
                     (mk_bool (0 <= offset andalso not (i ~~ ``-0i``)),
                      mk_Mode3_immediate (mk_word12 (Int.abs offset)))))
           else
             assertT (~255 <= offset andalso offset <= 255)
               ("arm_parse_mode3_dual_offset",
                "offset beyond permitted range (-255 to +255)")
               (return (mk_bool (0 <= offset andalso not (i ~~ ``-0i``)),
                  mk_Mode3_immediate (mk_word12 (Int.abs offset))))
         end handle HOL_ERR {message,...} =>
            other_errorT ("arm_parse_mode3_dual_offset", message))
      (fn _ =>
        assertT (not thumb)
         ("arm_parse_mode3_dual_offset", "expecting a constant")
         (arm_parse_plus_minus >>= (fn pos =>
          arm_parse_register >>= (fn rm =>
            return (mk_bool pos,mode3_register rm)))));

val arm_parse_mode3_dual : bool -> (term * term) M =
  fn ld =>
    need_dsp "arm_parse_mode3_dual" (thumb2_or_arm_okay "arm_parse_mode3_dual"
    (fn enc =>
       arm_parse_register >>= (fn rt =>
       arm_parse_comma >>-
       arm_parse_register >>= (fn rt2 =>
       arm_parse_comma >>-
         let val thumb = enc ~~ Encoding_Thumb2_tm
             val t1 = uint_of_word rt
             val t2 = uint_of_word rt2
         in
           assertT (thumb orelse t1 mod 2 = 0 andalso t2 = t1 + 1)
             ("arm_parse_mode3_dual",
              "first register must be even and second consecutive")
             (tryT arm_parse_lsquare
               (fn _ =>
                 arm_parse_register >>= (fn rn =>
                 tryT arm_parse_comma
                   (fn _ =>
                      arm_parse_mode3_dual_offset thumb >>= (fn (add,tm) =>
                      arm_parse_rsquare >>-
                      tryT arm_parse_exclaim (K (return T)) (K (return F)) >>=
                      (fn wb =>
                         return
                           (if ld then
                              (enc, mk_Load_Dual (T,add,wb,rn,rt,rt2,tm))
                            else
                              (enc, mk_Store_Dual (T,add,wb,rn,rt,rt2,tm))))))
                   (fn _ =>
                    arm_parse_rsquare >>-
                    tryT (arm_parse_comma >>- arm_parse_mode3_dual_offset thumb)
                      (fn (a,t) => return (F,a,t))
                      (fn _ =>
                         return (T,T,mk_Mode3_immediate (mk_word12 0))) >>=
                   (fn (indx,add,tm) =>
                      let val w = mk_bool
                                   (enc ~~ Encoding_Thumb2_tm andalso is_F indx)
                      in
                        return
                          (if ld then
                             (enc, mk_Load_Dual (indx,add,w,rn,rt,rt2,tm))
                           else
                             (enc, mk_Store_Dual (indx,add,w,rn,rt,rt2,tm)))
                      end))))
              (fn _ =>
                 assertT ld ("arm_parse_mode3_dual","expecting [")
                  (arm_parse_branch_offset >>= (fn i =>
                     if is_var i then
                       return (enc,
                         mk_Load_Dual (T,boolSyntax.arb,F,mk_word4 15,rt,rt2,
                           cast_var ``:addressing_mode3`` i))
                     else
                       let val v = sint_of_term i - (if thumb then 4 else 8)
                           val wide_okay = ~1020 <= v andalso v <= 1020
                           val arm_okay = ~255 <= v andalso v <= 255
                           val mode3 = mk_Mode3_immediate
                                         (mk_word12 (Int.abs v))
                       in
                         assertT
                           (if enc ~~ Encoding_Thumb2_tm
                            then wide_okay else arm_okay)
                           ("arm_parse_mode3_dual",
                            "offset beyond permitted range")
                           (return (enc,
                              mk_Load_Dual
                                (T,mk_bool (0 <= v andalso not (i ~~ ``-0i``)),
                                 F,mk_word4 15,rt,rt2,mode3)))
                       end handle HOL_ERR {message,...} =>
                         other_errorT ("arm_parse_mode3_dual", message)))))
         end))));

(* ------------------------------------------------------------------------- *)

val arm_parse_ldrex : (term * term) M =
  need_v6 "arm_parse_ldrex"
    (thumb2_or_arm_okay "arm_parse_ldrex"
     (fn enc =>
        arm_parse_register >>= (fn rt =>
        arm_parse_comma >>-
        arm_parse_lsquare >>-
        arm_parse_register >>= (fn rn =>
        tryT arm_parse_comma
          (fn _ =>
             arm_parse_constant >>= (fn i =>
             arm_parse_rsquare >>-
               let val v = sint_of_term i in
                 assertT (if enc ~~ Encoding_Thumb2_tm then
                            0 <= v andalso v <= 1020 andalso v mod 4 = 0
                          else
                            v = 0)
                   ("arm_parse_ldrex", "offset unaligned or out of range")
                   (return (enc,
                      mk_Load_Exclusive (rn,rt,mk_word8 (Int.abs (v div 4)))))
               end handle HOL_ERR {message,...} =>
                 other_errorT ("arm_parse_ldrex", message)))
          (fn _ =>
            arm_parse_rsquare >>-
             return (enc, mk_Load_Exclusive (rn,rt,mk_word8 0)))))));

val arm_parse_strex : (term * term) M =
  need_v6 "arm_parse_strex"
    (thumb2_or_arm_okay "arm_parse_strex"
     (fn enc =>
        arm_parse_register >>= (fn rd =>
        arm_parse_comma >>-
        arm_parse_register >>= (fn rt =>
        arm_parse_comma >>-
        arm_parse_lsquare >>-
        arm_parse_register >>= (fn rn =>
        tryT arm_parse_comma
          (fn _ =>
             arm_parse_constant >>= (fn i =>
             arm_parse_rsquare >>-
               let val v = sint_of_term i in
                 assertT (if enc ~~ Encoding_Thumb2_tm then
                            0 <= v andalso v <= 1020 andalso v mod 4 = 0
                          else
                            v = 0)
                   ("arm_parse_strex", "offset unaligned or out of range")
                   (return (enc,
                      mk_Store_Exclusive
                        (rn,rd,rt,mk_word8 (Int.abs (v div 4)))))
               end handle HOL_ERR {message,...} =>
                 other_errorT ("arm_parse_strex", message)))
          (fn _ =>
            arm_parse_rsquare >>-
             return (enc, mk_Store_Exclusive (rn,rd,rt,mk_word8 0))))))));

val arm_parse_ldrexd : (term * term) M =
  read_thumb >>= (fn thumb =>
    arch_okay ("arm_parse_ldrexd", "not supported by selected architecture")
      (fn a => version_number a >= 7 orelse not thumb andalso a = ARMv6K)
      (arm_parse_register >>= (fn rt =>
       arm_parse_comma >>-
       arm_parse_register >>= (fn rt2 =>
       arm_parse_comma >>-
       arm_parse_lsquare >>-
       arm_parse_register >>= (fn rn =>
       arm_parse_rsquare >>-
         let val t1 = uint_of_word rt
             val t2 = uint_of_word rt2
         in
           assertT (thumb orelse t1 mod 2 = 0 andalso t2 = t1 + 1)
             ("arm_parse_ldrexd",
              "first register must be even and second consecutive")
             (return (if thumb then Encoding_Thumb2_tm else Encoding_ARM_tm,
                mk_Load_Exclusive_Doubleword (rn,rt,rt2)))
         end)))));

val arm_parse_strexd : (term * term) M =
  read_thumb >>= (fn thumb =>
    arch_okay ("arm_parse_strexd", "not supported by selected architecture")
      (fn a => version_number a >= 7 orelse not thumb andalso a = ARMv6K)
      (arm_parse_register >>= (fn rd =>
       arm_parse_comma >>-
       arm_parse_register >>= (fn rt =>
       arm_parse_comma >>-
       arm_parse_register >>= (fn rt2 =>
       arm_parse_comma >>-
       arm_parse_lsquare >>-
       arm_parse_register >>= (fn rn =>
       arm_parse_rsquare >>-
         let val t1 = uint_of_word rt
             val t2 = uint_of_word rt2
         in
           assertT (thumb orelse t1 mod 2 = 0 andalso t2 = t1 + 1)
             ("arm_parse_strexd",
              "first register must be even and second consecutive")
             (return (if thumb then Encoding_Thumb2_tm else Encoding_ARM_tm,
                mk_Store_Exclusive_Doubleword (rn,rd,rt,rt2)))
         end))))));

val arm_parse_ldrexb_ldrexh : bool -> (term * term) M =
  fn half =>
    read_thumb >>= (fn thumb =>
      arch_okay ("arm_parse_ldrexb_ldrexh",
                 "not supported by selected architecture")
        (fn a => version_number a >= 7 orelse not thumb andalso a = ARMv6K)
        (arm_parse_register >>= (fn rt =>
         arm_parse_comma >>-
         arm_parse_lsquare >>-
         arm_parse_register >>= (fn rn =>
         arm_parse_rsquare >>-
           return (if thumb then Encoding_Thumb2_tm else Encoding_ARM_tm,
             if half then
               mk_Load_Exclusive_Halfword (rn,rt)
             else
               mk_Load_Exclusive_Byte (rn,rt))))));

val arm_parse_strexb_strexh : bool -> (term * term) M =
  fn half =>
    read_thumb >>= (fn thumb =>
      arch_okay ("arm_parse_strexb_strexh",
                 "not supported by selected architecture")
        (fn a => version_number a >= 7 orelse not thumb andalso a = ARMv6K)
        (arm_parse_register >>= (fn rd =>
         arm_parse_comma >>-
         arm_parse_register >>= (fn rt =>
         arm_parse_comma >>-
         arm_parse_lsquare >>-
         arm_parse_register >>= (fn rn =>
         arm_parse_rsquare >>-
           return (if thumb then Encoding_Thumb2_tm else Encoding_ARM_tm,
             if half then
               mk_Store_Exclusive_Halfword (rn,rd,rt)
             else
               mk_Store_Exclusive_Byte (rn,rd,rt)))))));

val arm_parse_swp : term -> (term * term) M =
  fn byte =>
    read_thumb >>= (fn thumb =>
      assertT (not thumb)
        ("arm_parse_swp", "not available as Thumb instruction")
        (arm_parse_register >>= (fn rt =>
         arm_parse_comma >>-
         arm_parse_register >>= (fn rt2 =>
         arm_parse_comma >>-
         arm_parse_lsquare >>-
         arm_parse_register >>= (fn rn =>
         arm_parse_rsquare >>-
           return (Encoding_ARM_tm, mk_Swap (byte,rn,rt,rt2)))))));

(* ------------------------------------------------------------------------- *)

val arm_parse_register_list_entry : (int * int) M =
  arm_parse_register >>= (fn ra =>
  tryT arm_parse_minus
    (fn _ =>
       arm_parse_register >>= (fn rb =>
         return (uint_of_word ra,uint_of_word rb)))
    (fn _ => let val i = uint_of_word ra in (return (i,i)) end));

fun arm_parse_register_list_entries
      (l : (int * int) list) : (int * int) list M =
    tryT arm_parse_register_list_entry
      (fn h =>
         tryT arm_parse_comma
           (fn _ => arm_parse_register_list_entries (h::l) >>= return)
           (fn _ => return (h::l)))
      (fn _ =>
        assertT (not (null l))
         ("arm_parse_register_list_entries", "not a valid register list")
         (return l));

fun valid_register_list [] = true
  | valid_register_list [(x,y)] = x <= y
  | valid_register_list ((x,y)::t) =
      x <= y andalso fst (hd t) < x andalso valid_register_list t;

local
  fun in_register_list _ [] = false
    | in_register_list r ((x,y)::t) =
        x <= r andalso r <= y orelse in_register_list r t;
in
  fun register_list_to_word16 l =
  let fun recurse 0 a = a
        | recurse i a = recurse (i - 1)
            (if in_register_list (i - 1) l then 2 * a + 1 else 2 * a)
  in
    mk_word16 (recurse 16 0)
  end
end;

val arm_parse_register_list : term M =
  arm_parse_lbrace >>-
  arm_parse_register_list_entries [] >>= (fn l =>
  arm_parse_rbrace >>-
  (assertT (valid_register_list l)
     ("arm_parse_register_list", "not a valid register list")
     (return (register_list_to_word16 l))));

val singleton_list_to_reg =
  mk_word4 o uint_of_word o eval o wordsSyntax.mk_word_log2;

fun bit_count tm = numSyntax.int_of_term (eval (wordsSyntax.mk_bit_count tm))

val arm_parse_pop_push : bool -> (term * term) M =
  fn pop =>
    arm_parse_register_list >>= (fn list =>
      let val count = bit_count list in
        read_thumb >>= (fn thumb =>
          if thumb then
            read_OutsideOrLastInITBlock >>= (fn OutsideOrLastInITBlock =>
            read_qualifier >>= (fn q =>
              let val high_bits = (uint_of_word list) div 256
                  val pc = bit 7 high_bits
                  val lr = bit 6 high_bits
                  val sp = bit 5 high_bits
                  val narrow_okay = q <> Wide andalso
                                    (not pc orelse OutsideOrLastInITBlock)
                                    andalso (high_bits = 0 orelse
                                    (high_bits = (if pop then 128 else 64)))
                  val wide_okay = q <> Narrow andalso not sp andalso
                                  (pop orelse not pc) andalso
                                  (not pc orelse not lr andalso
                                     OutsideOrLastInITBlock)
              in
                if count = 1 andalso not narrow_okay then
                  assertT wide_okay
                    ("arm_parse_pop_push",
                     "invalid register list, or must be outside or\
                     \ last in IT block")
                    (return (Encoding_Thumb2_tm,
                      if pop then
                        mk_Load (F,T,F,T,F,mk_word4 13,
                          singleton_list_to_reg list,
                          mk_Mode2_immediate (mk_word12 4))
                      else
                        mk_Store (T,F,F,T,F,mk_word4 13,
                          singleton_list_to_reg list,
                          mk_Mode2_immediate (mk_word12 4))))
                else
                  assertT (narrow_okay orelse wide_okay)
                    ("arm_parse_pop_push",
                     "invalid register list, or must be outside or\
                     \ last in IT block")
                    (return
                       (if narrow_okay then
                          Encoding_Thumb_tm
                        else
                          Encoding_Thumb2_tm,
                        if pop then
                          mk_Load_Multiple (F,T,F,T,mk_word4 13,list)
                        else
                          mk_Store_Multiple (T,F,F,T,mk_word4 13,list)))
                end))
          else
            return (Encoding_ARM_tm,
              if count = 1 then
                if pop then
                  mk_Load (F,T,F,F,F,mk_word4 13,singleton_list_to_reg list,
                           mk_Mode1_immediate (mk_word12 4))
                else
                  mk_Store (T,F,F,T,F,mk_word4 13,singleton_list_to_reg list,
                           mk_Mode1_immediate (mk_word12 4))
              else
                if pop then
                  mk_Load_Multiple (F,T,F,T,mk_word4 13,list)
                else
                  mk_Store_Multiple (T,F,F,T,mk_word4 13,list)))
      end);

val arm_parse_ldm_stm : bool -> term -> term -> (term * term) M =
  fn ldm => fn indx => fn add =>
    arm_parse_register >>= (fn rn =>
    tryT arm_parse_exclaim (K (return T)) (K (return F)) >>= (fn w =>
    arm_parse_comma >>-
    arm_parse_register_list >>= (fn list =>
      read_thumb >>= (fn thumb =>
      read_thumbee >>= (fn thumbee =>
        if thumb then
          read_OutsideOrLastInITBlock >>= (fn OutsideOrLastInITBlock =>
          read_qualifier >>= (fn q =>
            let
              val count = bit_count list
              val l = uint_of_word list
              val n = uint_of_word rn
              val high_bits = l div 256
              val pc = bit 7 high_bits
              val lr = bit 6 high_bits
              val sp = bit 5 high_bits
              val narrow_okay =
                    q <> Wide andalso not thumbee andalso
                    if ldm then
                      is_F indx andalso is_T add andalso
                      is_T w <> bit n l andalso
                      (narrow_register rn andalso high_bits = 0 orelse
                       is_SP rn andalso mem high_bits [0,128] andalso
                       (not pc orelse OutsideOrLastInITBlock))
                    else
                      is_T w andalso
                      (is_F indx andalso is_T add andalso
                       narrow_register rn andalso high_bits = 0 orelse
                       is_T indx andalso is_F add andalso
                       is_SP rn andalso mem high_bits [0,64])
              val wide_okay = q <> Narrow andalso
                              (is_F indx andalso is_T add orelse
                               is_T indx andalso is_F add) andalso
                              not sp andalso (ldm orelse not pc) andalso
                              (not pc orelse not lr andalso
                                 OutsideOrLastInITBlock)
            in
              if count = 1 andalso not narrow_okay then
                assertT wide_okay
                  ("arm_parse_ldm_stm", "invalid instruction")
                  (return
                    (Encoding_Thumb2_tm,
                     if ldm then
                       mk_Load (indx,add,F,F,w,rn,singleton_list_to_reg list,
                                mk_Mode2_immediate (mk_word12 4))
                     else
                       mk_Store (indx,add,F,w,F,rn,singleton_list_to_reg list,
                                 mk_Mode2_immediate (mk_word12 4))))
              else
                assertT (narrow_okay orelse wide_okay)
                  ("arm_parse_ldm_stm", "invalid instruction")
                  (return
                     (if narrow_okay then
                        Encoding_Thumb_tm
                      else
                        Encoding_Thumb2_tm,
                      if ldm then
                        mk_Load_Multiple (indx,add,F,w,rn,list)
                      else
                        mk_Store_Multiple (indx,add,F,w,rn,list)))
            end))
        else
          (tryT arm_parse_hat (K (return T)) (K (return F)) >>= (fn sys =>
            return
              (Encoding_ARM_tm,
               if ldm then
                 mk_Load_Multiple (indx,add,sys,w,rn,list)
               else
                 mk_Store_Multiple (indx,add,sys,w,rn,list)))))))));

(* ------------------------------------------------------------------------- *)

val arm_parse_pld_pli : bool option -> (term * term) M =
  fn opt =>
    (case opt of SOME false => need_dsp | _ => need_v7) "arm_parse_pld_pli"
       (thumb2_or_arm_okay "arm_parse_pld_pli"
        (fn enc =>
          tryT arm_parse_lsquare
            (fn _ =>
               arm_parse_register >>= (fn rn =>
               tryT arm_parse_comma
                 (fn _ =>
                    tryT arm_parse_constant
                      (fn i =>
                         arm_parse_rsquare >>-
                           let val v = sint_of_term i
                               val mode2 = mk_Mode2_immediate
                                             (mk_word12 (Int.abs v))
                           in
                             assertT
                               ((if enc ~~ Encoding_Thumb2_tm then
                                   ~255 <= v
                                 else
                                   ~4095 <= v) andalso v <= 4095)
                               ("arm_parse_pld_pli",
                                "offset beyond permitted range")
                               (return (enc,
                                  case opt
                                  of SOME wide =>
                                       mk_Preload_Data
                                        (mk_bool (0 <= v andalso
                                                  not (i ~~ ``-0i``)),
                                         mk_bool wide,rn,mode2)
                                   | NONE =>
                                       mk_Preload_Instruction
                                        (mk_bool (0 <= v andalso
                                                  not (i ~~ ``-0i``)),
                                         rn,mode2)))
                           end handle HOL_ERR {message,...} =>
                             other_errorT ("arm_parse_pld_pli", message))
                    (fn _ =>
                       let val thumb = enc ~~ Encoding_Thumb2_tm in
                         arm_parse_plus_minus >>= (fn pos =>
                         arm_parse_register >>= (fn rm =>
                           assertT (not thumb orelse pos)
                             ("arm_parse_pld_pli",
                              "register offset must be positive in Thumb mode")
                             (arm_parse_mode2_shift thumb Either rm >>=
                              (fn mode2 =>
                                arm_parse_rsquare >>-
                                  return (enc,
                                    case opt
                                      of SOME wide =>
                                          mk_Preload_Data
                                            (mk_bool pos,mk_bool wide,rn,mode2)
                                      | NONE =>
                                          mk_Preload_Instruction
                                            (mk_bool pos,rn,mode2))))))
                       end))
                  (fn _ =>
                    arm_parse_rsquare >>-
                     (return (enc,
                        case opt
                        of SOME wide =>
                             mk_Preload_Data (T,mk_bool wide,rn,
                               mk_Mode2_immediate (mk_word12 0))
                         | NONE =>
                             mk_Preload_Instruction (T,rn,
                               mk_Mode2_immediate (mk_word12 0)))))))
           (fn _ =>
             arm_parse_branch_offset >>= (fn i =>
             assertT (opt <> SOME true)
               ("arm_parse_pld_pli", "literal form not available for pldw")
               (if is_var i then
                  return (enc,
                    case opt
                    of SOME wide =>
                         mk_Preload_Data
                           (boolSyntax.arb,mk_bool wide,mk_word4 15,
                            cast_var ``:addressing_mode2`` i)
                     | NONE =>
                         mk_Preload_Instruction
                           (boolSyntax.arb,mk_word4 15,
                                cast_var ``:addressing_mode2`` i))
                else
                  let val v = sint_of_term i -
                                (if enc ~~ Encoding_Thumb2_tm then 4 else 8)
                      val up = mk_bool (0 <= v andalso not (i ~~ ``-0i``))
                      val mode2 = mk_Mode2_immediate (mk_word12 (Int.abs v))
                  in
                    assertT (~4095 <= v andalso v <= 4095)
                      ("arm_parse_pld_pli", "offset beyond permitted range")
                      (return (enc,
                         case opt
                         of SOME wide =>
                              mk_Preload_Data
                                (up,mk_bool wide,mk_word4 15,mode2)
                          | NONE =>
                              mk_Preload_Instruction (up,mk_word4 15,mode2)))
                  end handle HOL_ERR {message,...} =>
                    other_errorT ("arm_parse_mode3", message))))));

(* ------------------------------------------------------------------------- *)

val arm_parse_ssat_usat : bool -> (term * term) M =
  fn unsigned =>
    need_v6 "arm_parse_ssat_usat"
      (thumb2_or_arm_okay "arm_parse_ssat_usat"
       (fn enc =>
          arm_parse_register >>= (fn rd =>
          arm_parse_comma >>-
          arm_parse_constant >>= (fn i =>
          arm_parse_comma >>-
            let val sat_imm = sint_of_term i - (if unsigned then 0 else 1) in
              assertT (0 <= sat_imm andalso sat_imm <= 31)
                ("arm_parse_ssat_usat", "can only saturate in range " ^
                   (if unsigned then "0-31" else "1-32"))
                (arm_parse_register >>= (fn rn =>
                 tryT arm_parse_comma
                   (fn _ =>
                      arm_parse_shift >>= (fn stype =>
                        assertT (mem stype [LSL_shift, ASR_shift])
                          ("arm_parse_ssat_usat", "only lsl and asr permitted")
                          (arm_parse_constant >>= (fn j =>
                             let val shift32 = j ~~ ``32i``
                                 val imm5 = if shift32 then
                                              mk_word5 0
                                            else
                                              uint_to_word ``:5`` j
                                 val sh = mk_bool (shift32 orelse
                                            not (imm5 ~~ mk_word5 0) andalso
                                            stype = ASR_shift)
                             in
                               assertT (not shift32 orelse stype = ASR_shift
                                        andalso enc ~~ Encoding_ARM_tm)
                                 ("arm_parse_ssat_usat", "invalid shift")
                                 (return (enc,
                                    mk_Saturate (mk_bool unsigned,
                                      mk_word5 sat_imm,rd,imm5,sh,rn)))
                             end handle HOL_ERR {message,...} =>
                               other_errorT ("arm_parse_ssat_usat",message)))))
                   (fn _ =>
                     return (enc, mk_Saturate
                      (mk_bool unsigned,mk_word5 sat_imm,rd,mk_word5 0,F,rn)))))
            end handle HOL_ERR {message,...} =>
              other_errorT ("arm_parse_ssat_usat", message)))));

val arm_parse_ssat16_usat16 : bool -> (term * term) M =
  fn unsigned =>
    need_v6 "arm_parse_ssat_usat"
      (thumb2_or_arm_okay "arm_parse_ssat_usat"
       (fn enc =>
          arm_parse_register >>= (fn rd =>
          arm_parse_comma >>-
          arm_parse_constant >>= (fn i =>
            let val sat_imm = sint_of_term i - (if unsigned then 0 else 1) in
              assertT (0 <= sat_imm andalso sat_imm <= 15)
                ("arm_parse_ssat_usat", "can only saturate in range " ^
                   (if unsigned then "0-15" else "1-16"))
                (arm_parse_comma >>-
                 arm_parse_register >>= (fn rn =>
                   return
                     (enc,mk_Saturate_16
                        (mk_bool unsigned,mk_word4 sat_imm,rd,rn))))
            end handle HOL_ERR {message,...} =>
              other_errorT ("arm_parse_ssat16_usat16", message)))));

val arm_parse_ror248 : term M =
  arm_parse_string "ror" >>-
  arm_parse_constant >>= (fn i =>
  (case sint_of_term i
   of 0  => return (mk_word2 0)
    | 8  => return (mk_word2 1)
    | 16 => return (mk_word2 2)
    | 24 => return (mk_word2 3)
    | _ => other_errorT ("arm_parse_ror248",
                         "shift must be 0, 8, 16 or 24"))
   handle HOL_ERR {message,...} =>
     other_errorT ("arm_parse_ror248", message));

val arm_parse_sxtb_etc : instruction_mnemonic -> (term * term) M =
  fn m =>
    need_v6 "arm_parse_sxtb_etc"
      (arm_parse_register >>= (fn rd =>
       tryT (arm_parse_comma >>- arm_parse_register)
         return (fn _ => return rd) >>= (fn rm =>
       read_qualifier >>= (fn q =>
       read_thumb >>= (fn thumb =>
       tryT arm_parse_comma
        (fn _ =>
           assertT (q <> Narrow)
             ("arm_parse_sxtb_etc", "unexpected trailing comma")
             (arm_parse_ror248 >>=
               (fn rot =>
                 return
                   (if thumb then Encoding_Thumb2_tm else Encoding_ARM_tm,
                    case m
                    of SXTB => mk_Extend_Byte (F,mk_word4 15,rd,rot,rm)
                     | UXTB => mk_Extend_Byte (T,mk_word4 15,rd,rot,rm)
                     | SXTH => mk_Extend_Halfword (F,mk_word4 15,rd,rot,rm)
                     | UXTH => mk_Extend_Halfword (T,mk_word4 15,rd,rot,rm)
                     | _ => raise ERR "arm_parse_sxtb_etc"
                                      "unexpected mnemonic"))))
        (fn _ =>
          let val narrow_okay = q <> Wide andalso narrow_registers [rd, rm] in
            assertT (q <> Narrow orelse narrow_okay)
              ("arm_parse_sxtb_etc",
               "invalid registers for narrow thumb instruction")
              (return
                 (pick_enc thumb narrow_okay,
                  case m
                  of SXTB => mk_Extend_Byte (F,mk_word4 15,rd,mk_word2 0,rm)
                   | UXTB => mk_Extend_Byte (T,mk_word4 15,rd,mk_word2 0,rm)
                   | SXTH => mk_Extend_Halfword (F,mk_word4 15,rd,mk_word2 0,rm)
                   | UXTH => mk_Extend_Halfword (T,mk_word4 15,rd,mk_word2 0,rm)
                   | _ => raise ERR "arm_parse_sxtb_etc" "unexpected mnemonic"))
          end))))));

val arm_parse_sxtab_etc : instruction_mnemonic -> (term * term) M =
  fn m =>
    need_v6 "arm_parse_sxtab_etc"
      (thumb2_or_arm_okay "arm_parse_sxtab_etc"
       (fn enc =>
          arm_parse_register >>= (fn rd =>
          arm_parse_comma >>-
          arm_parse_register >>= (fn rn =>
          tryT (arm_parse_comma >>- arm_parse_register)
            (fn rm => return (rd,rn,rm))
            (fn _ => return (rd,rd,rn)) >>= (fn (rd,rn,rm) =>
          tryT arm_parse_comma
            (fn _ => arm_parse_ror248)
            (fn _ => return (mk_word2 0)) >>=
          (fn rot =>
             return (enc,
               case m
               of SXTAB   => mk_Extend_Byte (F,rn,rd,rot,rm)
                | UXTAB   => mk_Extend_Byte (T,rn,rd,rot,rm)
                | SXTAB16 => mk_Extend_Byte_16 (F,rn,rd,rot,rm)
                | UXTAB16 => mk_Extend_Byte_16 (T,rn,rd,rot,rm)
                | SXTAH   => mk_Extend_Halfword (F,rn,rd,rot,rm)
                | UXTAH   => mk_Extend_Halfword (T,rn,rd,rot,rm)
                | _ => raise ERR "arm_parse_sxtab_etc"
                                 "unexpected mnemonic")))))));

val arm_parse_sxtb16_uxtb16 : term -> (term * term) M =
  fn unsigned =>
    need_v6 "arm_parse_sxtb16_uxtb16"
      (thumb2_or_arm_okay "arm_parse_sxtb16_uxtb16"
       (fn enc =>
         arm_parse_register >>= (fn rd =>
         tryT (arm_parse_comma >>- arm_parse_register)
           return (fn _ => return rd) >>= (fn rm =>
         tryT arm_parse_comma
           (K arm_parse_ror248)
           (K (return (mk_word2 0))) >>=
         (fn rot =>
            return
              (enc, mk_Extend_Byte_16 (unsigned,mk_word4 15,rd,rot,rm)))))));

val arm_parse_rev : instruction_mnemonic -> (term * term) M =
  fn m =>
    need_v6 "arm_parse_sxtab_etc"
      (arm_parse_register >>= (fn rd =>
       arm_parse_comma >>-
       arm_parse_register >>= (fn rm =>
       read_qualifier >>= (fn q =>
       read_thumb >>= (fn thumb =>
         let val narrow_okay = q <> Wide andalso narrow_registers [rd,rm] in
           assertT (q <> Narrow orelse narrow_okay)
             ("arm_parse_rev", "invalid registers for narrow thumb instruction")
             (return
                (pick_enc thumb narrow_okay,
                 case m
                 of REV   => mk_Byte_Reverse_Word (rd,rm)
                  | REV16 => mk_Byte_Reverse_Packed_Halfword (rd,rm)
                  | REVSH => mk_Byte_Reverse_Signed_Halfword (rd,rm)
                  | _ => raise ERR "arm_parse_sxtab_etc" "unexpected mnemonic"))
         end)))));

val arm_parse_rbit : (term * term) M =
  need_v6 "arm_parse_rbit"
    (thumb2_or_arm_okay "arm_parse_rbit"
      (fn enc =>
         arm_parse_register >>= (fn rd =>
         arm_parse_comma >>-
         arm_parse_register >>= (fn rm =>
           return (enc,mk_Reverse_Bits (rd,rm))))));

val arm_parse_sbfx_etc : instruction_mnemonic -> (term * term) M =
  fn m =>
    need_t2 "arm_parse_sbfx_etc"
      (thumb2_or_arm_okay "arm_parse_sbfx_etc"
       (fn enc =>
          arm_parse_register >>= (fn rd =>
          (if m = BFC then
             return (mk_word4 15)
           else
             arm_parse_comma >>-
             arm_parse_register) >>= (fn rn =>
          arm_parse_comma >>-
          arm_parse_constant >>= (fn lsb =>
          arm_parse_comma >>-
          arm_parse_constant >>= (fn width =>
            let val l = sint_of_term lsb
                val w = sint_of_term width
                val lsb = mk_word5 l
                val v = w - 1
            in
              assertT (0 <= l andalso l <= 31 andalso
                       1 <= w andalso w <= 32 - l)
                ("arm_parse_sbfx_etc", "invalid bit range")
                (return (enc,
                   case m
                   of SBFX => mk_Bit_Field_Extract (F,mk_word5 v,rd,lsb,rn)
                    | UBFX => mk_Bit_Field_Extract (T,mk_word5 v,rd,lsb,rn)
                    | BFC  => mk_Bit_Field_Clear_Insert
                                (mk_word5 (l + v),rd,lsb,rn)
                    | BFI  => mk_Bit_Field_Clear_Insert
                                (mk_word5 (l + v),rd,lsb,rn)
                    | _ => raise ERR "arm_parse_sbfx_etc" "invalid mnemonic"))
            end handle HOL_ERR {message,...} =>
              other_errorT ("arm_parse_sbfx_etc", message)))))));

local
  fun barrier_option s =
    mk_word4
      (case s
       of "sy"    => 15
        | "st"    => 14
        | "ish"   => 11
        | "ishst" => 10
        | "nsh"   => 7
        | "nshst" => 6
        | "osh"   => 3
        | "oshst" => 2
        | _ => raise ERR "barrier_option" (s ^ "is not a barrier option"))

  val barrier_strings =
    ["sy", "st", "ish", "ishst", "nsh", "nshst", "osh", "oshst"]
in
  val arm_parse_barrier : instruction_mnemonic -> (term * term) M =
    fn m =>
      need_v7 "arm_parse_barrier"
        (thumb2_or_arm_okay "arm_parse_barrier"
         (fn enc =>
            tryT (arm_parse_strings barrier_strings)
                 return (fn _ => return "sy") >>=
            (fn s =>
               assertT (m <> ISB orelse s = "sy")
                 ("arm_parse_barrier", "sy is the only option available")
                 (let val option = barrier_option s in
                    return (enc,
                      case m
                      of DMB => mk_Data_Memory_Barrier option
                       | DSB => mk_Data_Synchronization_Barrier option
                       | ISB => mk_Instruction_Synchronization_Barrier option
                       | _ => raise ERR "arm_parse_barrier" "invalid mnemonic")
                  end))))
end;

val arm_parse_mrs : (term * term) M =
  thumb2_or_arm_okay "arm_parse_mrs"
    (fn enc =>
       arm_parse_register >>= (fn rd =>
       arm_parse_comma >>-
       arm_parse_strings ["apsr","cpsr","spsr"] >>= (fn s =>
         return (enc, mk_Status_to_Register (mk_bool (s = "spsr"),rd)))));

local
  fun psr_fields l =
  let fun recurse [] x = x
        | recurse (#"f"::t) [0,s,x,c] = recurse t [1,s,x,c]
        | recurse (#"s"::t) [f,0,x,c] = recurse t [f,1,x,c]
        | recurse (#"x"::t) [f,s,0,c] = recurse t [f,s,1,c]
        | recurse (#"c"::t) [f,s,x,0] = recurse t [f,s,x,1]
        | recurse _ _ = raise ERR "psr_fields" ""
  in
    mk_word4 (list_to_int (recurse l [0,0,0,0]))
  end
in
  fun decode_spec_reg s =
  let val ls = lower_string s in
    if ls = "apsr_nzcvq" then
      (F,mk_word4 8)
    else if ls = "apsr_g" then
      (F,mk_word4 4)
    else if ls = "apsr_nzcvqg" then
      (F,mk_word4 12)
    else if ls = "apsr" then
      (F,mk_word4 12)
    else if ls = "cpsr" then
      (F,mk_word4 15)
    else if ls = "spsr" then
      (T,mk_word4 15)
    else if String.isPrefix "cpsr_" ls then
      (F,psr_fields (List.drop (String.explode ls,5)))
    else if String.isPrefix "spsr_" ls then
      (T,psr_fields (List.drop (String.explode ls,5)))
    else
      raise ERR "decode_spec_reg" ""
  end
end;

val arm_parse_msr : (term * term) M =
  thumb2_or_arm_okay "arm_parse_msr"
    (fn enc =>
     (read_token >>=
      (fn h =>
         case h
         of NONE => syntax_errorT ("psr","end-of_input")
          | SOME s =>
              let val (spsr,mask) = decode_spec_reg s in
                next_token >>- return (spsr,mask)
              end handle HOL_ERR _ =>
                syntax_errorT ("psr", Substring.string s)) >>=
      (fn (spsr,mask) =>
         arm_parse_comma >>-
         tryT arm_parse_register
           (fn rn =>
              return (enc,mk_Register_to_Status (spsr,mask,rn)))
           (fn _ =>
              assertT (enc ~~ Encoding_ARM_tm)
                ("arm_parse_msr", "not a Thumb instruction")
                (arm_parse_constant >>= (fn i =>
                  let val imm12 = int_to_mode1_immediate i in
                    return (enc, mk_Immediate_to_Status (spsr,mask,imm12))
                  end handle HOL_ERR {message,...} =>
                 other_errorT ("arm_parse_msr", message)))))));

val arm_parse_cps : (term * term) M =
  need_v6 "arm_parse_cps"
    (thumb2_or_arm_okay "arm_parse_cps"
     (fn enc =>
       arm_parse_constant >>= (fn i =>
         let val imm5 = optionSyntax.mk_some (uint_to_word ``:5`` i) in
           return (enc,mk_Change_Processor_State (mk_word2 0,F,F,F,imm5))
         end handle HOL_ERR {message,...} =>
           other_errorT ("arm_parse_cps", message))));

fun cps_iflags s =
let fun recurse [] x = x
      | recurse (#"a"::t) (false,i,f) = recurse t (true,i,f)
      | recurse (#"i"::t) (a,false,f) = recurse t (a,true,f)
      | recurse (#"f"::t) (a,i,false) = recurse t (a,i,true)
      | recurse _ _ = raise ERR "cps_iflags" ""
    val (a,i,f) = recurse (String.explode (lower_string s)) (false,false,false)
in
  (mk_bool a, mk_bool i, mk_bool f)
end

val arm_parse_cpsie_cpsid : term -> (term * term) M =
  fn imod =>
    need_v6 "arm_parse_cps"
     (read_token >>=
      (fn h =>
         case h
         of NONE => syntax_errorT ("interrupt flags", "end-of_input")
          | SOME s =>
              let val (affectA,affectI,affectF) = cps_iflags s in
                next_token >>- return (affectA,affectI,affectF)
              end handle HOL_ERR _ =>
                syntax_errorT ("interrupt flags", Substring.string s)) >>=
      (fn (affectA,affectI,affectF) =>
         tryT arm_parse_comma
           (fn _ =>
              arm_parse_constant >>= (fn i =>
                let val imm5 = optionSyntax.mk_some (uint_to_word ``:5`` i) in
                  return (false,imm5)
                end handle HOL_ERR {message,...} =>
                  other_errorT ("arm_parse_cpsie_cpsid", message)))
           (fn _ => return (true,optionSyntax.mk_none ``:word5``)) >>=
         (fn (narrow_okay,mode) =>
            read_thumb >>= (fn thumb =>
              if thumb then
                read_qualifier >>= (fn q =>
                  assertT (q <> Narrow orelse narrow_okay)
                    ("arm_parse_cpsie_cpsid",
                     "cannot set mode with narrow Thumb instruction")
                    (return
                       (if narrow_okay andalso q <> Wide then
                          Encoding_Thumb_tm
                        else
                          Encoding_Thumb2_tm,
                        mk_Change_Processor_State
                          (imod,affectA,affectI,affectF,mode))))
              else
                return (Encoding_ARM_tm,
                  mk_Change_Processor_State
                    (imod,affectA,affectI,affectF,mode))))));

val arm_parse_srs : term -> term -> (term * term) M =
  fn p => fn inc =>
    need_v6 "arm_parse_srs"
      (thumb2_or_arm_okay "arm_parse_srs"
       (fn enc =>
          assertT (enc ~~ Encoding_ARM_tm orelse p !~ inc)
            ("arm_parse_srs", "not available as a Thumb instruction")
            (arm_parse_register >>= (fn sp =>
               assertT (is_SP sp)
                 ("arm_parse_srs", "expecting sp")
                 (tryT arm_parse_exclaim (K (return T)) (K (return F)) >>=
                 (fn w =>
                  arm_parse_comma >>-
                  arm_parse_constant >>= (fn i =>
                    let val imm5 = uint_to_word ``:5`` i in
                      return (enc, mk_Store_Return_State (p,inc,w,imm5))
                    end handle HOL_ERR {message,...} =>
                      other_errorT ("arm_parse_srs", message))))))));

val arm_parse_rfe : term -> term -> (term * term) M =
  fn p => fn inc =>
    need_v6 "arm_parse_rfe"
      (thumb2_or_arm_okay "arm_parse_rfe"
       (fn enc =>
          assertT (enc ~~ Encoding_ARM_tm orelse p !~ inc)
            ("arm_parse_rfe", "not available as a Thumb instruction")
            (arm_parse_register >>= (fn rn =>
             tryT arm_parse_exclaim (K (return T)) (K (return F)) >>= (fn w =>
             read_OutsideOrLastInITBlock >>= (fn OutsideOrLastInITBlock =>
               assertT OutsideOrLastInITBlock
                 ("arm_parse_rfe", "must be outside or last in IT block")
                 (return (enc, mk_Return_From_Exception (p,inc,w,rn)))))))));

val arm_parse_svc : (term * term) M =
  arm_parse_constant >>= (fn i =>
  read_thumb >>= (fn thumb =>
    if thumb then
      read_qualifier >>= (fn q =>
        let val v = sint_of_term i in
          assertT (q <> Wide andalso 0 <= v andalso v <= 255)
            ("arm_parse_svc", "narrow only with contant 0-255")
            (return (Encoding_Thumb_tm,
               mk_Supervisor_Call (uint_to_word ``:24`` i)))
        end handle HOL_ERR {message,...} =>
          other_errorT ("arm_parse_svc", message))
    else
      let val imm24 = uint_to_word ``:24`` i in
        return (Encoding_ARM_tm, mk_Supervisor_Call imm24)
      end handle HOL_ERR {message,...} =>
        other_errorT ("arm_parse_svc", message)));

val arm_parse_smc : (term * term) M =
  thumb2_or_arm_okay "arm_parse_smc"
    (fn enc =>
       arm_parse_constant >>= (fn i =>
       read_OutsideOrLastInITBlock >>= (fn OutsideOrLastInITBlock =>
         let val imm4 = uint_to_word ``:4`` i in
           assertT OutsideOrLastInITBlock
             ("arm_parse_smc", "must be outside or last in IT block")
             (return (enc, mk_Secure_Monitor_Call imm4))
         end handle HOL_ERR {message,...} =>
           other_errorT ("arm_parse_smc", message))));

val arm_parse_bkpt : (term * term) M =
  need_v5 "arm_parse_bkpt"
    (arm_parse_constant >>= (fn i =>
     read_thumb >>= (fn thumb =>
       if thumb then
         read_qualifier >>= (fn q =>
           let val v = sint_of_term i in
             assertT (q <> Wide andalso 0 <= v andalso v <= 255)
               ("arm_parse_bkpt", "narrow only with contant 0-255")
               (return (Encoding_Thumb_tm,
                  mk_Breakpoint (uint_to_word ``:16`` i)))
           end handle HOL_ERR {message,...} =>
             other_errorT ("arm_parse_bkpt", message))
       else
         let val imm16 = uint_to_word ``:16`` i in
           return (Encoding_ARM_tm, mk_Breakpoint imm16)
         end handle HOL_ERR {message,...} =>
           other_errorT ("arm_parse_bkpt", message))));

val arm_parse_nop : (term * term) M =
  read_thumb >>= (fn thumb =>
    arch_okay ("arm_parse_nop", "not supported by selected architecture")
      (fn a => has_thumb2 a orelse not thumb andalso a = ARMv6K)
      (if thumb then
         read_qualifier >>= (fn q =>
           return (if q <> Wide then Encoding_Thumb_tm else Encoding_Thumb2_tm,
             mk_Hint Hint_nop_tm))
       else
         return (Encoding_ARM_tm, mk_Hint Hint_nop_tm)));

fun hint YIELD = Hint_yield_tm
  | hint WFE   = Hint_wait_for_event_tm
  | hint WFI   = Hint_wait_for_interrupt_tm
  | hint SEV   = Hint_send_event_tm
  | hint _     = raise ERR "hint" "invalid mnemonic";

val arm_parse_hint : instruction_mnemonic -> (term * term) M =
  fn m =>
    read_thumb >>= (fn thumb =>
      arch_okay ("arm_parse_hint", "not supported by selected architecture")
        (fn a => a = ARMv6T2 orelse version_number a >= 7 orelse
                 not thumb andalso a = ARMv6K)
        (if thumb then
           read_qualifier >>= (fn q =>
             return
              (if q <> Wide then Encoding_Thumb_tm else Encoding_Thumb2_tm,
               mk_Hint (hint m)))
         else
           return (Encoding_ARM_tm, mk_Hint (hint m))));

val arm_parse_dbg : (term * term) M =
  read_thumb >>= (fn thumb =>
    arch_okay ("arm_parse_dbg", "not supported by selected architecture")
      (fn a => a = ARMv6T2 orelse version_number a >= 7 orelse
               not thumb andalso a = ARMv6K)
      (arm_parse_constant >>= (fn i =>
         let val v = sint_of_term i in
           assertT (0 <= v andalso v <= 15)
             ("arm_parse_dbg", "constant must be in range 0-15")
             (let val instr = mk_Hint (mk_Hint_debug (mk_word4 v)) in
                if thumb then
                  not_narrow "arm_parse_dbg"
                    (return (Encoding_Thumb2_tm, instr))
                else
                  return (Encoding_ARM_tm, instr)
              end)
         end)));

(* ------------------------------------------------------------------------- *)

val arm_parse_enterx_leavex : term -> (term * term) M =
  fn is_enterx =>
    need_v7 "arm_parse_enterx"
      (thumb2_okay "arm_parse_enterx"
         (return (Encoding_Thumb2_tm, mk_Enterx_Leavex is_enterx)));

val arm_parse_check_array : (term * term) M =
  read_thumbee >>= (fn thumbee =>
  read_qualifier >>= (fn q =>
    assertT (thumbee andalso q <> Wide)
      ("arm_parse_check_array", "only available as narrow ThumbEE instruction")
      (arm_parse_register >>= (fn rn =>
       arm_parse_comma >>-
       arm_parse_register >>= (fn rm =>
         return (Encoding_ThumbEE_tm, mk_Check_Array (rn,rm)))))));

val arm_parse_handler_branch_link : term -> (term * term) M =
  fn link =>
    read_thumbee >>= (fn thumbee =>
    read_qualifier >>= (fn q =>
      assertT (thumbee andalso q <> Wide)
        ("arm_parse_handler_branch_link",
         "only available as narrow ThumbEE instruction")
        (arm_parse_constant >>= (fn i =>
          let val h = uint_to_word ``:8`` i in
            return (Encoding_ThumbEE_tm, mk_Handler_Branch_Link (link,h))
          end handle HOL_ERR {message,...} =>
            other_errorT ("arm_parse_handler_branch_link", message)))));

val arm_parse_handler_branch_parameter : (term * term) M =
  read_thumbee >>= (fn thumbee =>
  read_qualifier >>= (fn q =>
    assertT (thumbee andalso q <> Wide)
      ("arm_parse_handler_branch_parameter",
       "only available as narrow ThumbEE instruction")
      (arm_parse_constant >>= (fn i =>
       arm_parse_comma >>-
       arm_parse_constant >>= (fn j =>
        let val imm3 = uint_to_word ``:3`` i
            val h = uint_to_word ``:5`` j
        in
          return (Encoding_ThumbEE_tm, mk_Handler_Branch_Parameter (imm3,h))
        end handle HOL_ERR {message,...} =>
          other_errorT ("arm_parse_handler_branch_parameter", message))))));

val arm_parse_handler_branch_link_parameter : (term * term) M =
  read_thumbee >>= (fn thumbee =>
  read_qualifier >>= (fn q =>
    assertT (thumbee andalso q <> Wide)
      ("arm_parse_handler_branch_link_parameter",
       "only available as narrow ThumbEE instruction")
      (arm_parse_constant >>= (fn i =>
       arm_parse_comma >>-
       arm_parse_constant >>= (fn j =>
        let val imm5 = uint_to_word ``:5`` i
            val h = uint_to_word ``:5`` j
        in
          return
            (Encoding_ThumbEE_tm,
             mk_Handler_Branch_Link_Parameter (imm5,h))
        end handle HOL_ERR {message,...} =>
          other_errorT
            ("arm_parse_handler_branch_link_parameter", message))))));

(* ------------------------------------------------------------------------- *)

val arm_parse_ldc_stc : instruction_mnemonic -> (term * term) M =
  fn m =>
    thumb2_or_arm_okay "arm_parse_smc"
    (fn enc =>
       arm_parse_coprocessor >>= (fn coproc =>
       arm_parse_comma >>-
       arm_parse_cregister >>= (fn crd =>
       arm_parse_comma >>-
       arm_parse_lsquare >>-
       arm_parse_register >>= (fn rn =>
       tryT arm_parse_rsquare
         (fn _ =>
            tryT arm_parse_comma
              (fn _ =>
                 tryT arm_parse_constant
                   (fn i =>
                      let val v = sint_of_term i in
                        assertT
                          (v mod 4 = 0 andalso ~1020 <= v andalso v <= 1020)
                          ("arm_parse_ldc_stc",
                           "offset not aligned or beyond permitted range\
                           \ (+/-1020)")
                          (return
                             (F,mk_bool (0 <= v andalso not (i ~~ ``-0i``)),T,
                              mk_word8 (Int.abs (v div 4))))
                      end handle HOL_ERR {message,...} =>
                        other_errorT ("arm_parse_ldc_stc", message))
                   (fn _ =>
                      arm_parse_lbrace >>-
                      arm_parse_number >>= (fn i =>
                      arm_parse_rbrace >>-
                        let val imm8 = int_to_word ``:8`` i in
                          return (F,T,F,imm8)
                        end handle HOL_ERR {message,...} =>
                          other_errorT ("arm_parse_ldc_stc", message))))
              (fn _ => return (T,T,F,mk_word8 0)))
         (fn _ =>
            arm_parse_comma >>-
            arm_parse_constant >>= (fn i =>
            arm_parse_rsquare >>-
            tryT arm_parse_exclaim (K (return T)) (K (return F)) >>= (fn w =>
              let val v = sint_of_term i in
                assertT
                  (v mod 4 = 0 andalso ~1020 <= v andalso v <= 1020)
                  ("arm_parse_ldc_stc",
                   "offset not aligned or beyond permitted range (+/-1020)")
                  (return (T,mk_bool (0 <= v andalso not (i ~~ ``-0i``)),w,
                           mk_word8 (Int.abs (v div 4))))
              end handle HOL_ERR {message,...} =>
                other_errorT ("arm_parse_ldc_stc", message)))) >>=
        (fn (p,u,w,imm8) =>
           return (enc,
            case m
            of LDC   => mk_Coprocessor_Load  (p,u,F,w,rn,crd,coproc,imm8)
             | LDC2  => mk_Coprocessor_Load  (p,u,F,w,rn,crd,coproc,imm8)
             | LDCL  => mk_Coprocessor_Load  (p,u,T,w,rn,crd,coproc,imm8)
             | LDC2L => mk_Coprocessor_Load  (p,u,T,w,rn,crd,coproc,imm8)
             | STC   => mk_Coprocessor_Store (p,u,F,w,rn,crd,coproc,imm8)
             | STC2  => mk_Coprocessor_Store (p,u,F,w,rn,crd,coproc,imm8)
             | STCL  => mk_Coprocessor_Store (p,u,T,w,rn,crd,coproc,imm8)
             | STC2L => mk_Coprocessor_Store (p,u,T,w,rn,crd,coproc,imm8)
             | _ => raise ERR "arm_parse_ldc_stc" "unexpected mnemonic"))))));

val arm_parse_cdp : (term * term) M =
  thumb2_or_arm_okay "arm_parse_smc"
  (fn enc =>
     arm_parse_coprocessor >>= (fn coproc =>
     arm_parse_comma >>-
     arm_parse_constant >>= (fn opc1 =>
     arm_parse_comma >>-
     arm_parse_cregister >>= (fn crd =>
     arm_parse_comma >>-
     arm_parse_cregister >>= (fn crn =>
     arm_parse_comma >>-
     arm_parse_cregister >>= (fn crm =>
     tryT (arm_parse_comma >>- arm_parse_constant)
       (fn i =>
          let val imm3 = int_to_word ``:3`` i in
            return imm3
          end handle HOL_ERR {message,...} =>
            other_errorT ("arm_parse_cdp", message))
       (fn _ => return (mk_word3 0)) >>= (fn opc2 =>
       let val imm4 = int_to_word ``:4`` opc1 in
         return (enc,
           mk_Coprocessor_Data_Processing (imm4,crn,crd,coproc,opc2,crm))
       end handle HOL_ERR {message,...} =>
         other_errorT ("arm_parse_cdp", message))))))));

val arm_parse_mrc_mcr : instruction_mnemonic -> (term * term) M =
  fn m =>
    thumb2_or_arm_okay "arm_parse_smc"
    (fn enc =>
       arm_parse_coprocessor >>= (fn coproc =>
       arm_parse_comma >>-
       arm_parse_constant >>= (fn opc1 =>
       arm_parse_comma >>-
       arm_parse_register >>= (fn rt =>
       arm_parse_comma >>-
       arm_parse_cregister >>= (fn crn =>
       arm_parse_comma >>-
       arm_parse_cregister >>= (fn crm =>
       tryT (arm_parse_comma >>- arm_parse_constant)
         (fn i =>
            let val imm3 = int_to_word ``:3`` i in
              return imm3
            end handle HOL_ERR {message,...} =>
              other_errorT ("arm_parse_mrc_mcr", message))
         (fn _ => return (mk_word3 0)) >>= (fn opc2 =>
         let val imm3 = int_to_word ``:3`` opc1
             val b = mk_bool (m = MRC orelse m = MRC2)
         in
           return (enc, mk_Coprocessor_Transfer (imm3,b,crn,rt,coproc,opc2,crm))
         end handle HOL_ERR {message,...} =>
           other_errorT ("arm_parse_mrc_mcr", message))))))));

val arm_parse_mrrc_mcrr : instruction_mnemonic -> (term * term) M =
  fn m =>
    thumb2_or_arm_okay "arm_parse_smc"
    (fn enc =>
       arm_parse_coprocessor >>= (fn coproc =>
       arm_parse_comma >>-
       arm_parse_constant >>= (fn opc1 =>
       arm_parse_comma >>-
       arm_parse_register >>= (fn rt =>
       arm_parse_comma >>-
       arm_parse_register >>= (fn rt2 =>
       arm_parse_comma >>-
       arm_parse_cregister >>= (fn crm =>
         let val imm4 = int_to_word ``:4`` opc1
             val b = mk_bool (m = MRRC orelse m = MRRC2)
         in
           return (enc, mk_Coprocessor_Transfer_Two (b,rt2,rt,coproc,imm4,crm))
         end handle HOL_ERR {message,...} =>
           other_errorT ("arm_parse_mrrc_mcrr", message)))))));

(* ------------------------------------------------------------------------- *)

datatype line
  = Align of int
  | Ascii1 of string
  | Label of int * string
  | Byte1 of term list
  | Short1 of term list
  | Word1 of term list
  | Space of term
  | Instruction1 of int * term * term * term;

val arm_parse_instruction : line M =
  arm_parse_mnemonic >>= (fn m =>
   (case m
    of B      => arm_parse_branch_target
     | BL     => arm_parse_branch_link
     | BLX    => arm_parse_branch_link_exchange
     | BX     => arm_parse_bx
     | BFC    => arm_parse_sbfx_etc m
     | BFI    => arm_parse_sbfx_etc m
     | CBZ    => arm_parse_cbz_cbnz F
     | CBNZ   => arm_parse_cbz_cbnz T
     | CLZ    => arm_parse_clz
     | CLREX  => arm_parse_clrex
     | CDP    => arm_parse_cdp
     | CDP2   => arm_parse_cdp
     | CHKA   => arm_parse_check_array
     | ENTERX => arm_parse_enterx_leavex T
     | LEAVEX => arm_parse_enterx_leavex F
     | HB     => arm_parse_handler_branch_link F
     | HBL    => arm_parse_handler_branch_link T
     | HBLP   => arm_parse_handler_branch_link_parameter
     | HBP    => arm_parse_handler_branch_parameter
     | IT     => arm_parse_it
     | ADR    => arm_parse_adr
     | ADDW   => arm_parse_addw_subw T
     | SUBW   => arm_parse_addw_subw F
     | RRX    => arm_parse_rrx
     | MOVW   => arm_parse_mov_halfword F
     | MOVT   => arm_parse_mov_halfword T
     | MUL    => arm_parse_mul
     | PKHBT  => arm_parse_pkh F
     | PKHTB  => arm_parse_pkh T
     | REV    => arm_parse_rev m
     | REV16  => arm_parse_rev m
     | REVSH  => arm_parse_rev m
     | RBIT   => arm_parse_rbit
     | UDIV   => arm_parse_div T
     | SDIV   => arm_parse_div F
     | SSAT   => arm_parse_ssat_usat false
     | USAT   => arm_parse_ssat_usat true
     | SSAT16 => arm_parse_ssat16_usat16 false
     | USAT16 => arm_parse_ssat16_usat16 true
     | SXTB   => arm_parse_sxtb_etc m
     | UXTB   => arm_parse_sxtb_etc m
     | SXTH   => arm_parse_sxtb_etc m
     | UXTH   => arm_parse_sxtb_etc m
     | SXTB16 => arm_parse_sxtb16_uxtb16 F
     | UXTB16 => arm_parse_sxtb16_uxtb16 T
     | SBFX   => arm_parse_sbfx_etc m
     | UBFX   => arm_parse_sbfx_etc m
     | DMB    => arm_parse_barrier m
     | DSB    => arm_parse_barrier m
     | ISB    => arm_parse_barrier m
     | CPS    => arm_parse_cps
     | CPSIE  => arm_parse_cpsie_cpsid (mk_word2 2)
     | CPSID  => arm_parse_cpsie_cpsid (mk_word2 3)
     | SETEND => arm_parse_setend
     | SVC    => arm_parse_svc
     | SMC    => arm_parse_smc
     | BKPT   => arm_parse_bkpt
     | NOP    => arm_parse_nop
     | DBG    => arm_parse_dbg
     | LDMIA  => arm_parse_ldm_stm true F T
     | LDMDA  => arm_parse_ldm_stm true F F
     | LDMDB  => arm_parse_ldm_stm true T F
     | LDMIB  => arm_parse_ldm_stm true T T
     | LDR    => arm_parse_mode2 true F
     | LDRB   => arm_parse_mode2 true T
     | LDRH   => arm_parse_mode3 (SOME (F,T))
     | LDRSB  => arm_parse_mode3 (SOME (T,F))
     | LDRSH  => arm_parse_mode3 (SOME (T,T))
     | LDRD   => arm_parse_mode3_dual true
     | LDREX  => arm_parse_ldrex
     | LDREXB => arm_parse_ldrexb_ldrexh false
     | LDREXD => arm_parse_ldrexd
     | LDREXH => arm_parse_ldrexb_ldrexh true
     | MRS    => arm_parse_mrs
     | MSR    => arm_parse_msr
     | POP    => arm_parse_pop_push true
     | PUSH   => arm_parse_pop_push false
     | RFEIA  => arm_parse_rfe F T
     | RFEDA  => arm_parse_rfe F F
     | RFEDB  => arm_parse_rfe T F
     | RFEIB  => arm_parse_rfe T T
     | STMIA  => arm_parse_ldm_stm false F T
     | STMDA  => arm_parse_ldm_stm false F F
     | STMDB  => arm_parse_ldm_stm false T F
     | STMIB  => arm_parse_ldm_stm false T T
     | STR    => arm_parse_mode2 false F
     | STRB   => arm_parse_mode2 false T
     | STRH   => arm_parse_mode3 NONE
     | STRD   => arm_parse_mode3_dual false
     | STRT   => arm_parse_mode2_unpriv false F
     | STRBT  => arm_parse_mode2_unpriv false T
     | STRHT  => arm_parse_mode3_unpriv NONE
     | STREX  => arm_parse_strex
     | STREXB => arm_parse_strexb_strexh false
     | STREXD => arm_parse_strexd
     | STREXH => arm_parse_strexb_strexh true
     | SWP    => arm_parse_swp F
     | SWPB   => arm_parse_swp T
     | SRSIA  => arm_parse_srs F T
     | SRSDA  => arm_parse_srs F F
     | SRSDB  => arm_parse_srs T F
     | SRSIB  => arm_parse_srs T T
     | TBB    => arm_parse_tbb
     | TBH    => arm_parse_tbh
     | PLD    => arm_parse_pld_pli (SOME false)
     | PLDW   => arm_parse_pld_pli (SOME true)
     | PLI    => arm_parse_pld_pli NONE
     | LDRT   => arm_parse_mode2_unpriv true F
     | LDRBT  => arm_parse_mode2_unpriv true T
     | LDRHT  => arm_parse_mode3_unpriv (SOME (F,T))
     | LDRSBT => arm_parse_mode3_unpriv (SOME (T,F))
     | LDRSHT => arm_parse_mode3_unpriv (SOME (T,T))
     | _ => (if is_data_processing3 m then
               arm_parse_data_processing3 m
             else if is_data_processing2 m then
               arm_parse_data_processing2 m
             else if mem m [LSL,ASR,LSR,ROR] then
               arm_parse_mov_shift m
             else if is_thumb2_3 m then
               arm_parse_thumb2_3
             else if is_thumb2_4 m then
               arm_parse_thumb2_4
             else if mem m [SXTAB,UXTAB,SXTAB16,UXTAB16,SXTAH,UXTAH] then
               arm_parse_sxtab_etc m
             else if mem m [YIELD,WFI,WFE,SEV] then
               arm_parse_hint m
             else if mem m [LDC,LDCL,LDC2,LDC2L,STC,STCL,STC2,STC2L] then
               arm_parse_ldc_stc m
             else if mem m [MRC,MRC2,MCR,MCR2] then
               arm_parse_mrc_mcr m
             else if mem m [MRRC,MRRC2,MCRR,MCRR2] then
               arm_parse_mrrc_mcrr m
             else
               other_errorT
                 ("arm_parse_instruction", "not supported yet"))) >>=
   (fn (enc,tm) =>
      if m = IT andalso enc ~~ boolSyntax.arb then
        write_instruction NONE >>- return (Space ``0i``)
      else
        read_cond >>= (fn cond =>
        write_instruction NONE >>-
        (if m <> IT then next_itstate else return ()) >>-
        read_linenumber >>= (fn line =>
          return (Instruction1 (line,enc,cond,tm))))));

local
  val arch_versions =
    ["armv4", "armv4t", "armv5t", "armv5te",
     "armv6", "armv6k", "armv6t2", "armv7"]
in
  val arm_parse_arch : unit M =
    arm_parse_strings arch_versions >>= (fn v =>
      case v
      of "armv4"   => write_arch ARMv4
       | "armv4t"  => write_arch ARMv4T
       | "armv5t"  => write_arch ARMv5T
       | "armv5te" => write_arch ARMv5TE
       | "armv6"   => write_arch ARMv6
       | "armv6k"  => write_arch ARMv6K
       | "armv6t2" => write_arch ARMv6T2
       | "armv7"   => tryT arm_parse_minus
                        (fn _ =>
                           arm_parse_strings ["a","m","r"] >>= (fn s =>
                             case s
                             of "a" => write_arch ARMv7_A
                              | "r" => write_arch ARMv7_R
                              | _ => raise ERR "arm_parse_arch" ""))
                        (fn _ => write_arch ARMv7_A)
       | _ => raise ERR "arm_parse_arch" "")
end;

val switch_to_arm : unit M = write_code ARM_CODE;

val switch_to_thumb : unit M =
  read_arch >>= (fn a =>
    assertT (a <> ARMv4)
    ("switch_to_thumb", "ARMv4 does not support Thumb")
    (write_code THUMB_CODE));

val switch_to_thumbx : unit M =
  read_arch >>= (fn a =>
    assertT (a = ARMv7_A orelse a = ARMv7_R)
    ("switch_to_thumb", "ThumbEE not supported before ARMv7")
    (write_code THUMBX_CODE));

local
  fun arm_parse_number_list (l : term list) (P : term -> bool) : term list M =
    tryT arm_parse_signed_number
      (fn h =>
         assertT (P h)
           ("arm_parse_number_list", "number not in expected range")
           (tryT arm_parse_comma
              (fn _ => arm_parse_number_list (l @ [h]) P)
              (fn _ => return (l @ [h]))))
      (fn _ =>
        assertT (not (null l))
         ("arm_parse_number_list", "not a valid number list")
         (return l))

  fun in_range (mn,mx) tm =
    let val v = sint_of_term tm in
      mn <= v andalso v <= mx
    end handle HOL_ERR _ => false | Overflow => false;

  val word_min = Arbint.~ (Arbint.fromString "2147483648")
  val word_max = Arbint.fromString "4294967295"
in
  val arm_parse_number_list = arm_parse_number_list []

  val is_byte  = in_range (~128,255)
  val is_short = in_range (~32768,65535)
  fun is_word tm =
    let open Arbint
        val v = intSyntax.int_of_term tm
    in
      word_min <= v andalso v <= word_max
    end handle HOL_ERR _ => false;
end;

val arm_parse_align : line M =
  tryT (arm_parse_strings ["2","4","8"])
    (fn i =>
      case i
        of "2" => return (Align 2)
         | "4" => return (Align 4)
         | "8" => return (Align 8)
         | _ => raise ERR "arm_parse_align" "")
    (fn _ =>
       read_thumb >>= (fn thumb => return (Align (if thumb then 2 else 4))));

local
  val directives =
    ["arch","code","code16","code32","arm","thumb","thumbx",
     "ascii","byte","short","word","align","space"]
in
  val arm_parse_line : line list M =
    tryT (arm_parse_strings directives)
      (fn s =>
        (case s
         of "arch" => arm_parse_arch >>- return []
          | "code" => arm_parse_strings ["16","32"] >>= (fn i =>
                        (case i
                         of "16" => switch_to_thumb >>- return ([Align 2])
                          | "32" => switch_to_arm >>- return ([Align 4])
                          | _ => raise ERR "arm_parse_directive" ""))
          | "arm"    => switch_to_arm >>- return ([Align 4])
          | "code32" => switch_to_arm >>- return ([Align 4])
          | "thumb"  => switch_to_thumb >>- return ([Align 2])
          | "code16" => switch_to_thumb >>- return ([Align 2])
          | "thumbx" => switch_to_thumbx >>- return ([Align 2])
          | "ascii"  => arm_parse_string_const >>= (fn s =>
                          assertT (Lib.all Char.isAscii (explode s))
                            ("arm_parse_line", "not an Ascii string")
                            (return ([Ascii1 s])))
          | "byte"   => arm_parse_number_list is_byte >>= (fn l =>
                          return ([Byte1 l]))
          | "short"  => arm_parse_number_list is_short >>= (fn l =>
                          return ([Short1 l]))
          | "word"   => arm_parse_number_list is_word >>= (fn l =>
                          return ([Word1 l]))
          | "space"  => arm_parse_number >>= (fn i => return ([Space i]))
          | "align"  => arm_parse_align >>= (fn l => return ([l]))
          | _ => raise ERR "arm_parse_directive" ""))
      (fn _ => arm_parse_instruction >>= (fn instr => return ([instr]))) >>=
    (fn l => arm_parse_endline >>- return l)
end;

val arm_parse_label : line list M =
  arm_parse_variable ``:unit`` >>= (fn label =>
  arm_parse_colon >>-
  read_linenumber >>= (fn line =>
    return ([Label (line,label |> dest_var |> fst)])));

val arm_parse_labelled_line : line list M =
  tryT arm_parse_endline (fn _ => return []) (fn _ =>
  tryT arm_parse_label return (fn _ => return []) >>=
   (fn label =>
      tryT arm_parse_endline (fn _ => return label)
        (fn _ => arm_parse_line >>= (fn l => return (label @ l)))));

fun arm_parse_lines (l1 : line list) : line list M =
  arm_parse_endoffile >>= (fn endoffile =>
    if endoffile then
      read_InITBlock >>= (fn InITBlock =>
        let val _ = if InITBlock then
                      HOL_WARNING "arm_parserLib" "arm_parse_lines"
                                  "code finished before end of IT block"
                    else ()
        in
          return l1
        end)
    else
      arm_parse_labelled_line >>= (fn l2 => arm_parse_lines (l1 @ l2)));

(* ------------------------------------------------------------------------- *)

datatype arm_code
  = Ascii of string
  | Byte of term list
  | Short of term list
  | Word of term list
  | Instruction of term * term * term;

fun arm_code_cmp (Ascii s1, Ascii s2) = String.compare (s1,s2)
  | arm_code_cmp (Ascii _, _) = LESS
  | arm_code_cmp (_, Ascii _) = GREATER
  | arm_code_cmp (Byte tl1, Byte tl2) = list_compare Term.compare (tl1, tl2)
  | arm_code_cmp (Byte _, _) = LESS
  | arm_code_cmp (_, Byte _) = GREATER
  | arm_code_cmp (Short tl1, Short tl2) = list_compare Term.compare (tl1, tl2)
  | arm_code_cmp (Short _, _) = LESS
  | arm_code_cmp (_, Short _) = GREATER
  | arm_code_cmp (Word tl1, Word tl2) = list_compare Term.compare (tl1, tl2)
  | arm_code_cmp (Word _, _) = LESS
  | arm_code_cmp (_, Word _) = GREATER
  | arm_code_cmp (Instruction(t1,t2,t3), Instruction(ta, tb, tc)) =
      list_compare Term.compare ([t1,t2,t3], [ta,tb,tc])

fun arm_code_eq ac1 ac2 = arm_code_cmp(ac1,ac2) = EQUAL


local
  open Arbnum
  val n4 = fromInt 4
in
  fun align (line,e) =
       line + (if e ~~ Encoding_ARM_tm then
                 (n4 - (line mod n4)) mod n4
               else
                 (two - (line mod two)) mod two)

  fun inc_code_width line (Label _) = line
    | inc_code_width line (Ascii1 s) = line + (s |> String.size |> fromInt)
    | inc_code_width line (Byte1 l)  = line + (l |> List.length |> fromInt)
    | inc_code_width line (Short1 l) =
        line + (l |> List.length |> fromInt |> times2)
    | inc_code_width line (Word1 l) =
        line + (l |> List.length |> fromInt) * n4
    | inc_code_width line (Space n) =
        line + (n |> intSyntax.int_of_term |> Arbint.toNat)
    | inc_code_width line (Align i) =
        let val n = fromInt i in line + (n - (line mod n)) mod n end
    | inc_code_width line (Instruction1 (_,e,_,_)) =
        align (line,e) +
        (if e ~~ Encoding_Thumb_tm orelse e ~~ Encoding_ThumbEE_tm then
           two
         else
           n4)
end;

local
  val n4 = Arbnum.fromInt 4
  val vname = fst o dest_var

  fun Add_Sub_label tm =
        let val (_,_,_,imm12) = dest_Add_Sub tm in vname imm12 end

  fun Load_label tm =
        let val (_,_,_,_,_,_,_,mode2) = dest_Load tm in vname mode2 end

  fun find_forward _ _ [] = raise ERR "find_forward" "label not found"
    | find_forward (x as (line,v)) n ((Label (_,s))::t) =
        if v = s then
          SOME (Arbint.-(Arbint.fromNat n,Arbint.fromNat (Arbnum.+(line,n4))))
        else
          find_forward x n t
    | find_forward x n ((c as Instruction1 (_,enc,_,_))::t) =
        if is_genvar enc then
          NONE
        else
          find_forward x (inc_code_width n c) t
    | find_forward x n (h::t) = find_forward x (inc_code_width n h) t;

  fun inst_enc (Instruction1 (_,e,_,_)) = e
    | inst_enc _ = raise ERR "inst_enc" "";

  fun number_lines [] (line,code,lmap) = (code,lmap)
    | number_lines (h::t) (line,code,lmap) =
        number_lines t
        (case h
         of Align n  => (inc_code_width line h,code,lmap)
          | Space t  => (inc_code_width line h,code,lmap)
          | Ascii1 s => (inc_code_width line h,(line,h)::code,lmap)
          | Byte1 t  => (inc_code_width line h,(line,h)::code,lmap)
          | Short1 t => (inc_code_width line h,(line,h)::code,lmap)
          | Word1 t  => (inc_code_width line h,(line,h)::code,lmap)
          | Label (i,s) =>
              let val _ = not (isSome (Redblackmap.peek (lmap,s))) orelse
                   raise ERR "number_lines"
                     ("label " ^ s ^ " duplicated on line " ^ Int.toString i)
              in
                (line,code,Redblackmap.insert (lmap,s,line))
              end
          | Instruction1 (i,enc,cond,tm) =>
              let val h' =
                if not (is_genvar enc) then
                  h
                else
                  let fun pick b = Instruction1
                                      (i,if b then Encoding_Thumb_tm
                                              else Encoding_Thumb2_tm,cond,tm)
                  in
                    if is_Branch_Target tm then
                      let val v = vname (dest_Branch_Target tm) in
                        case Redblackmap.peek (lmap,v)
                        of SOME address =>
                             let open Arbnum
                                 val offset = line + n4 - address
                                 val narrow_okay =
                                       if is_AL cond then
                                         offset <= (fromString "2048")
                                       else
                                         offset <= (fromString "256")
                             in
                               pick narrow_okay
                             end
                         | NONE =>
                             let open Arbint in
                               case find_forward (line,v)
                                      (inc_code_width line (pick true)) t
                               of SOME offset =>
                                    let val narrow_okay =
                                              if is_AL cond then
                                                (fromString "-2048") <= offset
                                                andalso
                                                offset <= (fromString "2046")
                                              else
                                                (fromString "-256") <= offset
                                                andalso
                                                offset <= (fromString "254")
                                    in
                                      pick narrow_okay
                                    end
                                | NONE => pick false
                             end handle HOL_ERR _ =>
                               raise ERR "number_lines" ("cannot find label " ^
                                 v ^ " on line " ^ Int.toString i)
                      end
                    else if is_Add_Sub tm orelse is_Load tm then
                      let val v = if is_Add_Sub tm then
                                    Add_Sub_label tm
                                  else
                                    Load_label tm
                      in
                        case Redblackmap.peek (lmap,v)
                        of SOME _ => pick false
                         | NONE =>
                             let open Arbint in
                               case find_forward (line,v)
                                      (inc_code_width line (pick true)) t
                               of SOME offset =>
                                    let val narrow_okay =
                                              offset mod (fromInt 4) = zero
                                              andalso
                                              (fromString "0") <= offset
                                              andalso
                                              offset <= (fromString "1020")
                                    in
                                      pick narrow_okay
                                    end
                                | NONE => pick false
                             end handle HOL_ERR _ =>
                               raise ERR "number_lines" ("cannot find label " ^
                                 v ^ " on line " ^ Int.toString i)
                      end
                    else raise ERR "number_lines" "unexpected genvar"
                  end
              in
                (inc_code_width line h',(align (line,inst_enc h'),h')::code,
                 lmap)
              end)

  fun link_lines (l1,lmap) =
    let
      fun in_range (mn,mx) i = mn <= i andalso i <= mx
      fun aligned (i,n) = i mod n = 0
      fun enc_pc n enc =
            let open Arbint in
              fromNat n + fromInt (if enc ~~ Encoding_ARM_tm then 8 else 4)
            end
      fun align_pc n enc =
            let open Arbint
                val i4 = fromInt 4
                val pc = enc_pc n enc
            in
              (pc div i4) * i4
            end
      fun link_instruction i pc v f =
            case Redblackmap.peek (lmap,v)
            of SOME target =>
                 let open Arbint
                 in f (intSyntax.term_of_int (fromNat target - pc)) end
             | NONE => raise ERR "link_instruction"
                 ("failed to find label " ^ v ^ " on line " ^ Int.toString i)
      fun offset_to_int i offset =
            sint_of_term offset handle Overflow => raise ERR "link_instruction"
              ("offset caused overflow on line " ^ Int.toString i)
      fun ilink_instruction i pc v f =
            link_instruction i pc v (f o offset_to_int i)
      fun recurse [] code = code
        | recurse ((x,Ascii1 s)::t) code = recurse t ((x,Ascii s)::code)
        | recurse ((x,Byte1 l)::t) code  = recurse t ((x,Byte l)::code)
        | recurse ((x,Short1 l)::t) code = recurse t ((x,Short l)::code)
        | recurse ((x,Word1 l)::t) code  = recurse t ((x,Word l)::code)
        | recurse ((x,Instruction1 (i,enc,cond,tm))::t) code =
            if null (free_vars tm) then
              recurse t ((x,Instruction (enc,cond,tm))::code)
            else
              let val tm' =
                    if is_Branch_Target tm then
                      let val v = vname (dest_Branch_Target tm) in
                        ilink_instruction i (enc_pc x enc) v
                          (fn offset =>
                             let val narrow_okay =
                                       aligned (offset,2) andalso
                                       if is_var cond orelse is_AL cond then
                                         in_range (~2048,2046) offset
                                       else
                                         in_range (~256,254) offset
                                 val wide_okay =
                                       aligned (offset,2) andalso
                                       if is_var cond orelse is_AL cond then
                                         in_range (~16777216,16777214) offset
                                       else
                                         in_range (~1048576,1048574) offset
                                 val arm_okay =
                                       aligned (offset,4) andalso
                                       in_range (~33554432,33554428) offset
                                 val imm24 = offset_to_imm24 (offset div
                                               (if enc ~~ Encoding_ARM_tm
                                                then 4 else 2))
                             in
                               if enc ~~ Encoding_Thumb_tm andalso narrow_okay
                                  orelse
                                  enc ~~ Encoding_Thumb2_tm andalso wide_okay
                                  orelse
                                  enc ~~ Encoding_ARM_tm andalso arm_okay
                               then
                                 mk_Branch_Target imm24
                               else
                                 raise ERR "link_lines" ("branch target " ^ v ^
                                    " unaligned or beyond permitted range on\
                                    \ line " ^ Int.toString i)
                             end)
                      end
                    else if is_Branch_Link_Exchange_Immediate tm then
                      let val (h,toARM,imm24) =
                                 dest_Branch_Link_Exchange_Immediate tm
                          val v = vname imm24
                      in
                        ilink_instruction i
                          ((if is_T toARM then align_pc else enc_pc) x enc) v
                          (fn offset =>
                             let val wide_okay =
                                       if is_T toARM then
                                         aligned (offset,4) andalso
                                         in_range (~16777216,16777212) offset
                                       else
                                         aligned (offset,2) andalso
                                         in_range (~16777216,16777214) offset
                                 val arm_okay =
                                       if is_T toARM then
                                         aligned (offset,4) andalso
                                         in_range (~33554432,33554428) offset
                                       else
                                         aligned (offset,2) andalso
                                         in_range (~33554432,33554430) offset
                                 val h' = mk_bool ((offset div 2) mod 2 = 1)
                                 val imm24 = offset_to_imm24 (offset div 4)
                             in
                               if (is_arb h orelse is_F h') andalso
                                  (enc ~~ Encoding_Thumb2_tm andalso wide_okay
                                   orelse
                                   enc ~~ Encoding_ARM_tm andalso arm_okay)
                               then
                                 mk_Branch_Link_Exchange_Immediate
                                   (h',toARM,imm24)
                               else
                                 raise ERR "link_lines" ("branch target " ^ v ^
                                    " unaligned or beyond permitted range\
                                    \ on line " ^ Int.toString i)
                             end)
                      end
                    else if is_Compare_Branch tm then
                      let val (nonzero,imm6,n) = dest_Compare_Branch tm
                          val v = vname imm6
                      in
                        ilink_instruction i (enc_pc x enc) v
                          (fn offset =>
                             if enc ~~ Encoding_Thumb_tm andalso
                                aligned (offset,2) andalso
                                in_range (0,126) offset
                             then
                               mk_Compare_Branch (nonzero,
                                 wordsSyntax.mk_wordii (offset div 2,6),n)
                             else
                               raise ERR "link_lines" ("branch target " ^ v ^
                                  " unaligned or beyond permitted range on\
                                  \ line " ^ Int.toString i))
                      end
                    else if is_Add_Sub tm then
                      let val (a,n,d,imm12) = dest_Add_Sub tm
                          val v = vname imm12
                      in
                        link_instruction i (align_pc x enc) v
                          (fn tm =>
                             if enc ~~ Encoding_ARM_tm then
                               case total (mode1_immediate2 false ADD) tm
                               of SOME (opc,imm12) =>
                                    mk_Add_Sub
                                      (mk_bool (opc ~~ dp_opcode ADD),n,d,imm12)
                                | NONE =>
                                    raise ERR "link_lines" ("cannot represent\
                                      \ offset to label " ^ v ^ " as a mode1\
                                      \ immmediate on line " ^ Int.toString i)
                             else
                               let val offset = offset_to_int i tm
                                   val narrow_okay =
                                         aligned (offset,4) andalso
                                         in_range (0,1020) offset
                                   val wide_okay =
                                         in_range (~4095,4095) offset
                                   val imm12 = mk_word12 (Int.abs offset)
                             in
                               if enc ~~ Encoding_Thumb_tm andalso narrow_okay
                                  orelse
                                  enc ~~ Encoding_Thumb2_tm andalso wide_okay
                               then
                                 mk_Add_Sub (mk_bool (0 <= offset),n,d,imm12)
                               else
                                 raise ERR "link_lines"
                                   ("address target " ^ v ^
                                    " unaligned or beyond permitted range on\
                                    \ line " ^ Int.toString i)
                             end)
                      end
                    else if is_Preload_Data tm then
                      let val (a,w,n,mode2) = dest_Preload_Data tm
                          val v = vname mode2
                      in
                        ilink_instruction i (align_pc x enc) v
                          (fn offset =>
                             if in_range (~4095,4095) offset andalso
                                (enc ~~ Encoding_Thumb2_tm orelse
                                 enc ~~ Encoding_ARM_tm)
                             then
                               mk_Preload_Data (mk_bool (0 <= offset),w,n,
                                mk_Mode2_immediate (mk_word12 (Int.abs offset)))
                             else
                               raise ERR "link_lines" ("load target " ^ v ^
                                  " unaligned or beyond permitted range\
                                  \ on line " ^ Int.toString i))
                      end
                    else if is_Preload_Instruction tm then
                      let val (a,n,mode2) = dest_Preload_Instruction tm
                          val v = vname mode2
                      in
                        ilink_instruction i (align_pc x enc) v
                          (fn offset =>
                             if in_range (~4095,4095) offset andalso
                                (enc ~~ Encoding_Thumb2_tm orelse
                                 enc ~~ Encoding_ARM_tm)
                             then
                               mk_Preload_Instruction (mk_bool (0 <= offset),n,
                                mk_Mode2_immediate (mk_word12 (Int.abs offset)))
                             else
                               raise ERR "link_lines" ("load target " ^ v ^
                                  " unaligned or beyond permitted range\
                                  \ on line " ^ Int.toString i))
                      end
                    else if is_Load tm then
                      let val (indx,a,b,w,u,n,t,mode2) = dest_Load tm
                          val v = vname mode2
                      in
                        ilink_instruction i (align_pc x enc) v
                          (fn offset =>
                             let val narrow_okay =
                                       aligned (offset,4) andalso
                                       in_range (0,1020) offset
                                 val wide_okay =
                                       in_range (~4095,4095) offset
                                 val mode2 = mk_Mode2_immediate
                                              (mk_word12 (Int.abs offset))
                             in
                               if enc ~~ Encoding_Thumb_tm andalso narrow_okay
                                  orelse (enc ~~ Encoding_Thumb2_tm orelse
                                  enc ~~ Encoding_ARM_tm) andalso wide_okay
                               then
                                 mk_Load (indx,mk_bool (0 <= offset),b,w,u,n,t,
                                   mode2)
                               else
                                 raise ERR "link_lines" ("load target " ^ v ^
                                    " unaligned or beyond permitted range on\
                                    \ line " ^ Int.toString i)
                             end)
                      end
                    else if is_Load_Halfword tm then
                      let val (indx,a,w,s,h,u,n,t,mode3) = dest_Load_Halfword tm
                          val v = vname mode3
                      in
                        ilink_instruction i (align_pc x enc) v
                          (fn offset =>
                             let val wide_okay =
                                       in_range (~4095,4095) offset
                                 val arm_okay =
                                       in_range (~255,255) offset
                                 val mode3 = mk_Mode3_immediate
                                              (mk_word12 (Int.abs offset))
                             in
                               if enc ~~ Encoding_Thumb2_tm andalso wide_okay
                                  orelse
                                  enc ~~ Encoding_ARM_tm andalso arm_okay
                               then
                                 mk_Load_Halfword (indx,mk_bool (0 <= offset),w,
                                   s,h,u,n,t,mode3)
                               else
                                 raise ERR "link_lines" ("load target " ^ v ^
                                    " beyond permitted range on line " ^
                                    Int.toString i)
                             end)
                      end
                    else if is_Load_Dual tm then
                      let val (indx,a,w,n,t,t2,mode3) = dest_Load_Dual tm
                          val v = vname mode3
                      in
                        ilink_instruction i (align_pc x enc) v
                          (fn offset =>
                             let val wide_okay =
                                       in_range (~1020,1020) offset
                                 val arm_okay =
                                       in_range (~255,255) offset
                                 val mode3 = mk_Mode3_immediate
                                              (mk_word12 (Int.abs offset))
                             in
                               if enc ~~ Encoding_Thumb2_tm andalso wide_okay
                                  orelse
                                  enc ~~ Encoding_ARM_tm andalso arm_okay
                               then
                                 mk_Load_Dual (indx,mk_bool (0 <= offset),w,
                                   n,t,t2,mode3)
                               else
                                 raise ERR "link_lines" ("load target " ^ v ^
                                    " beyond permitted range on line " ^
                                    Int.toString i)
                             end)
                      end
                    else raise ERR "recurse"
                          ("unexpected free variable on line " ^ Int.toString i)
              in
                recurse t ((x,Instruction (enc,cond,tm'))::code)
              end
        | recurse (_::t) code = recurse t code
    in
      recurse l1 []
    end
in
  fun link_code c = let
    val x as (code,lmap) =
          number_lines c (Arbnum.zero,[],Redblackmap.mkDict String.compare)
  in
    (link_lines x, lmap)
  end
end;

fun arm_parse_from_string s =
  s |> arm_parse (arm_parse_lines []) |> link_code;

fun arm_parse_from_quote s =
  s |> arm_parse_quote (arm_parse_lines []) |> link_code;

fun arm_parse_from_file s =
let val instream = TextIO.openIn s
    val input = TextIO.inputAll instream before TextIO.closeIn instream
in
  arm_parse_from_string input
end;

(* for testing *)
fun arm_lex_from_file s =
let val instream = TextIO.openIn s
    val input = TextIO.inputAll instream before TextIO.closeIn instream
in
  arm_lex input
end;

(* ------------------------------------------------------------------------- *)

end
