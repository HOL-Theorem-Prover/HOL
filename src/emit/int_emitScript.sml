open HolKernel boolLib bossLib Parse;
open EmitML arithmeticTheory integerTheory integer_wordTheory;
open words_emitTheory;

val _ = new_theory "int_emit";

val neg_int_of_num_def = Define `neg_int_of_num n = ~ int_of_num (n + 1)`;
val i2w_itself_def = Define `i2w_itself(i,(:'a)) = i2w i : 'a word`;

val i2w_itself = REWRITE_RULE [i2w_def] i2w_itself_def;

val emit_rule = SIMP_RULE std_ss [numeralTheory.iZ, NUMERAL_DEF];

fun emit_conv l1 l2 = LIST_CONJ
 (map (GEN_ALL o (SIMP_CONV (srw_ss()) (neg_int_of_num_def::l1)
    THENC REWRITE_CONV [GSYM neg_int_of_num_def])) l2);

val lem1 = DECIDE ``~(n + 1n <= m) ==> (n + 1 - m = (n - m) + 1)``;
val lem2 = DECIDE ``m + 1n + (n + 1) = m + n + 1 + 1``;

val INT_NEG_EMIT = Q.prove(
  `(!n. ~ (int_of_num n) =
         if n = 0 then int_of_num 0 else neg_int_of_num (n - 1)) /\
   (!n. ~ (neg_int_of_num n) = int_of_num (n + 1))`,
  SRW_TAC [ARITH_ss] [neg_int_of_num_def]);

val INT_ADD_EMIT = emit_conv [emit_rule INT_ADD_REDUCE, lem1, lem2]
   [``int_of_num m + int_of_num n``,
    ``neg_int_of_num m + int_of_num n``,
    ``int_of_num m + neg_int_of_num n``,
    ``neg_int_of_num m + neg_int_of_num n``];

val INT_SUB_EMIT = emit_conv [emit_rule INT_SUB_REDUCE]
   [``int_of_num m - int_of_num n``,
    ``neg_int_of_num m - int_of_num n``,
    ``int_of_num m - neg_int_of_num n``,
    ``neg_int_of_num m - neg_int_of_num n``];

val INT_MUL_EMIT = emit_conv [emit_rule INT_MUL_REDUCE]
   [``int_of_num m * int_of_num n``,
    ``neg_int_of_num m * int_of_num n``,
    ``int_of_num m * neg_int_of_num n``,
    ``neg_int_of_num m * neg_int_of_num n``];

val INT_LT_EMIT = emit_conv [emit_rule INT_LT_CALCULATE]
   [``int_of_num m < int_of_num n``,
    ``neg_int_of_num m < int_of_num n``,
    ``int_of_num m < neg_int_of_num n``,
    ``neg_int_of_num m < neg_int_of_num n``];

val INT_NEG_EXP = Q.prove(
  `!m n.
      neg_int_of_num m ** n =
        if EVEN n then
          int_of_num ((m + 1) ** n)
        else
          ~int_of_num ((m + 1) ** n)`,
  SRW_TAC [] [neg_int_of_num_def, INT_EXP_NEG]
    THEN FULL_SIMP_TAC std_ss [INT_EXP_NEG, GSYM ODD_EVEN]);

val INT_EXP_EMIT = CONJ INT_EXP INT_NEG_EXP;

val INT_Num_EMIT = Q.prove(
  `(!n. Num (int_of_num n) = n) /\
   (!n. Num (neg_int_of_num n) =
     FAIL $Num ^(mk_var("negative",bool)) (neg_int_of_num n))`,
  SRW_TAC [] [combinTheory.FAIL_THM]);

val INT_DIV_EMIT = Q.prove(
  `!i j. i / j =
      if j = 0 then FAIL $/ ^(mk_var("zero denominator",bool)) i j
      else
        ^((rhs o snd o dest_imp o snd o strip_forall o concl) int_div)`,
  SRW_TAC [] [combinTheory.FAIL_THM, int_div]);

val INT_MOD_EMIT = Q.prove(
  `!i j. i % j =
      if j = 0 then FAIL $% ^(mk_var("zero denominator",bool)) i j
      else
        ^((rhs o snd o dest_imp o snd o strip_forall o concl) int_mod)`,
  SRW_TAC [] [combinTheory.FAIL_THM, int_mod]);

val INT_QUOTE_EMIT = Q.prove(
  `!i j. i quot j =
      if j = 0 then FAIL $quot ^(mk_var("zero denominator",bool)) i j
      else
        ^((rhs o snd o dest_imp o snd o strip_forall o concl) int_quot)`,
  SRW_TAC [] [combinTheory.FAIL_THM, int_quot]);

val INT_REM_EMIT = Q.prove(
  `!i j. i rem j =
      if j = 0 then FAIL $rem ^(mk_var("zero denominator",bool)) i j
      else
        ^((rhs o snd o dest_imp o snd o strip_forall o concl) int_rem)`,
  SRW_TAC [] [combinTheory.FAIL_THM, int_rem]);

val _ = EmitML.is_int_literal_hook := intSyntax.is_int_literal;
val _ = EmitML.int_of_term_hook := intSyntax.int_of_term;

val _ = temp_clear_overloads_on "&";
val _ = temp_overload_on("int_of_num", ``integer$int_of_num``);

val _ = eSML "int"
 (OPEN ["num", "words"]
  :: EQDATATYPE ([], `int = int_of_num of num | neg_int_of_num of num`)
  :: MLSIG "type num = numML.num"
  :: MLSIG "type 'a itself = 'a fcpML.itself"
  :: MLSIG "type 'a word = 'a wordsML.word"
  :: MLSIG "val int_of_num : num -> int"
  :: MLSIG "val fromInt : Int.int -> int"
  :: MLSIG "val toInt : int -> Int.int option"
  :: MLSIG "val fromString : string -> int"
  :: MLSTRUCT
        "fun fromString s =\n\
      \    let val s = String.extract(s,0,SOME (Int.-(String.size s,1))) in\n\
      \      if String.sub(s,0) = #\"-\" then\n\
      \        let val s = String.extract(s,1,NONE) in\n\
      \          neg_int_of_num (numML.PRE (numML.fromString s))\n\
      \        end\n\
      \      else\n\
      \        int_of_num (numML.fromString s)\n\
      \    end\n"
  :: MLSTRUCT
        "fun fromInt i =\n\
      \    fromString (String.map (fn c => if c = #\"~\" then #\"-\" else c)\n\
      \      (String.^(Int.toString i,\"i\")))\n"
  :: MLSTRUCT
        "fun toInt (int_of_num n) = numML.toInt n\n\
      \    | toInt (neg_int_of_num n) =\n\
      \         case numML.toInt n of\n\
      \           SOME v => SOME (Int.-(Int.~ v,1))\n\
      \         | NONE => NONE\n"
  :: map DEFN
      [INT_NEG_EMIT, INT_Num_EMIT,
       INT_LT_EMIT, INT_LE_CALCULATE, INT_GT_CALCULATE, INT_GE_CALCULATE,
       INT_ABS, INT_ADD_EMIT, INT_SUB_EMIT, INT_MUL_EMIT, INT_EXP_EMIT,
       INT_DIV_EMIT, INT_MOD_EMIT, INT_QUOTE_EMIT, INT_REM_EMIT,
       INT_MAX_def, INT_MIN_def, UINT_MAX_def, i2w_itself, w2i_def])


(*---------------------------------------------------------------------------*)
(* Remind ML code generator about integer literals and how to take them apart*)
(*---------------------------------------------------------------------------*)

val _ = adjoin_to_theory {sig_ps = NONE,
   struct_ps = SOME (fn ppstrm =>
     let val S = PP.add_string ppstrm
         fun NL() = PP.add_newline ppstrm
     in S "val _ = EmitML.is_int_literal_hook := intSyntax.is_int_literal;"; NL();
        S "val _ = EmitML.int_of_term_hook := intSyntax.int_of_term;";
        NL(); NL()
     end)}


val _ = export_theory ();
