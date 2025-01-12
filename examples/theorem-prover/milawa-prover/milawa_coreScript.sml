open HolKernel boolLib bossLib Parse; val _ = new_theory "milawa_core";

open stringTheory finite_mapTheory pred_setTheory listTheory sumTheory;
open optionTheory arithmeticTheory relationTheory;

open lisp_sexpTheory lisp_parseTheory;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


val _ = max_print_depth := 10;

(* read all lines from file *)

fun text_from_file filename = let
  val t = TextIO.openIn(filename)
  fun all_lines () =
    case TextIO.inputLine(t) of NONE => []
                              | SOME x => x::all_lines ()
  val text = all_lines ()
  val _ = TextIO.closeIn(t)
  val output = foldr (fn (x,y) => x ^ y) "" text
  val _ = print ("\n" ^ filename ^ " contains " ^ int_to_string (length text) ^
                 " lines and " ^ int_to_string (size output) ^ " characters.\n\n")
  in output end;

val milawa_core_tm = stringSyntax.fromMLstring (text_from_file "core.lisp");

local
  val app_cons = APPEND |> SPEC_ALL |> CONJUNCT2
  val app_nil = APPEND |> SPEC_ALL |> CONJUNCT1
  fun append_conv tm =
    ((REWR_CONV app_cons THENC RAND_CONV append_conv)
     ORELSEC (REWR_CONV app_nil)) tm
    handle HOL_ERR _ => ALL_CONV tm
in
  val milawa_core_append_thm = append_conv ``^milawa_core_tm ++ rest``
  val milawa_core_tm = milawa_core_append_thm |> concl |> rand
end


(* move the following to lisp_parseTheory *)

val LENGTH_sexp_lex_parse = sexp_lex_parse_ind
  |> Q.ISPEC `\(cs,s,r,mem). LENGTH (SND (sexp_lex_parse (cs,s,r,mem))) <= LENGTH cs`
  |> SIMP_RULE std_ss [];

val LENGTH_SND_read_while = prove(
  ``!t x. LENGTH (SND (read_while P t x)) <= LENGTH t``,
  Induct \\ SIMP_TAC std_ss [read_while_def] \\ SRW_TAC [] []
  \\ Q.PAT_ASSUM `!x.bb` (MP_TAC o Q.SPEC `STRCAT x (STRING h "")`)
  \\ REPEAT STRIP_TAC \\ DECIDE_TAC);

val read_while_IMP_LENGTH_LESS_EQ = prove(
  ``(read_while P t x = (x1,x2)) ==> (LENGTH x2 <= LENGTH t)``,
  REPEAT STRIP_TAC
  \\ MP_TAC (SPEC_ALL LENGTH_SND_read_while) \\ FULL_SIMP_TAC std_ss []);

val PULL_FORALL_IMP = METIS_PROVE [] ``(Q ==> !x. P x) = !x. Q ==> P x``
val IMP_IMP = METIS_PROVE [] ``b1 /\ (b2 ==> b3) ==> ((b1 ==> b2) ==> b3)``

val str2sym_aux_LESS_EQ = prove(
  ``!xs b y ys. (str2sym_aux xs b = (y,ys)) ==> LENGTH ys <= LENGTH xs``,
  Induct \\ Cases_on `b` \\ SIMP_TAC std_ss [str2sym_aux_def,LET_DEF]
  \\ REPEAT STRIP_TAC
  \\ `?z zs. str2sym_aux xs F = (z,zs)` by METIS_TAC [pairTheory.PAIR]
  \\ `?z zs. str2sym_aux xs T = (z,zs)` by METIS_TAC [pairTheory.PAIR]
  \\ FULL_SIMP_TAC std_ss [LENGTH] \\ RES_TAC
  \\ TRY (Q.PAT_X_ASSUM `zs = ys` (ASSUME_TAC)) \\ FULL_SIMP_TAC std_ss []
  \\ TRY (Q.PAT_X_ASSUM `(if b1 then x1 else y1) = z1` MP_TAC)
  \\ SRW_TAC [] [] \\ DECIDE_TAC);

val str2sym_LENGTH = prove(
  ``!xs y ys. (str2sym (x::xs) = (y,ys)) ==> LENGTH ys <= LENGTH xs``,
  SIMP_TAC std_ss [str2sym_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ `?y1 y2. read_while identifier_char xs "" = (y1,y2)` by METIS_TAC [pairTheory.PAIR]
  \\ `?z1 z2. str2sym_aux xs F = (z1,z2)` by METIS_TAC [pairTheory.PAIR]
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC read_while_IMP_LENGTH_LESS_EQ
  \\ IMP_RES_TAC str2sym_aux_LESS_EQ
  \\ Cases_on `x = #"|"` \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT (POP_ASSUM MP_TAC)
  \\ FULL_SIMP_TAC std_ss []);

val next_token_LESS_EQ = prove(
  ``!cs cs2. (next_token cs = (t,cs2)) ==> LENGTH cs2 <= LENGTH cs``,
  STRIP_TAC \\ completeInduct_on `LENGTH cs` \\ NTAC 2 STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL_IMP]
  \\ Cases_on `cs` \\ SIMP_TAC std_ss [next_token_def,LET_DEF]
  \\ SRW_TAC [] [] THEN1
   (`STRLEN t' < STRLEN (STRING h t')` by (EVAL_TAC \\ DECIDE_TAC)
    \\ RES_TAC \\ DECIDE_TAC)
  THEN1
   (POP_ASSUM MP_TAC
    \\ `?z zs. read_while number_char t' "" = (z,zs)` by METIS_TAC [pairTheory.PAIR]
    \\ FULL_SIMP_TAC std_ss [] \\ SRW_TAC [] [LENGTH]
    \\ FULL_SIMP_TAC std_ss [LENGTH,TL]
    \\ Cases_on `zs` \\ FULL_SIMP_TAC std_ss [LENGTH,TL]
    \\ IMP_RES_TAC read_while_IMP_LENGTH_LESS_EQ
    \\ FULL_SIMP_TAC std_ss [LENGTH,TL] \\ DECIDE_TAC)
  THEN1
   (POP_ASSUM MP_TAC
    \\ `?z zs. read_while number_char t' "" = (z,zs)` by METIS_TAC [pairTheory.PAIR]
    \\ FULL_SIMP_TAC std_ss [] \\ SRW_TAC [] [LENGTH]
    \\ IMP_RES_TAC read_while_IMP_LENGTH_LESS_EQ \\ DECIDE_TAC)
  THEN1
   (`?z zs. read_while (\x. x <> #"\n") t' "" = (z,zs)` by METIS_TAC [pairTheory.PAIR]
    \\ FULL_SIMP_TAC std_ss []
    \\ `STRLEN zs < STRLEN (STRING #";" t')` by
     (IMP_RES_TAC read_while_IMP_LENGTH_LESS_EQ
      \\ FULL_SIMP_TAC std_ss [LENGTH] \\ DECIDE_TAC)
    \\ RES_TAC \\ FULL_SIMP_TAC std_ss [LENGTH] \\ DECIDE_TAC)
  THEN1
   (`?z1 z2. str2sym (STRING h t') = (z1,z2)` by METIS_TAC [pairTheory.PAIR]
    \\ IMP_RES_TAC str2sym_LENGTH \\ FULL_SIMP_TAC std_ss []
    \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC));

val LENGTH_SND_sexp_lex_parse = prove(
  ``!cs s r mem. LENGTH (SND (sexp_lex_parse (cs,s,r,mem))) <= LENGTH cs``,
  MATCH_MP_TAC LENGTH_sexp_lex_parse \\ REPEAT STRIP_TAC THEN1
   (ONCE_REWRITE_TAC [sexp_lex_parse_def] \\ SRW_TAC [] [] \\ SRW_TAC [] []
    \\ Q.PAT_X_ASSUM `next_token xx = yy` (MP_TAC)
    \\ TRY (Cases_on `t`) \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD]
    \\ IMP_RES_TAC next_token_LESS_EQ \\ IMP_RES_TAC LESS_EQ_TRANS)
  \\ Cases_on `s` \\ ONCE_REWRITE_TAC [sexp_lex_parse_def]
  \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF] \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC std_ss []);

val sexp_lex_parse_LESS_EQ = prove(
  ``!cs s r mem.
      (sexp_lex_parse (cs,s,r,mem) = (x1,x2)) ==>
      LENGTH x2 <= LENGTH cs``,
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL LENGTH_SND_sexp_lex_parse)
  \\ FULL_SIMP_TAC std_ss []);

val is_eof_F_IMP = prove(
  ``!str str1.
       ((F,str1) = is_eof str) ==>
       ?x xs. (str1 = x::xs) /\ ~(space_char x) /\ ~(x = #";") /\
              LENGTH xs < LENGTH str``,
  STRIP_TAC \\ completeInduct_on `LENGTH str` \\ STRIP_TAC
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [PULL_FORALL_IMP]
  \\ POP_ASSUM MP_TAC \\ Cases_on `str` THEN1 EVAL_TAC
  \\ SIMP_TAC std_ss [is_eof_def] \\ SRW_TAC [] [] THEN1
   (Q.PAT_X_ASSUM `!x.bbb` (MP_TAC o Q.SPECL [`t`,`str1`])
    \\ FULL_SIMP_TAC std_ss [] \\ MATCH_MP_TAC IMP_IMP
    \\ STRIP_TAC THEN1 (EVAL_TAC \\ DECIDE_TAC)
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`x`,`xs`]
    \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ Q.ABBREV_TAC `str2 = SND (read_while (\x. x <> #"\n") t "")`
  \\ Q.PAT_X_ASSUM `!x.bbb` (MP_TAC o Q.SPECL [`str2`,`str1`])
  \\ `LENGTH str2 <= LENGTH t` by
       (Q.UNABBREV_TAC `str2` \\ FULL_SIMP_TAC std_ss [LENGTH_SND_read_while])
  \\ FULL_SIMP_TAC std_ss [] \\ MATCH_MP_TAC IMP_IMP
  \\ STRIP_TAC THEN1 (EVAL_TAC \\ DECIDE_TAC)
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC);

val next_token_PROGRESS = prove(
  ``~space_char x /\ x <> #";" ==>
    LENGTH (SND (next_token (STRING x xs))) <= LENGTH xs``,
  SIMP_TAC std_ss [next_token_def] \\ REPEAT STRIP_TAC
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss []
  \\ TRY (Cases_on `cs`) \\ FULL_SIMP_TAC (srw_ss()) [LENGTH]
  \\ SRW_TAC [] [] \\ IMP_RES_TAC read_while_IMP_LENGTH_LESS_EQ
  \\ IMP_RES_TAC str2sym_LENGTH
  \\ FULL_SIMP_TAC std_ss [LENGTH] \\ DECIDE_TAC);

val sexp_parse_stream_PROGRESS = store_thm("sexp_parse_stream_PROGRESS",
  ``((F,str1) = is_eof str) /\ ((s,str2) = sexp_parse_stream str1) ==>
    LENGTH str2 < LENGTH str``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC is_eof_F_IMP
  \\ FULL_SIMP_TAC std_ss [sexp_parse_stream_def]
  \\ Q.PAT_X_ASSUM `(s,str2) = bb` (MP_TAC o GSYM)
  \\ SIMP_TAC std_ss [Once sexp_lex_parse_def]
  \\ `?y1 y2. next_token (STRING x xs) = (y1,y2)` by METIS_TAC [pairTheory.PAIR]
  \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ IMP_RES_TAC next_token_PROGRESS
  \\ POP_ASSUM (MP_TAC o Q.SPEC `xs`)
  \\ FULL_SIMP_TAC std_ss [] \\ SRW_TAC [] []
  \\ IMP_RES_TAC sexp_lex_parse_LESS_EQ \\ DECIDE_TAC);

val read_sexps_def = tDefine "read_sexps" `
  read_sexps str =
    let (yes,str) = is_eof str in
      if yes then [] else
        let (s,str) = sexp_parse_stream str in
          s::read_sexps str`
  (WF_REL_TAC `measure LENGTH` \\ METIS_TAC [sexp_parse_stream_PROGRESS])
  |> SPEC_ALL;

val evals = map EVAL
  [``next_token (STRING #")" cs)``,
   ``next_token (STRING #"'" cs)``,
   ``next_token (STRING #"." cs)``,
   ``next_token (STRING #"(" cs)``,
   ``next_token (STRING #" " cs)``,
   ``next_token (STRING #"0" cs)``,
   ``next_token (STRING #"1" cs)``,
   ``next_token (STRING #"2" cs)``,
   ``next_token (STRING #"3" cs)``,
   ``next_token (STRING #"4" cs)``,
   ``next_token (STRING #"5" cs)``,
   ``next_token (STRING #"6" cs)``,
   ``next_token (STRING #"7" cs)``,
   ``next_token (STRING #"8" cs)``,
   ``next_token (STRING #"9" cs)``,
   ``next_token (STRING #";" cs)``,
   ``next_token (STRING #"|" cs)``,
   ``str2sym (STRING #"|" cs)``] |> LIST_CONJ

val sexp_lex_parse_SIMP1 = prove(
  ``(sexp_lex_parse (#")"::cs,s,L_READ,mem) = sexp_lex_parse (cs,s,L_COLLECT (Sym "NIL"),mem)) /\
    (sexp_lex_parse (#"'"::cs,s,L_READ,mem) = sexp_lex_parse (cs,L_QUOTE::s,L_READ,mem)) /\
    (sexp_lex_parse (#"."::cs,s,L_READ,mem) = sexp_lex_parse (cs,L_DOT::s,L_READ,mem))``,
  REPEAT STRIP_TAC \\ SIMP_TAC (srw_ss()) [Once sexp_lex_parse_def,LET_DEF,evals]);

val sexp_lex_parse_SIMP2 = prove(
  ``(sexp_lex_parse (#" "::cs,s,L_READ,mem) = sexp_lex_parse (cs,s,L_READ,mem)) /\
    (sexp_lex_parse (#"\n"::cs,s,L_READ,mem) = sexp_lex_parse (cs,s,L_READ,mem)) /\
    (sexp_lex_parse (#"\t"::cs,s,L_READ,mem) = sexp_lex_parse (cs,s,L_READ,mem)) /\
    (sexp_lex_parse (#"("::cs,s,L_READ,mem) = sexp_lex_parse (cs,L_STOP::s,L_READ,mem))``,
  EVAL_TAC);

val DROP_WHILE_NOT_NL_def = Define `
  (DROP_WHILE_NOT_NL [] = []) /\
  (DROP_WHILE_NOT_NL (x::xs) = if x = #"\n" then #"\n"::xs else DROP_WHILE_NOT_NL xs)`

val DROP_WHILE_NOT_NL_INTRO = prove(
  ``!t s. SND (read_while (\x. x <> #"\n") t s) =
          DROP_WHILE_NOT_NL t``,
  Induct \\ ASM_SIMP_TAC std_ss [read_while_def,DROP_WHILE_NOT_NL_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `h = #"\n"` \\ ASM_SIMP_TAC std_ss []);

val sexp_lex_parse_COMMENT = prove(
  ``(sexp_lex_parse (#";"::cs,s,L_READ,mem) =
       sexp_lex_parse (DROP_WHILE_NOT_NL cs,s,L_READ,mem))``,
  REPEAT STRIP_TAC \\ SIMP_TAC (srw_ss()) [Once sexp_lex_parse_def,LET_DEF,evals,
     GSYM (Q.SPECL [`t`,`""`] DROP_WHILE_NOT_NL_INTRO),GSYM ORD_11]
  \\ EVAL_TAC);

val sexp_lex_parse_SIMP_NUM = prove(
  ``(sexp_lex_parse (#"0"::cs,s,L_READ,mem) =
       let (str,cs) = read_while number_char cs "" in
         sexp_lex_parse (cs,s,L_RETURN (Val (str2num str)),mem)) /\
    (sexp_lex_parse (#"1"::cs,s,L_READ,mem) =
       let (str,cs) = read_while number_char cs "" in
         sexp_lex_parse (cs,s,L_RETURN (Val (10 ** STRLEN str + str2num str)),mem)) /\
    (sexp_lex_parse (#"2"::cs,s,L_READ,mem) =
       let (str,cs) = read_while number_char cs "" in
         sexp_lex_parse (cs,s,L_RETURN (Val (2 * 10 ** STRLEN str + str2num str)),mem)) /\
    (sexp_lex_parse (#"3"::cs,s,L_READ,mem) =
       let (str,cs) = read_while number_char cs "" in
         sexp_lex_parse (cs,s,L_RETURN (Val (3 * 10 ** STRLEN str + str2num str)),mem)) /\
    (sexp_lex_parse (#"4"::cs,s,L_READ,mem) =
       let (str,cs) = read_while number_char cs "" in
         sexp_lex_parse (cs,s,L_RETURN (Val (4 * 10 ** STRLEN str + str2num str)),mem)) /\
    (sexp_lex_parse (#"5"::cs,s,L_READ,mem) =
       let (str,cs) = read_while number_char cs "" in
         sexp_lex_parse (cs,s,L_RETURN (Val (5 * 10 ** STRLEN str + str2num str)),mem)) /\
    (sexp_lex_parse (#"6"::cs,s,L_READ,mem) =
       let (str,cs) = read_while number_char cs "" in
         sexp_lex_parse (cs,s,L_RETURN (Val (6 * 10 ** STRLEN str + str2num str)),mem)) /\
    (sexp_lex_parse (#"7"::cs,s,L_READ,mem) =
       let (str,cs) = read_while number_char cs "" in
         sexp_lex_parse (cs,s,L_RETURN (Val (7 * 10 ** STRLEN str + str2num str)),mem)) /\
    (sexp_lex_parse (#"8"::cs,s,L_READ,mem) =
       let (str,cs) = read_while number_char cs "" in
         sexp_lex_parse (cs,s,L_RETURN (Val (8 * 10 ** STRLEN str + str2num str)),mem)) /\
    (sexp_lex_parse (#"9"::cs,s,L_READ,mem) =
       let (str,cs) = read_while number_char cs "" in
         sexp_lex_parse (cs,s,L_RETURN (Val (9 * 10 ** STRLEN str + str2num str)),mem))``,
  REPEAT STRIP_TAC
  \\ SIMP_TAC (srw_ss()) [Once sexp_lex_parse_def,LET_DEF,evals]
  \\ Cases_on `read_while number_char cs ""`
  \\ FULL_SIMP_TAC (srw_ss()) []);

val sexp_lex_parse_BAR = prove(
  ``(sexp_lex_parse (#"|"::cs,s,L_READ,mem) =
      let (str,cs) = str2sym (STRING #"|" cs) in
        sexp_lex_parse (cs,s,L_RETURN (Sym str),mem))``,
  REPEAT STRIP_TAC
  \\ SIMP_TAC (srw_ss()) [Once sexp_lex_parse_def,LET_DEF,evals]
  \\ Cases_on `str2sym_aux cs F`
  \\ FULL_SIMP_TAC (srw_ss()) []);

fun auto_prove (goal,tac) = let
  val (rest,validation) = tac ([], goal)
  in if length rest = 0 then validation []
     else failwith("auto_prove failed") end

val sexp_lex_parse_chars = let
  fun is_true tm = (tm ~~ T)
  fun is_identifier_char c =
    ``identifier_char ^c`` |> EVAL |> concl |> rand |> is_true
  fun all_ichars_below 0 xs = xs
    | all_ichars_below n xs = let
    val c = stringSyntax.fromMLchar (chr n)
    in all_ichars_below (n-1) (if is_identifier_char c then c::xs else xs) end
  val cs = all_ichars_below 255 []
  fun thm_for_char c = let
    val sym_evals = CONJ (EVAL ``next_token (STRING ^c cs)``)
                         (EVAL ``str2sym (STRING ^c cs)``)
    in auto_prove(
      ``(sexp_lex_parse (^c::cs,s,L_READ,mem) =
          let (str,cs) = str2sym (STRING ^c cs) in
            sexp_lex_parse (cs,s,L_RETURN (Sym str),mem))``,
      REPEAT STRIP_TAC
      \\ SIMP_TAC (srw_ss()) [Once sexp_lex_parse_def,LET_DEF,sym_evals]
      \\ Cases_on `read_while identifier_char cs ""`
      \\ FULL_SIMP_TAC (srw_ss()) []) end handle HOL_ERR _ => TRUTH
  in filter (not o is_true o concl) (map thm_for_char cs) end;

val sexp_lex_parse_SIMP_RETURN = prove(
  ``(sexp_lex_parse (cs,L_STOP::s,L_RETURN x,mem) =
     sexp_lex_parse (cs,L_CONS x::L_STOP::s,L_READ,mem)) /\
    (sexp_lex_parse (cs,L_CONS y::s,L_RETURN x,mem) =
     sexp_lex_parse (cs,L_CONS x::L_CONS y::s,L_READ,mem)) /\
    (sexp_lex_parse (cs,L_DOT::s,L_RETURN x,mem) =
     sexp_lex_parse (cs,L_CONS x::L_DOT::s,L_READ,mem)) /\
    (sexp_lex_parse (cs,L_QUOTE::s,L_RETURN x,mem) =
     sexp_lex_parse (cs,s,L_RETURN (Dot (Sym "QUOTE") (Dot x (Sym "NIL"))),mem)) /\
    (sexp_lex_parse (cs,L_STORE n::s,L_RETURN x,mem) =
     sexp_lex_parse (cs,s,L_RETURN x,(n =+ x) mem)) /\
    (sexp_lex_parse (cs,[],L_RETURN x,mem) = (x,cs))``,
  REPEAT STRIP_TAC \\ SIMP_TAC (srw_ss()) [Once sexp_lex_parse_def]
  \\ SIMP_TAC (srw_ss()) [LET_DEF,READ_L_STORE_def] \\ EVAL_TAC);

val sexp_lex_parse_SIMP_COLLECT = prove(
  ``(sexp_lex_parse (cs,L_STOP::s,L_COLLECT x,mem) =
     sexp_lex_parse (cs,s,L_RETURN x,mem)) /\
    (sexp_lex_parse (cs,L_CONS y::s,L_COLLECT x,mem) =
     sexp_lex_parse (cs,s,L_COLLECT (Dot y x),mem)) /\
    (sexp_lex_parse (cs,L_DOT::s,L_COLLECT x,mem) =
     sexp_lex_parse (cs,s,L_COLLECT (CAR x),mem)) /\
    (sexp_lex_parse (cs,[],L_COLLECT x,mem) = (Sym "NIL",cs))``,
  REPEAT STRIP_TAC \\ SIMP_TAC (srw_ss()) [Once sexp_lex_parse_def,LET_DEF,
    READ_L_CONS_def] \\ EVAL_TAC);

val sexp_lex_parse_SIMP = LIST_CONJ
  (sexp_lex_parse_BAR ::
   sexp_lex_parse_COMMENT ::
   sexp_lex_parse_chars @
   CONJUNCTS sexp_lex_parse_SIMP_NUM @
   CONJUNCTS sexp_lex_parse_SIMP1 @
   CONJUNCTS sexp_lex_parse_SIMP2 @
   CONJUNCTS sexp_lex_parse_SIMP_RETURN @
   CONJUNCTS sexp_lex_parse_SIMP_COLLECT);

local
  fun eval_term_ss tm_name tm = simpLib.conv_ss
    { name = tm_name, trace = 3, key = SOME ([],tm), conv = K (K EVAL) };
  val pattern = ``sexp_lex_parse (str,s,task,mem)``
  val str_tm = ``str:string``
  val rws = CONJ (EVAL ``str2sym ""``) (EVAL ``str2num ""``)
  val my_ss = std_ss ++ eval_term_ss "str2sym" ``str2sym (STRING c cs)``
                     ++ eval_term_ss "str2num" ``str2num (STRING c cs)``
                     ++ eval_term_ss "read_while_comment" ``DROP_WHILE_NOT_NL (x::xs)``
                     ++ eval_term_ss "read_while_number" ``read_while number_char (STRING c cs) ""``
  fun dest_string tm = let
    val (x,y) = listSyntax.dest_cons tm
    in x :: dest_string y end handle HOL_ERR _ => [tm]
  fun take_until p [] = []
    | take_until p (x::xs) = if p x then [] else x :: take_until p xs
in
  fun sexp_lex_parse_conv tm = let
    val _ = print "sexp_lex_parse_conv: "
    val s = fst (match_term pattern tm)
    val input_tm = subst s str_tm
    val input = dest_string input_tm
    val input_length = length input - 1
    val fst_line = input
          |> take_until (fn c => c ~~ ``#"\n"`` orelse type_of c = ``:string``)
          |> map stringSyntax.fromHOLchar |> implode
    val _ = print (fst_line ^ " ... \n")
    val sp_chr_tm = ``#" "``
    fun split_after n k [] acc = [implode (rev acc)]
      | split_after n k [x] acc = [implode (rev acc)]
      | split_after n k (x::xs) acc =
          if n < k orelse x !~ sp_chr_tm
          then split_after (n+1) k xs ((stringSyntax.fromHOLchar x)::acc)
          else implode (rev ((stringSyntax.fromHOLchar x)::acc))
               :: split_after 0 k xs []
    val segments = split_after 0 80 input []
    val th = REFL (subst [input_tm|->str_tm] tm)
    fun find_fringe_terms p tm =
      if p tm then [tm] else
      if is_abs tm then find_fringe_terms p (snd (dest_abs tm)) else
      if is_comb tm then find_fringe_terms p (rator tm) @ find_fringe_terms p (rand tm) else
        []
    val c = SIMP_CONV my_ss [sexp_lex_parse_SIMP,LET_DEF,APPEND,LENGTH,rws]
    fun c2 tm = let
      val xs = find_fringe_terms (fn tm => type_of tm = ``:SExp``) tm
      val ys = map (fn x => (x,genvar(type_of x))) xs
      val tm2 = subst (map (fn (x,y) => x |-> y) ys) tm
      val tm3 = c tm2
      in INST (map (fn (x,y) => y |-> x) ys) tm3 end
    fun mk_string [] = str_tm
      | mk_string (x::xs) = listSyntax.mk_cons(stringSyntax.fromMLchar x, mk_string xs)
    fun process_segments [] th = th
      | process_segments (s::ss) th = let
          val _ = print (int_to_string (length ss) ^ " ")
          val th = CONV_RULE (RAND_CONV c2) (INST [str_tm|->mk_string (explode s)] th)
          in if pairSyntax.is_pair (rand (concl th)) then let
               val l = input_length - foldl (fn (x,y) => size x + y) 0 ss
               fun ntimes 0 f x = x | ntimes n f x = ntimes (n-1) f (f x)
               in INST [str_tm|->ntimes l rand input_tm] th end
             else process_segments ss th end
    val th = INST [str_tm|->last input] (process_segments segments th)
    val _ = print "\n"
    in th end;
end

val is_eof_aux_def = Define `
  (is_eof_aux "" = is_eof "") /\
  (is_eof_aux (x::xs) = if x = #"\n" then is_eof xs else is_eof_aux xs)`

val is_eof_comment = prove(
  ``!xs. is_eof (#";"::xs) = is_eof_aux xs``,
  SIMP_TAC std_ss [is_eof_def,LET_DEF,EVAL ``space_char #";"``]
  \\ Q.SPEC_TAC (`""`,`ys`) \\ Induct_on `xs`
  \\ FULL_SIMP_TAC std_ss [read_while_def,is_eof_aux_def]
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss [is_eof_def,EVAL ``space_char #"\n"``]);

val is_eof_lemmas = let
  fun all_below f 0 = []
    | all_below f n = f (n-1) :: all_below f (n-1)
  val is_eof_aux_nil = EVAL ``is_eof_aux ""``
  fun is_eof_aux n =
    EVAL (``is_eof_aux (CHR n::cs)`` |> subst [``n:num``|->numSyntax.term_of_int n])
  val is_eof_aux_lemmas = (is_eof_aux_nil :: all_below is_eof_aux 256)
  val is_eof_nil = EVAL ``is_eof ""``
  fun is_eof n =
    if n = ord #";" then SPEC_ALL is_eof_comment else
      EVAL (``is_eof (CHR n::cs)`` |> subst [``n:num``|->numSyntax.term_of_int n])
  val is_eof_lemmas = is_eof_nil :: all_below is_eof 256
  in is_eof_aux_lemmas @ is_eof_lemmas end;

fun TRY_EACHC [] = NO_CONV
  | TRY_EACHC (c::cs) = c ORELSEC TRY_EACHC cs

val is_eof_conv = REPEATC (TRY_EACHC (map REWR_CONV is_eof_lemmas))

local
  val pattern = ``read_sexps str``
  val str_tm = ``str:string``
  val lemma = SIMP_RULE std_ss [LET_DEF,sexp_parse_stream_def] read_sexps_def
in
  fun read_sexps_conv tm = let
    val s = fst (match_term pattern tm)
    val th = INST s lemma |> CONV_RULE ((RAND_CONV o RAND_CONV) is_eof_conv)
    val pair = (th |> concl |> rand |> rand |> pairSyntax.is_pair) handle HOL_ERR _ => false
    in if not pair then CONV_RULE (RAND_CONV (REWR_CONV (GSYM lemma))) th else let
    val th = CONV_RULE (RAND_CONV PairRules.PBETA_CONV THENC RAND_CONV COND_CONV) th
    val t = th |> concl |> rand
    in if not (can (find_term (aconv ``read_sexps``)) t) then th else let
    val th = CONV_RULE (RAND_CONV (RAND_CONV sexp_lex_parse_conv
                                   THENC PairRules.PBETA_CONV)) th
    in CONV_RULE ((RAND_CONV o RAND_CONV) read_sexps_conv) th end end end
end

val read_sexps_milawa_core_thm =
  time (REWRITE_RULE [CAR_def] o read_sexps_conv) ``read_sexps ^milawa_core_tm``;

val input_tm = milawa_core_append_thm |> concl |> rator |> rand
val output_tm = read_sexps_milawa_core_thm |> concl |> rand

val MILAWA_CORE_TEXT_def = Define `MILAWA_CORE_TEXT = ^(input_tm |> rator |> rand)`;
val MILAWA_CORE_SEXP_def = Define `MILAWA_CORE_SEXP rest = ^output_tm`;

val lemma = milawa_core_append_thm
  |> CONV_RULE ((RATOR_CONV o RAND_CONV o RATOR_CONV o RAND_CONV)
       (REWR_CONV (GSYM MILAWA_CORE_TEXT_def)))

val MILAWA_CORE_TEXT_THM = save_thm("MILAWA_CORE_TEXT_THM",
  read_sexps_milawa_core_thm
  |> CONV_RULE (RAND_CONV (REWR_CONV (GSYM MILAWA_CORE_SEXP_def)))
  |> CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV) (REWR_CONV (GSYM lemma))));

val _ = max_print_depth := 0;
val _ = export_theory();
