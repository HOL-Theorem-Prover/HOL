
open HolKernel boolLib bossLib Parse; val _ = new_theory "lisp_compiler_op";
val _ = ParseExtras.temp_loose_equality()

open compilerLib decompilerLib codegenLib;

open lisp_sexpTheory lisp_invTheory lisp_opsTheory lisp_bigopsTheory;
open lisp_codegenTheory lisp_initTheory lisp_symbolsTheory
open lisp_sexpTheory lisp_invTheory lisp_parseTheory;
open lisp_semanticsTheory lisp_alt_semanticsTheory lisp_compilerTheory progTheory;

open wordsTheory arithmeticTheory wordsLib listTheory pred_setTheory pairTheory;
open combinTheory finite_mapTheory addressTheory helperLib sumTheory;
open set_sepTheory bitTheory fcpTheory stringTheory optionTheory relationTheory;

val _ = let
  val thms = DB.match [] ``SPEC X64_MODEL``
  val thms = filter (can (find_term (can (match_term ``zLISP``))) o car o concl)
                    (map (#1 o #2) thms)
  val thms = map (Q.INST [`ddd`|->`SOME F`,`cu`|->`NONE`]) thms
  val _ = map (fn th => add_compiled [th] handle e => ()) thms
  in () end;

(* ---

  max_print_depth := 40;

*)

open lisp_compilerTheory lisp_semanticsTheory;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


val _ = set_echo 5;

val PULL_EXISTS_IMP = METIS_PROVE [] ``((?x. P x) ==> Q) = (!x. P x ==> Q)``;
val PULL_FORALL_IMP = METIS_PROVE [] ``(Q ==> !x. P x) = (!x. Q ==> P x)``;


(* sexp2sexp *)

val (_,mc_list_sfix1_def,mc_list_sfix1_pre_def) = compile "x64" ``
  mc_list_sfix1 (x1,x2,xs) =
    if ~isDot x2 then (x1,x2,xs) else
      let x1 = CAR x2 in
      let x2 = CDR x2 in
      let x1 = SFIX x1 in
      let xs = x1 :: xs in
        mc_list_sfix1 (x1,x2,xs)``;

val (_,mc_list_sfix2_def,mc_list_sfix2_pre_def) = compile "x64" ``
  mc_list_sfix2 (x1,x2,xs) =
    let x1 = HD xs in
    let xs = TL xs in
      if isVal x1 then (x1,x2,xs) else
        let x1 = Dot x1 x2 in
        let x2 = x1 in
          mc_list_sfix2 (x1,x2,xs)``

val (_,mc_list_sfix_def,mc_list_sfix_pre_def) = compile "x64" ``
  mc_list_sfix (x1,x2,xs) =
    let xs = x1::xs in
    let x1 = Val 0 in
    let xs = x1::xs in
    let (x1,x2,xs) = mc_list_sfix1 (x1,x2,xs) in
    let x2 = Sym "NIL" in
    let (x1,x2,xs) = mc_list_sfix2 (x1,x2,xs) in
    let x1 = HD xs in
    let xs = TL xs in
      (x1,x2,xs)``;

val SFIX_sfix = prove(
  ``SFIX = sfix``,
  SIMP_TAC std_ss [FUN_EQ_THM] \\ Cases \\ EVAL_TAC);

val mc_list_sfix1_thm = prove(
  ``!x2 x1 xs.
      ?y1 y2. mc_list_sfix1_pre (x1,x2,xs) /\
              (mc_list_sfix1 (x1,x2,xs) =
               (y1,y2,REVERSE (MAP sfix (sexp2list x2)) ++ xs))``,
  REVERSE Induct \\ ONCE_REWRITE_TAC [mc_list_sfix1_def,mc_list_sfix1_pre_def]
  \\ FULL_SIMP_TAC std_ss [LET_DEF,isDot_def,sexp2list_def,MAP,APPEND,CAR_def,CDR_def,REVERSE_DEF]
  \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [`SFIX x2`,`SFIX x2::xs`])
  \\ ASM_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,SFIX_sfix]);

val isVal_SFIX = prove(``!x. ~isVal (SFIX x)``, Cases \\ EVAL_TAC);

val mc_list_sfix2_thm = prove(
  ``!ys zs x1 xs.
       mc_list_sfix2_pre (x1,list2sexp zs,MAP SFIX ys ++ Val 0 :: xs) /\
       (mc_list_sfix2 (x1,list2sexp zs,MAP SFIX ys ++ Val 0 :: xs) =
          (Val 0, list2sexp (REVERSE (MAP SFIX ys) ++ zs), xs))``,
  Induct \\ ONCE_REWRITE_TAC [mc_list_sfix2_def,mc_list_sfix2_pre_def]
  \\ SIMP_TAC (srw_ss()) [APPEND,REVERSE_DEF,HD,TL,LET_DEF,isVal_def,isVal_SFIX]
  \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [GSYM list2sexp_def]
  \\ SIMP_TAC std_ss [APPEND,GSYM APPEND_ASSOC]);

val mc_list_sfix_thm = prove(
  ``mc_list_sfix_pre (x1,x2,xs) /\
    (mc_list_sfix (x1,x2,xs) = (x1,list2sexp (MAP sfix (sexp2list x2)),xs))``,
  SIMP_TAC std_ss [mc_list_sfix_def,mc_list_sfix_pre_def,LET_DEF]
  \\ STRIP_ASSUME_TAC (Q.SPECL [`x2`,`Val 0`,`Val 0::x1::xs`] mc_list_sfix1_thm)
  \\ FULL_SIMP_TAC std_ss [GSYM rich_listTheory.MAP_REVERSE]
  \\ ASM_SIMP_TAC std_ss [mc_list_sfix2_thm,GSYM SFIX_sfix,GSYM list2sexp_def]
  \\ FULL_SIMP_TAC std_ss [GSYM rich_listTheory.MAP_REVERSE,TL,HD,REVERSE_REVERSE]
  \\ FULL_SIMP_TAC (srw_ss()) [APPEND_NIL]);

(* push list of args to sexp2sexp *)

val (_,mc_push_list_def,mc_push_list_pre_def) = compile "x64" ``
  mc_push_list (x0,x2,xs) =
    if ~isDot x2 then
      let x0 = Sym "NIL" in
      let x2 = Sym "NIL" in
        (x0,x2,xs)
    else
      let x0 = CAR x2 in
      let x2 = CDR x2 in
      let xs = x0 :: xs in
      let x0 = Sym "EQUAL" in
      let xs = x0 :: xs in
        mc_push_list (x0,x2,xs)``

val push_list_fun_def = Define `
  (push_list_fun [] = []) /\
  (push_list_fun (x::xs) = Sym "EQUAL" :: x :: push_list_fun xs)`;

val push_list_fun_SNOC = prove(
  ``!xs x. push_list_fun (xs ++ [x]) = push_list_fun xs ++ [Sym "EQUAL"; x]``,
  Induct \\ ASM_SIMP_TAC std_ss [push_list_fun_def,APPEND]);

val mc_push_list_thm = prove(
  ``!x2 x0 xs.
      mc_push_list_pre (x0,x2,xs) /\
      (mc_push_list (x0,x2,xs) =
        (Sym "NIL",Sym "NIL",push_list_fun (REVERSE (sexp2list x2)) ++ xs))``,
  REVERSE Induct \\ ONCE_REWRITE_TAC [mc_push_list_pre_def,mc_push_list_def]
  THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
  THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
  \\ ASM_SIMP_TAC std_ss [isDot_def,LET_DEF,sexp2list_def,REVERSE_DEF,CDR_def,CAR_def]
  \\ ASM_SIMP_TAC std_ss [push_list_fun_SNOC,GSYM APPEND_ASSOC,APPEND]);

val (_,mc_sexp2sexp_aux_def,mc_sexp2sexp_aux_pre_def) = compile "x64" ``
  mc_sexp2sexp_aux (x0,x1,x2,xs:SExp list) =
    if x0 = Sym "NIL" then (* eval *)
      if x2 = Sym "NIL" then
        let x1 = Sym "NIL" in
        let x0 = Sym "QUOTE" in
        let x2 = Dot x2 x1 in
        let x0 = Dot x0 x2 in
        let x2 = x0 in
        let x0 = Sym "T" in
          (x0,x1,x2,xs)
      else if x2 = Sym "T" then
        let x1 = Sym "NIL" in
        let x0 = Sym "QUOTE" in
        let x2 = Dot x2 x1 in
        let x0 = Dot x0 x2 in
        let x2 = x0 in
        let x0 = Sym "T" in
          (x0,x1,x2,xs)
      else if isVal x2 then
        let x1 = Sym "NIL" in
        let x0 = Sym "QUOTE" in
        let x2 = Dot x2 x1 in
        let x0 = Dot x0 x2 in
        let x2 = x0 in
        let x0 = Sym "T" in
          (x0,x1,x2,xs)
      else if isSym x2 then
        let x1 = Sym "NIL" in
        let x0 = Sym "T" in
          (x0,x1,x2,xs)
      else let x0 = SAFE_CAR x2 in
      if x0 = Sym "QUOTE" then
        let x2 = SAFE_CDR x2 in
        let x2 = SAFE_CAR x2 in
        let x1 = Sym "NIL" in
        let x0 = Sym "QUOTE" in
        let x2 = Dot x2 x1 in
        let x0 = Dot x0 x2 in
        let x2 = x0 in
        let x0 = Sym "T" in
          (x0,x1,x2,xs)
      else if x0 = Sym "IF" then
        let xs = x0 :: xs in
        let x0 = Sym "CONSP" in
        let xs = x0 :: xs in
        let x2 = SAFE_CDR x2 in
        let x0 = SAFE_CAR x2 in
        let xs = x0 :: xs in
        let x0 = Sym "EQUAL" in
        let xs = x0 :: xs in
        let x2 = SAFE_CDR x2 in
        let x0 = SAFE_CAR x2 in
        let xs = x0 :: xs in
        let x0 = Sym "EQUAL" in
        let xs = x0 :: xs in
        let x2 = SAFE_CDR x2 in
        let x0 = SAFE_CAR x2 in
        let xs = x0 :: xs in
        let x0 = Sym "EQUAL" in
        let xs = x0 :: xs in
        let x2 = Sym "NIL" in
        let x0 = Sym "LIST" in
          (x0,x1,x2,xs)
      else if x0 = Sym "FIRST" then
        let xs = x0 :: xs in
        let x0 = Sym "CONS" in
        let xs = x0 :: xs in
        let x2 = SAFE_CDR x2 in
        let x2 = SAFE_CAR x2 in
        let x0 = Sym "NIL" in
          (x0,x1,x2,xs)
      else if x0 = Sym "SECOND" then
        let xs = x0 :: xs in
        let x0 = Sym "CONS" in
        let xs = x0 :: xs in
        let x2 = SAFE_CDR x2 in
        let x2 = SAFE_CAR x2 in
        let x0 = Sym "NIL" in
          (x0,x1,x2,xs)
      else if x0 = Sym "THIRD" then
        let xs = x0 :: xs in
        let x0 = Sym "CONS" in
        let xs = x0 :: xs in
        let x2 = SAFE_CDR x2 in
        let x2 = SAFE_CAR x2 in
        let x0 = Sym "NIL" in
          (x0,x1,x2,xs)
      else if x0 = Sym "FOURTH" then
        let xs = x0 :: xs in
        let x0 = Sym "CONS" in
        let xs = x0 :: xs in
        let x2 = SAFE_CDR x2 in
        let x2 = SAFE_CAR x2 in
        let x0 = Sym "NIL" in
          (x0,x1,x2,xs)
      else if x0 = Sym "FIFTH" then
        let xs = x0 :: xs in
        let x0 = Sym "CONS" in
        let xs = x0 :: xs in
        let x2 = SAFE_CDR x2 in
        let x2 = SAFE_CAR x2 in
        let x0 = Sym "NIL" in
          (x0,x1,x2,xs)
      else let x0 = SAFE_CAR x0 in if x0 = Sym "LAMBDA" then
        let x1 = SAFE_CDR x2 in
        let xs = x1 :: xs in
        let x2 = SAFE_CAR x2 in
        let x2 = SAFE_CDR x2 in
        let x1 = SAFE_CDR x2 in
        let x2 = SAFE_CAR x2 in
        let (x1,x2,xs) = mc_list_sfix (x1,x2,xs) in
        let xs = x2 :: xs in
        let x2 = SAFE_CAR x1 in
        let xs = x0 :: xs in
        let x0 = Sym "NIL" in
          (x0,x1,x2,xs)
      else let x0 = SAFE_CAR x2 in if x0 = Sym "COND" then
        let xs = x0 :: xs in
        let xs = x0 :: xs in
        let x2 = SAFE_CDR x2 in
        let (x0,x2,xs) = mc_push_list (x0,x2,xs) in
        let x2 = Sym "NIL" in
        let x0 = Sym "COND" in
          (x0,x1,x2,xs)
      else let x0 = SAFE_CAR x2 in if x0 = Sym "LET" then
        let xs = x2 :: xs in
        let x0 = Val 1 in
        let xs = x0 :: xs in
        let x2 = SAFE_CDR x2 in
        let x2 = SAFE_CAR x2 in
        let (x0,x2,xs) = mc_push_list (x0,x2,xs) in
        let x2 = Sym "NIL" in
        let x0 = Sym "LET" in
          (x0,x1,x2,xs)
      else let x0 = SAFE_CAR x2 in if x0 = Sym "LET*" then
        let xs = x2 :: xs in
        let x0 = Val 1 in
        let xs = x0 :: xs in
        let x2 = SAFE_CDR x2 in
        let x2 = SAFE_CAR x2 in
        let (x0,x2,xs) = mc_push_list (x0,x2,xs) in
        let x2 = Sym "NIL" in
        let x0 = Sym "LET" in
          (x0,x1,x2,xs)
      else if x0 = Sym "DEFUN" then
        let x1 = x2 in
        let x1 = SAFE_CDR x1 in
        let x2 = SAFE_CAR x1 in
        let x2 = SFIX x2 in
        let xs = x2 :: xs in
        let x1 = SAFE_CDR x1 in
        let x2 = SAFE_CAR x1 in
        let (x1,x2,xs) = mc_list_sfix (x1,x2,xs) in
        let xs = x2 :: xs in
        let x1 = SAFE_CDR x1 in
        let x2 = SAFE_CAR x1 in
        let x1 = Sym "NIL" in
        let x2 = Dot x2 x1 in
        let x1 = x2 in
        let x2 = HD xs in
        let xs = TL xs in
        let x2 = Dot x2 x1 in
        let x1 = x2 in
        let x2 = HD xs in
        let xs = TL xs in
        let x2 = Dot x2 x1 in
        let x0 = Dot x0 x2 in
        let x2 = x0 in
        let x0 = Sym "T" in
        let x1 = Sym "NIL" in
          (x0,x1,x2,xs)
      else
        let x2 = SAFE_CDR x2 in
        let x0 = SFIX x0 in
        let xs = x0 :: xs in
        let x0 = Sym "CONSP" in
        let xs = x0 :: xs in
        let (x0,x2,xs) = mc_push_list (x0,x2,xs) in
        let x2 = Sym "NIL" in
        let x0 = Sym "LIST" in
          (x0,x1,x2,xs)
  else if x0 = Sym "LIST" then
    let x0 = HD xs in
    let xs = TL xs in
    let x1 = HD xs in
    let xs = TL xs in
      if x0 = Sym "EQUAL" then
        let xs = x2 :: xs in
        let x2 = x1 in
        let x0 = Sym "LIST" in
        let xs = x0 :: xs in
        let x0 = Sym "NIL" in
          (x0,x1,x2,xs)
      else
        let x1 = Dot x1 x2 in
        let x2 = x1 in
        let x0 = Sym "T" in
        let x1 = Sym "NIL" in
          (x0,x1,x2,xs)
  else if x0 = Sym "LET" then
    let x0 = HD xs in
    let xs = TL xs in
    let x1 = HD xs in
    let xs = TL xs in
      if x0 = Sym "EQUAL" then
        let xs = x2 :: xs in
        let x2 = SAFE_CDR x1 in
        let x2 = SAFE_CAR x2 in
        let x0 = SAFE_CAR x1 in
        let xs = x0 :: xs in
        let x0 = Sym "LET" in
        let xs = x0 :: xs in
        let x0 = Sym "NIL" in
          (x0,x1,x2,xs)
      else
        let x0 = SAFE_CAR x1 in
        let xs = x0 :: xs in
        let xs = x2 :: xs in
        let x2 = Val 1 in
        let xs = x2 :: xs in
        let x1 = SAFE_CDR x1 in
        let x1 = SAFE_CDR x1 in
        let x2 = SAFE_CAR x1 in
        let x0 = Sym "NIL" in
          (x0,x1,x2,xs)
  else if x0 = Sym "COND" then
    let x0 = HD xs in
    let xs = TL xs in
    let x1 = HD xs in
    let xs = TL xs in
      if x0 = Sym "EQUAL" then
        let xs = x2 :: xs in
        let x0 = Sym "COND" in
        let xs = x0 :: xs in
        let xs = x0 :: xs in
        let x0 = Sym "CONSP" in
        let xs = x0 :: xs in
        let x0 = SAFE_CAR x1 in
        let xs = x0 :: xs in
        let x0 = Sym "EQUAL" in
        let xs = x0 :: xs in
        let x2 = SAFE_CDR x1 in
        let x0 = SAFE_CAR x2 in
        let xs = x0 :: xs in
        let x0 = Sym "EQUAL" in
        let xs = x0 :: xs in
        let x2 = Sym "NIL" in
        let x0 = Sym "LIST" in
          (x0,x1,x2,xs)
      else
        let x1 = Dot x1 x2 in
        let x2 = x1 in
        let x1 = Sym "NIL" in
        let x0 = Sym "T" in
          (x0,x1,x2,xs)
  else if x0 = Sym "T" then  (* continue / return *)
    let x0 = HD xs in
    let xs = TL xs in
      if x0 = Sym "NIL" then
        let x0 = Sym "FIRST" in
          (x0,x1,x2,xs)
      else if x0 = Sym "CONS" then
        let x0 = HD xs in
        let xs = TL xs in
        let x1 = Sym "NIL" in
        let x2 = Dot x2 x1 in
        let x0 = Dot x0 x2 in
        let x2 = x0 in
        let x0 = Sym "T" in
          (x0,x1,x2,xs)
      else if x0 = Sym "LIST" then
        let x0 = HD xs in
        let xs = TL xs in
        let x2 = Dot x2 x0 in
        let x0 = Sym "LIST" in
          (x0,x1,x2,xs)
      else if x0 = Sym "COND" then
        let x0 = HD xs in
        let xs = TL xs in
        let x2 = CDR x2 in
        let x2 = Dot x2 x0 in
        let x0 = Sym "COND" in
          (x0,x1,x2,xs)
      else if x0 = Sym "LET" then
        let x0 = Sym "NIL" in
        let x2 = Dot x2 x0 in
        let x0 = HD xs in
        let xs = TL xs in
        let x0 = SFIX x0 in
        let x0 = Dot x0 x2 in
        let x2 = HD xs in
        let xs = TL xs in
        let x0 = Dot x0 x2 in
        let x2 = x0 in
        let x0 = Sym "LET" in
          (x0,x1,x2,xs)
      else if x0 = Val 1 then (* final case for let *)
        let x1 = Sym "NIL" in
        let x2 = Dot x2 x1 in
        let x1 = HD xs in
        let xs = TL xs in
        let x1 = Dot x1 x2 in
        let x2 = HD xs in
        let xs = TL xs in
        let x2 = Dot x2 x1 in
        let x1 = Sym "NIL" in
        let x0 = Sym "T" in
          (x0,x1,x2,xs)
      else if x0 = Sym "LAMBDA" then
        let x1 = Sym "NIL" in
        let x2 = Dot x2 x1 in
        let x1 = HD xs in
        let xs = TL xs in
        let x1 = Dot x1 x2 in
        let x0 = Dot x0 x1 in
        let x2 = HD xs in
        let xs = TL xs in
        let xs = x0 :: xs in
        let x0 = Sym "CONSP" in
        let xs = x0 :: xs in
        let (x0,x2,xs) = mc_push_list (x0,x2,xs) in
        let x1 = Sym "NIL" in
        let x2 = Sym "NIL" in
        let x0 = Sym "LIST" in
          (x0,x1,x2,xs)
      else (x0,x1,x2,xs)
  else
    let x0 = Sym "FIRST" in (x0,x1,x2,xs)``;

val (_,mc_sexp2sexp_loop_def,mc_sexp2sexp_loop_pre_def) = compile "x64" ``
  mc_sexp2sexp_loop (x0,x1,x2,xs) =
    if x0 = Sym "FIRST" then (x0,x1,x2,xs) else
      let (x0,x1,x2,xs) = mc_sexp2sexp_aux (x0,x1,x2,xs) in
        mc_sexp2sexp_loop (x0,x1,x2,xs)``

val (_,mc_sexp2sexp_def,mc_sexp2sexp_pre_def) = compile "x64" ``
  mc_sexp2sexp (x0,x1,x2,xs) =
    let xs = x0 :: xs in
    let xs = x1 :: xs in
    let x0 = Sym "NIL" in
    let xs = x0 :: xs in
    let (x0,x1,x2,xs) = mc_sexp2sexp_loop (x0,x1,x2,xs) in
    let x1 = HD xs in
    let xs = TL xs in
    let x0 = HD xs in
    let xs = TL xs in
      (x0,x1,x2,xs)``;


val CAR_LESS_SUC = prove(
  ``!x. LSIZE x < SUC n ==> LSIZE (CAR x) < SUC n``,
  Cases_on `x` \\ EVAL_TAC \\ DECIDE_TAC);

val CDR_LESS_SUC = prove(
  ``!x. LSIZE x < SUC n ==> LSIZE (CDR x) < SUC n``,
  Cases_on `x` \\ EVAL_TAC \\ DECIDE_TAC);

val LSIZE_EVERY_sexp2list = prove(
  ``!x3 x2. LSIZE x3 < LSIZE x2 ==> EVERY (\x. LSIZE x < LSIZE x2) (sexp2list x3)``,
  REVERSE Induct \\ ASM_SIMP_TAC std_ss [EVERY_DEF,sexp2list_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [LSIZE_def] THEN1 DECIDE_TAC
  \\ `LSIZE x3' < LSIZE x2` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []);

val LSIZE_CAR_LESS_EQ = prove(
  ``!x. LSIZE (CAR x) <= LSIZE x /\ LSIZE (CDR x) <= LSIZE x``,
  Cases \\ SIMP_TAC std_ss [CAR_def,CDR_def,LSIZE_def] \\ DECIDE_TAC);

val mc_sexp2sexp_loop_alt =
  SIMP_RULE std_ss [mc_sexp2sexp_aux_pre_def,mc_sexp2sexp_aux_def,
    mc_push_list_thm,LET_DEF,mc_list_sfix_thm] mc_sexp2sexp_loop_def

val mc_sexp2sexp_loop_pre_alt =
  SIMP_RULE std_ss [mc_sexp2sexp_aux_pre_def,mc_sexp2sexp_aux_def,
    mc_push_list_thm,LET_DEF,mc_list_sfix_thm] mc_sexp2sexp_loop_pre_def

val mc_sexp2sexp_loop_lemma = prove(
  ``!x2 x1 xs.
      (mc_sexp2sexp_loop_pre (Sym "NIL",x1,x2,xs) =
       mc_sexp2sexp_loop_pre (Sym "T",Sym "NIL",sexp2sexp x2,xs)) /\
      (mc_sexp2sexp_loop (Sym "NIL",x1,x2,xs) =
       mc_sexp2sexp_loop (Sym "T",Sym "NIL",sexp2sexp x2,xs))``,
  STRIP_TAC \\ completeInduct_on `LSIZE x2` \\ NTAC 4 STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL_IMP]
  \\ SIMP_TAC std_ss [Once mc_sexp2sexp_loop_pre_alt]
  \\ SIMP_TAC std_ss [Once mc_sexp2sexp_loop_alt]
  \\ ONCE_REWRITE_TAC [sexp2sexp_def]
  \\ Cases_on `x2 = Sym "NIL"` THEN1 FULL_SIMP_TAC (srw_ss()) [LET_DEF,list2sexp_def]
  \\ Cases_on `x2 = Sym "T"` THEN1 FULL_SIMP_TAC (srw_ss()) [LET_DEF,list2sexp_def]
  \\ Cases_on `isVal x2` THEN1 FULL_SIMP_TAC (srw_ss()) [LET_DEF,list2sexp_def]
  \\ Cases_on `isSym x2` THEN1 FULL_SIMP_TAC (srw_ss()) [LET_DEF,list2sexp_def]
  \\ FULL_SIMP_TAC std_ss [LET_DEF,SAFE_CAR_def,SAFE_CDR_def]
  \\ Cases_on `CAR x2 = Sym "QUOTE"` \\ FULL_SIMP_TAC std_ss []
  THEN1 FULL_SIMP_TAC (srw_ss()) [LET_DEF,list2sexp_def]
  \\ `LSIZE (CDR x2) < LSIZE x2 /\
      LSIZE (CAR (CDR x2)) < LSIZE x2 /\
      LSIZE (CAR (CDR (CDR x2))) < LSIZE x2 /\
      LSIZE (CAR (CDR (CDR (CDR x2)))) < LSIZE x2` by
   (Cases_on `x2` \\ FULL_SIMP_TAC std_ss [isVal_def,isSym_def,CDR_def,LSIZE_def]
    \\ REPEAT STRIP_TAC
    \\ REPEAT (MATCH_MP_TAC CAR_LESS_SUC ORELSE MATCH_MP_TAC CDR_LESS_SUC)
    \\ DECIDE_TAC)
  \\ Cases_on `CAR x2 = Sym "FIRST"` \\ FULL_SIMP_TAC std_ss [] THEN1
   (FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_alt,LET_DEF,HD,list2sexp_def]
    \\ FULL_SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_pre_alt,LET_DEF,HD,list2sexp_def])
  \\ Cases_on `CAR x2 = Sym "SECOND"` \\ FULL_SIMP_TAC std_ss [] THEN1
   (FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_alt,LET_DEF,HD,list2sexp_def]
    \\ FULL_SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_pre_alt,LET_DEF,HD,list2sexp_def])
  \\ Cases_on `CAR x2 = Sym "THIRD"` \\ FULL_SIMP_TAC std_ss [] THEN1
   (FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_alt,LET_DEF,HD,list2sexp_def]
    \\ FULL_SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_pre_alt,LET_DEF,HD,list2sexp_def])
  \\ Cases_on `CAR x2 = Sym "FOURTH"` \\ FULL_SIMP_TAC std_ss [] THEN1
   (FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_alt,LET_DEF,HD,list2sexp_def]
    \\ FULL_SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_pre_alt,LET_DEF,HD,list2sexp_def])
  \\ Cases_on `CAR x2 = Sym "FIFTH"` \\ FULL_SIMP_TAC std_ss [] THEN1
   (FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_alt,LET_DEF,HD,list2sexp_def]
    \\ FULL_SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_pre_alt,LET_DEF,HD,list2sexp_def])
  \\ Cases_on `CAR x2 = Sym "IF"` \\ FULL_SIMP_TAC std_ss [list2sexp_def] THEN1
   (FULL_SIMP_TAC (srw_ss()) []
    \\ NTAC 10 (SIMP_TAC std_ss [Once mc_sexp2sexp_loop_alt]
                \\ SIMP_TAC std_ss [Once mc_sexp2sexp_loop_pre_alt]
                \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF,HD,list2sexp_def]))
  \\ Cases_on `CAR x2 = Sym "DEFUN"` \\ FULL_SIMP_TAC (srw_ss()) [mc_list_sfix_thm,CAR_def]
  THEN1 (FULL_SIMP_TAC std_ss [HD,TL,SFIX_sfix])
  \\ FULL_SIMP_TAC std_ss [mc_push_list_thm]
  \\ `!x1 x3 xs x zs.
        LSIZE x3 < LSIZE x2 ==>
        (mc_sexp2sexp_loop_pre (Sym "LIST",x1,list2sexp zs,
           push_list_fun (REVERSE (sexp2list x3)) ++ Sym "CONSP"::x::xs) =
         mc_sexp2sexp_loop_pre (Sym "T",Sym "NIL",
           list2sexp (x::MAP (\a. sexp2sexp a) (sexp2list x3) ++ zs),xs)) /\
        (mc_sexp2sexp_loop (Sym "LIST",x1,list2sexp zs,
           push_list_fun (REVERSE (sexp2list x3)) ++ Sym "CONSP"::x::xs) =
         mc_sexp2sexp_loop (Sym "T",Sym "NIL",
           list2sexp (x::MAP (\a. sexp2sexp a) (sexp2list x3) ++ zs),xs))` by
     (REPEAT STRIP_TAC
      \\ `EVERY (\x. LSIZE x < LSIZE x2) (sexp2list x3)` by METIS_TAC [LSIZE_EVERY_sexp2list]
      \\ POP_ASSUM MP_TAC
      \\ Q.SPEC_TAC (`x1`,`x1`)
      \\ Q.SPEC_TAC (`zs`,`zs`)
      \\ SIMP_TAC std_ss []
      \\ `sexp2list x3 = REVERSE (REVERSE (sexp2list x3))` by METIS_TAC [REVERSE_REVERSE]
      \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
      \\ Q.SPEC_TAC (`REVERSE (sexp2list x3)`,`ys`)
      \\ SIMP_TAC std_ss [REVERSE_REVERSE]
      \\ Induct THEN1
       (SIMP_TAC std_ss [push_list_fun_def,APPEND,REVERSE_DEF,EVERY_DEF,MAP]
        \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_alt,LET_DEF,list2sexp_def]
        \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_pre_alt,LET_DEF,list2sexp_def])
      \\ SIMP_TAC std_ss [push_list_fun_def,APPEND,REVERSE_DEF,EVERY_DEF,MAP]
      \\ SIMP_TAC std_ss [MAP_APPEND,MAP,APPEND,GSYM APPEND_ASSOC,EVERY_APPEND,EVERY_DEF]
      \\ REPEAT STRIP_TAC
      \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_alt,LET_DEF,list2sexp_def]
      \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_pre_alt,LET_DEF,list2sexp_def]
      \\ ASM_SIMP_TAC std_ss []
      \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_alt,LET_DEF,list2sexp_def]
      \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_pre_alt,LET_DEF,list2sexp_def]
      \\ SIMP_TAC std_ss [GSYM list2sexp_def]
      \\ ASM_SIMP_TAC std_ss [] \\ ASM_SIMP_TAC std_ss [list2sexp_def,APPEND])
  \\ Cases_on `CAR (CAR x2) = Sym "LAMBDA"` \\ ASM_SIMP_TAC std_ss [] THEN1
   (`LSIZE (CAR (CDR (CDR (CAR x2)))) < LSIZE x2` by
      (Cases_on `x2` \\ FULL_SIMP_TAC std_ss [isVal_def,isSym_def,CDR_def,LSIZE_def,CAR_def]
       \\ REPEAT STRIP_TAC
       \\ REPEAT (MATCH_MP_TAC CAR_LESS_SUC ORELSE MATCH_MP_TAC CDR_LESS_SUC)
       \\ DECIDE_TAC)
    \\ ASM_SIMP_TAC std_ss []
    \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_alt,LET_DEF,mc_push_list_thm]
    \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_pre_alt,LET_DEF,mc_push_list_thm]
    \\ `LSIZE (CDR x2) < LSIZE x2` by
       (Cases_on `x2` \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [isVal_def,isSym_def] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [GSYM list2sexp_def,APPEND_NIL])
  \\ Cases_on `CAR x2 = Sym "COND"` \\ ASM_SIMP_TAC std_ss [] THEN1
   (FULL_SIMP_TAC std_ss [GSYM list2sexp_def]
    \\ `!x1 x3 xs x zs.
        LSIZE x3 < LSIZE x2 ==>
        (mc_sexp2sexp_loop_pre (Sym "COND",x1,list2sexp zs,
           push_list_fun (REVERSE (sexp2list x3)) ++
           Sym "COND"::Sym "COND"::xs) =
         mc_sexp2sexp_loop_pre (Sym "T",Sym "NIL",
           list2sexp (Sym "COND"::
              MAP (\a. list2sexp [sexp2sexp (CAR a); sexp2sexp (CAR (CDR a))])
                (sexp2list x3) ++ zs),xs)) /\
        (mc_sexp2sexp_loop (Sym "COND",x1,list2sexp zs,
           push_list_fun (REVERSE (sexp2list x3)) ++
           Sym "COND"::Sym "COND"::xs) =
         mc_sexp2sexp_loop (Sym "T",Sym "NIL",
           list2sexp (Sym "COND"::
              MAP (\a. list2sexp [sexp2sexp (CAR a); sexp2sexp (CAR (CDR a))])
                (sexp2list x3) ++ zs),xs))` suffices_by (STRIP_TAC THEN Q.PAT_X_ASSUM `LSIZE (CDR x2) < LSIZE x2` ASSUME_TAC
      \\ FULL_SIMP_TAC std_ss [list2sexp_def,APPEND_NIL])
    \\ NTAC 6 STRIP_TAC
    \\ `EVERY (\x. LSIZE x < LSIZE x2) (sexp2list x3)` by METIS_TAC [LSIZE_EVERY_sexp2list]
    \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
    \\ Q.SPEC_TAC (`x1`,`x1`)
    \\ Q.SPEC_TAC (`zs`,`zs`)
    \\ SIMP_TAC std_ss []
    \\ `sexp2list x3 = REVERSE (REVERSE (sexp2list x3))` by METIS_TAC [REVERSE_REVERSE]
    \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
    \\ Q.SPEC_TAC (`REVERSE (sexp2list x3)`,`ys`)
    \\ SIMP_TAC std_ss [REVERSE_REVERSE]
    \\ Induct THEN1
       (SIMP_TAC std_ss [push_list_fun_def,APPEND,REVERSE_DEF,EVERY_DEF,MAP]
        \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_pre_alt,LET_DEF,list2sexp_def]
        \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_alt,LET_DEF,list2sexp_def])
    \\ SIMP_TAC std_ss [push_list_fun_def,APPEND,REVERSE_DEF,EVERY_DEF,MAP]
    \\ SIMP_TAC std_ss [MAP_APPEND,MAP,APPEND,GSYM APPEND_ASSOC,EVERY_APPEND,EVERY_DEF]
    \\ NTAC 5 STRIP_TAC
    \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_alt,LET_DEF,list2sexp_def]
    \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_pre_alt,LET_DEF,list2sexp_def]
    \\ SIMP_TAC std_ss [SAFE_CAR_def,SAFE_CDR_def]
    \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_alt,LET_DEF,list2sexp_def]
    \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_pre_alt,LET_DEF,list2sexp_def]
    \\ `LSIZE (CAR (CDR h)) < LSIZE x2 /\ LSIZE (CAR h) < LSIZE x2` by
     (REPEAT STRIP_TAC \\ MATCH_MP_TAC LESS_EQ_LESS_TRANS
      \\ Q.EXISTS_TAC `LSIZE h` \\ ASM_SIMP_TAC std_ss []
      \\ METIS_TAC [LSIZE_CAR_LESS_EQ,LESS_EQ_TRANS])
    \\ FULL_SIMP_TAC std_ss [list2sexp_def]
    \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_alt,LET_DEF,list2sexp_def]
    \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_pre_alt,LET_DEF,list2sexp_def]
    \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_alt,LET_DEF,list2sexp_def]
    \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_pre_alt,LET_DEF,list2sexp_def]
    \\ ASM_SIMP_TAC std_ss []
    \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_alt,LET_DEF,list2sexp_def]
    \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_pre_alt,LET_DEF,list2sexp_def]
    \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_alt,LET_DEF,list2sexp_def]
    \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_pre_alt,LET_DEF,list2sexp_def]
    \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_alt,LET_DEF,list2sexp_def,CDR_def]
    \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_pre_alt,LET_DEF,list2sexp_def,CDR_def]
    \\ SIMP_TAC std_ss [GSYM list2sexp_def] \\ ASM_SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [list2sexp_def,MAP,MAP_APPEND,APPEND,isDot_def])
  \\ `!x1 x3 xs x zs.
        LSIZE x3 < LSIZE x2 ==>
        (mc_sexp2sexp_loop_pre (Sym "LET",x1,list2sexp zs,
           push_list_fun (REVERSE (sexp2list x3)) ++ Val 1::x2::xs) =
         mc_sexp2sexp_loop_pre (Sym "T",Sym "NIL",
           list2sexp [CAR x2; list2sexp (MAP (\a. list2sexp
              [sfix (CAR a); sexp2sexp (CAR (CDR a))]) (sexp2list x3) ++ zs);
              sexp2sexp (CAR (CDR (CDR x2)))],xs)) /\
        (mc_sexp2sexp_loop (Sym "LET",x1,list2sexp zs,
           push_list_fun (REVERSE (sexp2list x3)) ++ Val 1::x2::xs) =
         mc_sexp2sexp_loop (Sym "T",Sym "NIL",
           list2sexp [CAR x2; list2sexp (MAP (\a. list2sexp
              [sfix (CAR a); sexp2sexp (CAR (CDR a))]) (sexp2list x3) ++ zs);
              sexp2sexp (CAR (CDR (CDR x2)))],xs))` by
     (NTAC 6 STRIP_TAC
      \\ `EVERY (\x. LSIZE x < LSIZE x2) (sexp2list x3)` by METIS_TAC [LSIZE_EVERY_sexp2list]
      \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
      \\ Q.SPEC_TAC (`x1`,`x1`)
      \\ Q.SPEC_TAC (`zs`,`zs`)
      \\ SIMP_TAC std_ss []
      \\ `sexp2list x3 = REVERSE (REVERSE (sexp2list x3))` by METIS_TAC [REVERSE_REVERSE]
      \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
      \\ Q.SPEC_TAC (`REVERSE (sexp2list x3)`,`ys`)
      \\ SIMP_TAC std_ss [REVERSE_REVERSE]
      \\ Induct THEN1
       (SIMP_TAC std_ss [push_list_fun_def,APPEND,REVERSE_DEF,EVERY_DEF,MAP]
        \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_alt,LET_DEF,list2sexp_def]
        \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_pre_alt,LET_DEF,list2sexp_def]
        \\ SIMP_TAC std_ss [SAFE_CAR_def,SAFE_CDR_def]
        \\ ASM_SIMP_TAC std_ss []
        \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_alt,LET_DEF,list2sexp_def]
        \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_pre_alt,LET_DEF,list2sexp_def])
      \\ SIMP_TAC std_ss [push_list_fun_def,APPEND,REVERSE_DEF,EVERY_DEF,MAP]
      \\ SIMP_TAC std_ss [MAP_APPEND,MAP,APPEND,GSYM APPEND_ASSOC,EVERY_APPEND,EVERY_DEF]
      \\ NTAC 5 STRIP_TAC
      \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_alt,LET_DEF,list2sexp_def]
      \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_pre_alt,LET_DEF,list2sexp_def]
      \\ `LSIZE (CAR (CDR h)) < LSIZE x2` by
       (REPEAT STRIP_TAC \\ MATCH_MP_TAC LESS_EQ_LESS_TRANS
        \\ Q.EXISTS_TAC `LSIZE h` \\ ASM_SIMP_TAC std_ss []
        \\ METIS_TAC [LSIZE_CAR_LESS_EQ,LESS_EQ_TRANS])
      \\ ASM_SIMP_TAC std_ss [SAFE_CAR_def,SAFE_CDR_def]
      \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_alt,LET_DEF,list2sexp_def]
      \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_pre_alt,LET_DEF,list2sexp_def]
      \\ SIMP_TAC std_ss [GSYM list2sexp_def] \\ ASM_SIMP_TAC std_ss []
      \\ ASM_SIMP_TAC std_ss [list2sexp_def,APPEND,SFIX_sfix])
  \\ Cases_on `CAR x2 = Sym "LET"` \\ ASM_SIMP_TAC std_ss [] THEN1
   (Q.PAT_X_ASSUM `LSIZE (CAR (CDR x2)) < LSIZE x2` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss [GSYM list2sexp_def,APPEND_NIL])
  \\ Cases_on `CAR x2 = Sym "LET*"` \\ ASM_SIMP_TAC std_ss [] THEN1
   (Q.PAT_X_ASSUM `LSIZE (CAR (CDR x2)) < LSIZE x2` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss [GSYM list2sexp_def,APPEND_NIL])
  THEN1
   (Q.PAT_X_ASSUM `!x.bbb` (K ALL_TAC)
    \\ Q.PAT_X_ASSUM `!x.bbb` (MP_TAC o Q.SPECL [`x1`,`CDR x2`,`xs`,`SFIX (CAR x2)`,`[]`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (Cases_on `x2` \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [isVal_def,isSym_def] \\ DECIDE_TAC)
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [list2sexp_def]
    \\ SIMP_TAC std_ss [SFIX_sfix,list2sexp_def,APPEND_NIL]));

val mc_sexp2sexp_thm = prove(
  ``mc_sexp2sexp_pre (x0,x1,x2,xs) /\
    (mc_sexp2sexp (x0,x1,x2,xs) = (x0,x1,sexp2sexp x2,xs))``,
  SIMP_TAC std_ss [mc_sexp2sexp_def,mc_sexp2sexp_pre_def,
                   LET_DEF,mc_sexp2sexp_loop_lemma]
  \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_alt,LET_DEF]
  \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_pre_alt,LET_DEF]
  \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_alt,LET_DEF]
  \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_pre_alt,LET_DEF]
  \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_alt,LET_DEF]
  \\ SIMP_TAC (srw_ss()) [Once mc_sexp2sexp_loop_alt,LET_DEF]);


(* btree implementation -- allows fast lookup and adding elements *)

Definition SPLIT_LIST_def:
  (SPLIT_LIST [] = ([],[])) /\
  (SPLIT_LIST [x] = ([x],[])) /\
  (SPLIT_LIST (x1::x2::xs) =
     (x1::FST (SPLIT_LIST xs),x2::SND (SPLIT_LIST xs)))
End

val LENGTH_SPLIT_LIST = prove(
  ``!xs. (LENGTH (FST (SPLIT_LIST xs)) <= LENGTH xs) /\
         (LENGTH (SND (SPLIT_LIST xs)) <= LENGTH xs)``,
  HO_MATCH_MP_TAC (fetch "-" "SPLIT_LIST_ind")
  \\ SIMP_TAC std_ss [SPLIT_LIST_def,LENGTH] \\ DECIDE_TAC);

val list2btree_def = tDefine "list2tree" `
  (list2btree [] = Sym "NIL") /\
  (list2btree (x::xs) =
     Dot x (if xs = [] then Sym "NIL" else
              Dot (list2btree (FST (SPLIT_LIST xs)))
                  (list2btree (SND (SPLIT_LIST xs)))))`
 (WF_REL_TAC `measure (LENGTH)` \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ METIS_TAC [DECIDE ``n < SUC n``,LENGTH_SPLIT_LIST,LESS_EQ_LESS_TRANS]);

val btree_lookup_def = Define `
  btree_lookup n x =
    if n < 2 then CAR x else
      if EVEN n then btree_lookup (n DIV 2) (CAR (CDR x))
                else btree_lookup (n DIV 2) (CDR (CDR x))`;

val btree_insert_def = Define `
  btree_insert n y x =
    if n < 2 then Dot y (Sym "NIL") else
      if EVEN n then
        Dot (CAR x) (Dot (btree_insert (n DIV 2) y (CAR (CDR x))) (CDR (CDR x)))
      else
        Dot (CAR x) (Dot (CAR (CDR x)) (btree_insert (n DIV 2) y (CDR (CDR x))))`;

(*
  1
  10 11
  100 101 110 111
  1000 1001 1010 1011 1100 1101 1110 1111
*)

Theorem EL_SPLIT_LIST[local]:
  !xs n.
      n < LENGTH xs ==>
      (EL n xs = if EVEN n then EL (n DIV 2) (FST (SPLIT_LIST xs))
                           else EL (n DIV 2) (SND (SPLIT_LIST xs)))
Proof
  recInduct SPLIT_LIST_ind
  \\ SIMP_TAC std_ss [SPLIT_LIST_def,LENGTH] \\ REPEAT STRIP_TAC
  \\ Cases_on `n` \\ SIMP_TAC std_ss [EL,HD]
  \\ Cases_on `n'` \\ SIMP_TAC std_ss [EL,HD,TL,EVEN]
  \\ FULL_SIMP_TAC std_ss [ADD1,GSYM ADD_ASSOC]
  \\ SIMP_TAC std_ss [(SIMP_RULE std_ss [] (Q.SPEC `2` ADD_DIV_ADD_DIV))
       |> RW1 [ADD_COMM] |> Q.SPEC `1` |> SIMP_RULE std_ss []]
  \\ SIMP_TAC std_ss [GSYM ADD1,EL,TL]
QED

val LENGTH_SPLIT_LIST = prove(
  ``!xs. (LENGTH (SND (SPLIT_LIST xs)) = LENGTH xs DIV 2) /\
         (LENGTH (FST (SPLIT_LIST xs)) = LENGTH xs DIV 2 +  LENGTH xs MOD 2)``,
  HO_MATCH_MP_TAC (fetch "-" "SPLIT_LIST_ind")
  \\ SIMP_TAC std_ss [SPLIT_LIST_def,LENGTH]
  \\ FULL_SIMP_TAC std_ss [ADD1,GSYM ADD_ASSOC]
  \\ SIMP_TAC std_ss [(SIMP_RULE std_ss [] (Q.SPEC `2` ADD_DIV_ADD_DIV))
       |> RW1 [ADD_COMM] |> Q.SPEC `1` |> SIMP_RULE std_ss []]
  \\ SIMP_TAC std_ss [(SIMP_RULE std_ss [] (Q.SPEC `2` MOD_TIMES))
       |> RW1 [ADD_COMM] |> Q.SPEC `1` |> SIMP_RULE std_ss []]
  \\ ASM_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM]);

val NOT_EVEN_LESS = prove(
  ``~EVEN n /\ n < m ==> n < m DIV 2 * 2``,
  Cases_on `EVEN m`
  \\ IMP_RES_TAC EVEN_ODD_EXISTS
  \\ FULL_SIMP_TAC std_ss [RW1 [MULT_COMM] MULT_DIV]
  \\ SIMP_TAC std_ss [Once MULT_COMM]
  \\ FULL_SIMP_TAC std_ss [GSYM ODD_EVEN]
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC EVEN_ODD_EXISTS
  \\ FULL_SIMP_TAC std_ss [ADD1,RW1[MULT_COMM]DIV_MULT]
  \\ DECIDE_TAC);

val DIV_LESS_LENGTH_SPLIT_LIST = prove(
  ``n < LENGTH (t:SExp list) ==>
    if EVEN n then n DIV 2 < LENGTH (FST (SPLIT_LIST t))
              else n DIV 2 < LENGTH (SND (SPLIT_LIST t))``,
  Cases_on `EVEN n` \\ ASM_SIMP_TAC std_ss [] THEN1
   (FULL_SIMP_TAC std_ss [LENGTH_SPLIT_LIST]
    \\ SIMP_TAC std_ss [DIV_LT_X,RIGHT_ADD_DISTRIB] \\ STRIP_TAC
    \\ ASSUME_TAC (Q.SPEC `LENGTH (t:SExp list)` (MATCH_MP DIVISION (DECIDE ``0<2``)))
    \\ DECIDE_TAC) THEN1
   (FULL_SIMP_TAC std_ss [LENGTH_SPLIT_LIST]
    \\ SIMP_TAC std_ss [DIV_LT_X,RIGHT_ADD_DISTRIB]
    \\ METIS_TAC [NOT_EVEN_LESS]));

val btree_lookup_thm = prove(
  ``!n xs.
      n < LENGTH xs ==>
      (btree_lookup (n+1) (list2btree xs) = EL n xs)``,
  completeInduct_on `n` \\ REPEAT STRIP_TAC
  \\ Cases_on `n = 0` \\ ASM_SIMP_TAC std_ss [Once btree_lookup_def] THEN1
   (Cases_on `xs` \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ SIMP_TAC std_ss [list2btree_def,CAR_def,EL,HD])
  \\ `~(n + 1 < 2)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [EVEN,GSYM ADD1]
  \\ Cases_on `n` \\ FULL_SIMP_TAC std_ss [EVEN]
  \\ SIMP_TAC std_ss [ADD1,GSYM ADD_ASSOC]
  \\ SIMP_TAC std_ss [(SIMP_RULE std_ss [] (Q.SPEC `2` ADD_DIV_ADD_DIV))
       |> RW1 [ADD_COMM] |> Q.SPEC `1` |> SIMP_RULE std_ss []]
  \\ SIMP_TAC std_ss [RW[ADD1]EL]
  \\ Cases_on `xs` \\ FULL_SIMP_TAC std_ss [LENGTH,TL]
  \\ SIMP_TAC std_ss [list2btree_def,CAR_def,EL,HD,CDR_def]
  \\ Cases_on `t = []` \\ FULL_SIMP_TAC std_ss [LENGTH,CDR_def,CAR_def]
  \\ `n' DIV 2 < SUC n'` by (ASM_SIMP_TAC std_ss [DIV_LT_X] \\ DECIDE_TAC)
  \\ IMP_RES_TAC DIV_LESS_LENGTH_SPLIT_LIST
  \\ Cases_on `EVEN n'` \\ FULL_SIMP_TAC std_ss []
  \\ RES_TAC \\ ASM_SIMP_TAC std_ss [EL_SPLIT_LIST]);

val SPLIT_LIST_SNOC = prove(
  ``!xs x.
     (FST (SPLIT_LIST (xs ++ [x])) =
      if EVEN (LENGTH xs) then FST (SPLIT_LIST xs) ++ [x]
                          else FST (SPLIT_LIST xs)) /\
     (SND (SPLIT_LIST (xs ++ [x])) =
      if EVEN (LENGTH xs) then SND (SPLIT_LIST xs)
                          else SND (SPLIT_LIST xs) ++ [x])``,
  STRIP_TAC \\ completeInduct_on `LENGTH xs` \\ NTAC 3 STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL_IMP]
  \\ Cases_on `xs` THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
  \\ Cases_on `t` THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss [LENGTH,EVEN,SPLIT_LIST_def,APPEND]
  \\ `LENGTH t' < SUC (SUC (LENGTH t'))` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC []);

val LENGTH_SPLIT_LIST_LESS_SUC_LENGTH = prove(
  ``LENGTH (FST (SPLIT_LIST t)) < SUC (LENGTH t) /\
    LENGTH (SND (SPLIT_LIST t)) < SUC (LENGTH (t:SExp list))``,
  SIMP_TAC std_ss [LENGTH_SPLIT_LIST] \\ Q.SPEC_TAC (`LENGTH t`,`n`)
  \\ SIMP_TAC std_ss [DIV_LT_X] \\ REVERSE (REPEAT STRIP_TAC) THEN1 DECIDE_TAC
  \\ MATCH_MP_TAC LESS_EQ_LESS_TRANS \\ Q.EXISTS_TAC `2 * (n DIV 2) + n MOD 2`
  \\ REPEAT STRIP_TAC THEN1 (SIMP_TAC std_ss [TIMES2] \\ DECIDE_TAC)
  \\ ONCE_REWRITE_TAC [MULT_COMM]
  \\ SIMP_TAC std_ss [GSYM (MATCH_MP DIVISION (DECIDE ``0<2:num``))]);

val btree_insert_thm = prove(
  ``!xs y. btree_insert (LENGTH xs + 1) y (list2btree xs) = list2btree (xs ++ [y])``,
  STRIP_TAC \\ completeInduct_on `LENGTH xs` \\ REPEAT STRIP_TAC
  \\ Cases_on `xs` THEN1
   (SIMP_TAC std_ss [LENGTH,list2btree_def,APPEND,SPLIT_LIST_def]
    \\ SIMP_TAC std_ss [Once btree_insert_def])
  \\ SIMP_TAC std_ss [list2btree_def,APPEND]
  \\ Cases_on `t = []` \\ FULL_SIMP_TAC std_ss []
  THEN1 (FULL_SIMP_TAC std_ss [LENGTH,APPEND,NOT_CONS_NIL] \\ EVAL_TAC)
  \\ SIMP_TAC std_ss [APPEND_eq_NIL,NOT_CONS_NIL]
  \\ SIMP_TAC std_ss [Once btree_insert_def,CAR_def,CDR_def,LENGTH]
  \\ `~(SUC (LENGTH t) + 1 < 2)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [GSYM ADD1,EVEN]
  \\ SIMP_TAC std_ss [ADD1,GSYM ADD_ASSOC]
  \\ SIMP_TAC std_ss [(SIMP_RULE std_ss [] (Q.SPEC `2` ADD_DIV_ADD_DIV))
       |> RW1 [ADD_COMM] |> Q.SPEC `1` |> SIMP_RULE std_ss []]
  \\ FULL_SIMP_TAC std_ss [LENGTH,PULL_FORALL_IMP]
  \\ STRIP_ASSUME_TAC LENGTH_SPLIT_LIST_LESS_SUC_LENGTH
  \\ RES_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [LENGTH_SPLIT_LIST]
  \\ REVERSE (Cases_on `EVEN (LENGTH t)`)
  \\ ASM_SIMP_TAC std_ss [SPLIT_LIST_SNOC]
  \\ FULL_SIMP_TAC std_ss [EVEN_MOD2]);


(* tail-recursive version of insert *)

val btree_insert_pushes_def = Define `
  btree_insert_pushes n x =
    if n < 2 then [] else
      if EVEN n then
        btree_insert_pushes (n DIV 2) (CAR (CDR x)) ++ [Val 0;x]
      else
        btree_insert_pushes (n DIV 2) (CDR (CDR x)) ++ [Val 1;x]`;

val btree_insert_pushes_tr_def = Define `
  btree_insert_pushes_tr n x xs =
    if n < 2 then xs else
      if EVEN n then
        btree_insert_pushes_tr (n DIV 2) (CAR (CDR x)) ([Val 0;x] ++ xs)
      else
        btree_insert_pushes_tr (n DIV 2) (CDR (CDR x)) ([Val 1;x] ++ xs)`;

val (_,mc_btree_insert_pushes_def,mc_btree_insert_pushes_pre_def) = compile "x64" ``
  mc_btree_insert_pushes (x0,x1,x2,xs) =
    if x0 = Val 0 then (x0,x1,x2,xs) else
    if x0 = Val 1 then (x0,x1,x2,xs) else
      if EVEN (getVal x0) then
        let x2 = Val 0 in
        let xs = x1::xs in
        let xs = x2::xs in
        let x0 = Val (getVal x0 DIV 2) in
        let x1 = SAFE_CDR x1 in
        let x1 = SAFE_CAR x1 in
          mc_btree_insert_pushes (x0,x1,x2,xs)
      else
        let x2 = Val 1 in
        let xs = x1::xs in
        let xs = x2::xs in
        let x0 = Val (getVal x0 DIV 2) in
        let x1 = SAFE_CDR x1 in
        let x1 = SAFE_CDR x1 in
          mc_btree_insert_pushes (x0,x1,x2,xs)``;

val btree_insert_pops_def = Define `
  (btree_insert_pops y [] = y) /\
  (btree_insert_pops y [x] = y) /\
  (btree_insert_pops y (x::x2::xs) =
     if x = Val 0 then
       btree_insert_pops (Dot (CAR x2) (Dot y (CDR (CDR x2)))) xs
     else
       btree_insert_pops (Dot (CAR x2) (Dot (CAR (CDR x2)) y)) xs)`

val (_,mc_btree_insert_pops_def,mc_btree_insert_pops_pre_def) = compile "x64" ``
  mc_btree_insert_pops (x0,x1,xs) =
    let x0 = HD xs in
    let xs = TL xs in
      if ~(isVal x0) then (x0,x1,xs) else
      if x0 = Val 0 then
        let x0 = HD xs in
        let x0 = SAFE_CDR x0 in
        let x0 = SAFE_CDR x0 in
        let x1 = Dot x1 x0 in
        let x0 = HD xs in
        let xs = TL xs in
        let x0 = SAFE_CAR x0 in
        let x0 = Dot x0 x1 in
        let x1 = x0 in
          mc_btree_insert_pops (x0,x1,xs)
      else
        let x0 = HD xs in
        let x0 = SAFE_CDR x0 in
        let x0 = SAFE_CAR x0 in
        let x0 = Dot x0 x1 in
        let x1 = x0 in
        let x0 = HD xs in
        let xs = TL xs in
        let x0 = SAFE_CAR x0 in
        let x0 = Dot x0 x1 in
        let x1 = x0 in
          mc_btree_insert_pops (x0,x1,xs)``

val btree_insert_tr_def = Define `
  btree_insert_tr n y x =
    btree_insert_pops (Dot y (Sym "NIL")) (btree_insert_pushes_tr n x [])`;

val btree_insert_pops_thm = prove(
  ``!n x y z xs.
      btree_insert_pops (btree_insert 0 y z) (btree_insert_pushes n x ++ xs) =
      btree_insert_pops (btree_insert n y x) xs``,
  STRIP_TAC \\ completeInduct_on `n` \\ REPEAT STRIP_TAC
  \\ Cases_on `n = 0` \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [Once btree_insert_pushes_def,APPEND]
  THEN1 (SIMP_TAC std_ss [Once btree_insert_def]
         \\ SIMP_TAC std_ss [Once btree_insert_def])
  \\ Cases_on `n < 2` \\ ASM_SIMP_TAC std_ss []
  THEN1 (ASM_SIMP_TAC std_ss [Once btree_insert_pushes_def,APPEND]
         \\ SIMP_TAC std_ss [Once btree_insert_def]
         \\ ASM_SIMP_TAC std_ss [Once btree_insert_def])
  \\ `n DIV 2 < n` by (SIMP_TAC std_ss [DIV_LT_X] \\ DECIDE_TAC)
  \\ RES_TAC \\ Cases_on `EVEN n` \\ ASM_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ ASM_SIMP_TAC std_ss [btree_insert_pops_def]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ ASM_SIMP_TAC (srw_ss()) [Once btree_insert_def]);

val EVEN_LENGTH_INDUCT = prove(
  ``!P. (P []) /\ (!y1 y2 ys. P ys ==> P (y1::y2::ys)) ==>
        !ys. EVEN (LENGTH ys) ==> P ys``,
  REPEAT STRIP_TAC \\ completeInduct_on `LENGTH ys`
  \\ Cases \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [EVEN,LENGTH]
  \\ FULL_SIMP_TAC std_ss [ADD1,GSYM ADD_ASSOC]);

val EVERY_OTHER_VAL_def = Define `
  (EVERY_OTHER_VAL [] = T) /\
  (EVERY_OTHER_VAL [x] = T) /\
  (EVERY_OTHER_VAL (x::y::xs) = isVal x /\ EVERY_OTHER_VAL xs)`;

val mc_btree_insert_pops_thm = prove(
  ``!ys. EVEN (LENGTH ys) ==> !x0 y xs.
      EVERY_OTHER_VAL ys ==>
      ?y0. mc_btree_insert_pops_pre (x0,y,ys ++ Sym "NIL"::xs) /\
           (mc_btree_insert_pops (x0,y,ys ++ Sym "NIL"::xs) =
             (y0,btree_insert_pops y ys,xs))``,
  HO_MATCH_MP_TAC EVEN_LENGTH_INDUCT \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [btree_insert_pops_def,APPEND]
  \\ ONCE_REWRITE_TAC [mc_btree_insert_pops_def,mc_btree_insert_pops_pre_def]
  \\ SIMP_TAC std_ss [HD,TL,LET_DEF,isVal_def,SAFE_CAR_def,SAFE_CDR_def]
  \\ FULL_SIMP_TAC std_ss [EVERY_OTHER_VAL_def,NOT_CONS_NIL]
  \\ METIS_TAC []);

val mc_btree_insert_pushes_thm = prove(
  ``!n x1 x2 xs.
      ?y0 y1 y2.
        mc_btree_insert_pushes_pre (Val n,x1,x2,xs) /\
        (mc_btree_insert_pushes (Val n,x1,x2,xs) =
          (y0,y1,y2,btree_insert_pushes n x1 ++ xs))``,
  STRIP_TAC \\ completeInduct_on `n` \\ REPEAT STRIP_TAC
  \\ Cases_on `n < 2` \\ ASM_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [Once btree_insert_pushes_def,SAFE_CAR_def,SAFE_CDR_def,
       Once mc_btree_insert_pushes_def,Once mc_btree_insert_pushes_pre_def,APPEND]
  THEN1 (SRW_TAC [] [] \\ `F` by DECIDE_TAC)
  \\ `~(n = 0) /\ ~(n = 1)` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [SExp_11,getVal_def,LET_DEF]
  \\ `n DIV 2 < n` by (SIMP_TAC std_ss [DIV_LT_X] \\ DECIDE_TAC)
  \\ RES_TAC \\ POP_ASSUM (fn th =>
       (STRIP_ASSUME_TAC o Q.SPECL [`Val 1::x1::xs`,`Val 1`,`CDR (CDR x1)`]) th THEN
       (STRIP_ASSUME_TAC o Q.SPECL [`Val 0::x1::xs`,`Val 0`,`CAR (CDR x1)`]) th)
  \\ ASM_SIMP_TAC std_ss [] \\ Cases_on `EVEN n` \\ ASM_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,isVal_def]);

val btree_insert_pushes_tr_thm = prove(
  ``!n x xs. btree_insert_pushes_tr n x xs = btree_insert_pushes n x ++ xs``,
  STRIP_TAC \\ completeInduct_on `n` \\ REPEAT STRIP_TAC
  \\ Cases_on `n < 2` \\ ASM_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [Once btree_insert_pushes_def,
       Once btree_insert_pushes_tr_def,APPEND]
  \\ `n DIV 2 < n` by (SIMP_TAC std_ss [DIV_LT_X] \\ DECIDE_TAC)
  \\ RES_TAC \\ Cases_on `EVEN n` \\ ASM_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]);

val btree_insert_tr_thm = prove(
  ``!n y x. btree_insert_tr n y x = btree_insert n y x``,
  SIMP_TAC std_ss [btree_insert_tr_def,btree_insert_pushes_tr_thm]
  \\ REPEAT STRIP_TAC \\ `Dot y (Sym "NIL") = btree_insert 0 y x` by EVAL_TAC
  \\ ASM_SIMP_TAC std_ss [btree_insert_pops_thm]
  \\ SIMP_TAC std_ss [Once btree_insert_pops_def]);

val (_,mc_btree_insert_def,mc_btree_insert_pre_def) = compile "x64" ``
  mc_btree_insert (x0,x1,x2,x3,xs) =
    let xs = x0::xs in
    let xs = x1::xs in
    let xs = x2::xs in
    let x2 = Sym "NIL" in
    let x3 = Dot x3 x2 in
    let xs = x2::xs in
    let (x0,x1,x2,xs) = mc_btree_insert_pushes (x0,x1,x2,xs) in
    let x1 = x3 in
    let (x0,x1,xs) = mc_btree_insert_pops (x0,x1,xs) in
    let x3 = x1 in
    let x2 = HD xs in
    let xs = TL xs in
    let x1 = HD xs in
    let xs = TL xs in
    let x0 = HD xs in
    let xs = TL xs in
      (x0,x1,x2,x3,xs)``

val EVEN_ADD2 = prove(
  ``EVEN (n + 2) = EVEN n``,
  SIMP_TAC std_ss [DECIDE ``n+2 = SUC (SUC n)``,EVEN]);

val btree_insert_pushes_lemma_step = prove(
  ``!ys. EVEN (LENGTH ys) ==>
         (EVERY_OTHER_VAL (ys ++ zs) = EVERY_OTHER_VAL ys /\ EVERY_OTHER_VAL zs)``,
  HO_MATCH_MP_TAC EVEN_LENGTH_INDUCT \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [EVERY_OTHER_VAL_def,APPEND,CONJ_ASSOC]);

val btree_insert_pushes_lemma = prove(
  ``!n y. EVEN (LENGTH (btree_insert_pushes n y)) /\
          EVERY_OTHER_VAL (btree_insert_pushes n y)``,
  completeInduct_on `n` \\ ONCE_REWRITE_TAC [btree_insert_pushes_def]
  \\ SRW_TAC [] [EVERY_OTHER_VAL_def,EVEN,LENGTH]
  \\ `n DIV 2 < n` by (SIMP_TAC std_ss [DIV_LT_X] \\ DECIDE_TAC)
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [EVEN_ADD2,
       btree_insert_pushes_lemma_step] \\ EVAL_TAC);

val mc_btree_insert_thm = prove(
  ``!n x1 x2 xs.
      mc_btree_insert_pre (Val n,y,x2,x,xs) /\
      (mc_btree_insert (Val n,y,x2,x,xs) =
         (Val n,y,x2,btree_insert n x y,xs))``,
  SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [mc_btree_insert_def,mc_btree_insert_pre_def]
  \\ FULL_SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC
  \\ STRIP_ASSUME_TAC (Q.SPECL [`n`,`y`,`Sym "NIL"`,`Sym "NIL"::x2::y::Val n::xs`] mc_btree_insert_pushes_thm)
  \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_ASSUME_TAC (Q.SPECL [`btree_insert_pushes n y`,`y0`,`Dot x (Sym "NIL")`,`x2::y::Val n::xs`]
        (SIMP_RULE std_ss [PULL_FORALL_IMP] mc_btree_insert_pops_thm))
  \\ FULL_SIMP_TAC std_ss [HD,TL,btree_insert_pushes_lemma]
  \\ FULL_SIMP_TAC std_ss [GSYM btree_insert_tr_thm]
  \\ FULL_SIMP_TAC std_ss [btree_insert_tr_def,btree_insert_pushes_tr_thm]
  \\ FULL_SIMP_TAC std_ss [APPEND_NIL,NOT_CONS_NIL]);


(* tail-recursive version of BC_ev *)

(* these constants are chosen at random: they must all be distinct *)
val COMPILE_EV = ``Val 0``
val COMPILE_EVL = ``Val 1``
val COMPILE_AP = ``Val 2``
val CONTINUE = ``Sym "NIL"``
val COMPILE_LAM1 = ``Val 3``
val COMPILE_LAM2 = ``Val 4``
val COMPILE_IF2 = ``Val 5``
val COMPILE_IF3 = ``Val 6``
val COMPILE_SET_RET = ``Val 7``
val COMPILE_CALL = ``Val 8``
val COMPILE_TAILOPT = ``Val 9``
val COMPILE_MACRO = ``Val 10``
val COMPILE_OR2 = ``Val 11``

(* variable assignments:
     x0 -- temp
     x1 -- task
     x2 -- term(s) to be compiled
     x3 -- a2sexp a
     x4 -- boo2sexp ret
     x5 -- bc_state
*)

val bool2sexp_def = Define `
  (bool2sexp T = Sym "T") /\
  (bool2sexp F = Sym "NIL")`;

val code_ptr_REPLACE_CODE = prove(
  ``code_ptr (REPLACE_CODE code x y) = code_ptr code``,
  Cases_on `code` \\ Cases_on `p`
  \\ ASM_SIMP_TAC std_ss [REPLACE_CODE_def,code_ptr_def]);

val code_length_APPEND = prove(
  ``!xs ys. code_length (xs ++ ys) = code_length xs + code_length ys``,
  Induct \\ ASM_SIMP_TAC std_ss [code_length_def,APPEND,ADD_ASSOC]);

val SND_WRITE_CODE = prove(
  ``!xs code. code_ptr (WRITE_CODE code xs) = code_ptr code + code_length xs``,
  Induct \\ Cases_on `code` \\ Cases_on `p`
  \\ FULL_SIMP_TAC std_ss [WRITE_CODE_def,code_length_def,ADD_ASSOC,code_ptr_def]);

val WRITE_CODE_NIL = prove(
  ``!code. WRITE_CODE code [] = code``,
  Cases \\ Cases_on `p` \\ SIMP_TAC std_ss [WRITE_CODE_def]);

val REPLACE_CODE_WRITE_CODE = prove(
  ``!xs code n y.
      n < code_ptr code ==>
      (REPLACE_CODE (WRITE_CODE code xs) n y =
       WRITE_CODE (REPLACE_CODE code n y) xs)``,
  Induct \\ SIMP_TAC std_ss [code_length_def,WRITE_CODE_NIL]
  \\ REPEAT STRIP_TAC \\ Cases_on `code` \\ Cases_on `p`
  \\ FULL_SIMP_TAC std_ss [WRITE_CODE_def,code_ptr_def]
  \\ Q.PAT_X_ASSUM `!code. bbb` (MP_TAC o Q.SPECL
       [`BC_CODE ((r =+ SOME h) q,r + bc_length h)`,`n`,`y`])
  \\ FULL_SIMP_TAC std_ss [code_ptr_def,AC ADD_COMM ADD_ASSOC]
  \\ `n < r + bc_length h` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [WRITE_CODE_def,REPLACE_CODE_def]
  \\ `~(r = n)` by DECIDE_TAC \\ METIS_TAC [UPDATE_COMMUTES]);

val code_ptr_WRITE_CODE_lemma = prove(
  ``!code x. code_ptr (WRITE_CODE code [x]) = code_ptr code + bc_length x``,
  Cases \\ Cases \\ Cases_on `p` \\ SIMP_TAC std_ss [WRITE_CODE_def,code_ptr_def]);

val code_ptr_WRITE_CODE = prove(
  ``!xs code. code_ptr (WRITE_CODE code xs) = code_ptr code + code_length xs``,
  Induct \\ SIMP_TAC std_ss [WRITE_CODE_NIL,code_length_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `code` \\ Cases_on `p`
  \\ FULL_SIMP_TAC std_ss [WRITE_CODE_def,code_ptr_def]
  \\ FULL_SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC]);

val WRITE_CODE_APPEND = prove(
  ``!xs ys s. WRITE_CODE (WRITE_CODE s xs) ys = WRITE_CODE s (xs ++ ys)``,
  Induct \\ Cases_on `s` \\ Cases_on `p`
  \\ FULL_SIMP_TAC std_ss [FORALL_PROD,WRITE_CODE_def,APPEND]);

val REPLACE_CODE_RW = prove(
  ``(bc_length x = bc_length y) ==>
    (REPLACE_CODE (WRITE_CODE code (x_code ++ ([x] ++ y_code)))
                  (code_ptr code + code_length x_code) y =
     WRITE_CODE code (x_code ++ ([y] ++ y_code)))``,
  SIMP_TAC std_ss [GSYM WRITE_CODE_APPEND]
  \\ MP_TAC (Q.SPECL [`y_code`,`WRITE_CODE (WRITE_CODE code x_code) [x]`,`code_ptr code + code_length x_code`,`y`] REPLACE_CODE_WRITE_CODE)
  \\ FULL_SIMP_TAC std_ss [code_ptr_WRITE_CODE]
  \\ `0 < code_length [x]` by
        (Cases_on `x` \\ EVAL_TAC \\ Cases_on `l` \\ EVAL_TAC)
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ Cases_on `WRITE_CODE code x_code`
  \\ Cases_on `p` \\ Cases_on `code` \\ Cases_on `p`
  \\ FULL_SIMP_TAC std_ss [WRITE_CODE_def,REPLACE_CODE_def,code_ptr_def]
  \\ sg `r' + code_length x_code = r`
  \\ FULL_SIMP_TAC std_ss [UPDATE_EQ]
  \\ `code_ptr (WRITE_CODE (BC_CODE (q',r')) x_code) = code_ptr (BC_CODE (q,r))` by METIS_TAC []
  \\ FULL_SIMP_TAC std_ss [code_ptr_def,code_ptr_WRITE_CODE]);

val code_mem_WRITE_CODE_LESS = store_thm("code_mem_WRITE_CODE_LESS",
  ``!xs code i.
      i < code_ptr code ==>
      (code_mem (WRITE_CODE code xs) i = code_mem code i)``,
  Induct
  THEN1 (Cases_on `code` \\ Cases_on `p` \\ SIMP_TAC std_ss [WRITE_CODE_def])
  \\ ONCE_REWRITE_TAC [GSYM (EVAL ``[x] ++ ys``)]
  \\ SIMP_TAC std_ss [GSYM WRITE_CODE_APPEND]
  \\ REPEAT STRIP_TAC
  \\ `i < code_ptr (WRITE_CODE code [h])` by
   (Cases_on `code` \\ Cases_on `p`
    \\ FULL_SIMP_TAC std_ss [WRITE_CODE_def,code_ptr_def] \\ DECIDE_TAC)
  \\ RES_TAC \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `code` \\ Cases_on `p`
  \\ FULL_SIMP_TAC std_ss [WRITE_CODE_def,code_mem_def,APPLY_UPDATE_THM,code_ptr_def]
  \\ `~(i = r)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []);

val code_mem_WRITE_CODE = prove(
  ``!xs y ys code.
      (code_mem (WRITE_CODE code (xs ++ y::ys)) (code_length xs + code_ptr code) = SOME y)``,
  Induct \\ REPEAT STRIP_TAC THEN1
   (SIMP_TAC std_ss [APPEND,code_length_def]
    \\ ONCE_REWRITE_TAC [GSYM (EVAL ``[x] ++ ys``)]
    \\ SIMP_TAC std_ss [GSYM WRITE_CODE_APPEND]
    \\ `code_ptr code < code_ptr (WRITE_CODE code [y])` by
     (Cases_on `code` \\ Cases_on `p`
      \\ FULL_SIMP_TAC std_ss [WRITE_CODE_def,code_ptr_def]
      \\ Cases_on `y` \\ EVAL_TAC \\ Cases_on `l` \\ EVAL_TAC)
    \\ IMP_RES_TAC code_mem_WRITE_CODE_LESS
    \\ ASM_SIMP_TAC std_ss []
    \\ Cases_on `code` \\ Cases_on `p`
    \\ SIMP_TAC std_ss [WRITE_CODE_def,code_mem_def,code_ptr_def,APPLY_UPDATE_THM])
  \\ SIMP_TAC std_ss [APPEND]
  \\ ONCE_REWRITE_TAC [GSYM (EVAL ``[x] ++ ys``)]
  \\ SIMP_TAC std_ss [Once (GSYM WRITE_CODE_APPEND)]
  \\ `(code_length ([h] ++ xs) + code_ptr code) =
      (code_length xs + code_ptr (WRITE_CODE code [h]))` by
    (SIMP_TAC std_ss [code_ptr_WRITE_CODE,code_length_APPEND,AC ADD_COMM ADD_ASSOC])
  \\ ASM_SIMP_TAC std_ss []);

val code_mem_WRITE_CODE_IMP = prove(
  ``!xs y ys code l.
      ((code_length xs + code_ptr code) = l) ==>
      (code_mem (WRITE_CODE code (xs ++ y::ys)) l = SOME y)``,
  SIMP_TAC std_ss [code_mem_WRITE_CODE]);

val a2sexp_aux_def = Define `
  (a2sexp_aux ssTEMP = Val 0) /\
  (a2sexp_aux (ssVAR v) = Sym v)`;

val a2sexp_def = Define `
  a2sexp a = list2sexp (MAP a2sexp_aux a)`;

val bc_inv_def = Define `
  bc_inv bc = (bc.instr_length = bc_length) /\ BC_CODE_OK bc`;

val term2sexp_guard_lemma = prove(
  ``~isVal (term2sexp (App fc xs)) /\
    ~isDot (CAR (term2sexp (App fc xs))) /\
    ~isQuote (term2sexp (App fc xs)) /\
    ~(CAR (term2sexp (App fc xs)) = Sym "IF") /\
    ~(CAR (term2sexp (App fc xs)) = Sym "OR") /\
    ~(isSym (term2sexp (App fc xs))) /\
    ~(term2sexp (App fc xs) = Sym "NIL") /\
    ~(term2sexp (App fc xs) = Sym "T") /\
    ~(CAR (term2sexp (App fc xs)) = Val 1)``,
  REVERSE (Cases_on `fc`) THEN1
   (SIMP_TAC std_ss [term2sexp_def,func2sexp_def]
    \\ Cases_on `MEM s reserved_names` \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [MEM,reserved_names_def,macro_names_def,APPEND]
    \\ ASM_SIMP_TAC (srw_ss()) [APPEND,list2sexp_def,CAR_def,CDR_def] \\ EVAL_TAC
    \\ ASM_SIMP_TAC (srw_ss()) [APPEND,list2sexp_def,CAR_def,CDR_def] \\ EVAL_TAC)
  \\ REPEAT (Cases_on `l`) \\ EVAL_TAC);

val iLENGTH_thm = prove(
  ``!fs bc. bc_inv bc ==> (iLENGTH bc.instr_length = code_length) /\
                          (iLENGTH bc_length = code_length)``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [FUN_EQ_THM] \\ Induct
  \\ ASM_SIMP_TAC std_ss [iLENGTH_def,code_length_def]
  \\ FULL_SIMP_TAC std_ss [bc_inv_def]);

val sexp2list_list2sexp = prove(
  ``!xs. sexp2list (list2sexp xs) = xs``,
  Induct \\ ASM_SIMP_TAC std_ss [sexp2list_def,list2sexp_def]);

val s2sexp_retract = prove(
  ``!a. Dot (Val 0) (a2sexp a) = a2sexp (ssTEMP::a)``,
  SIMP_TAC std_ss [a2sexp_def,a2sexp_aux_def,MAP,list2sexp_def]);

val const_tree_def = Define `
  const_tree bc = Dot (Val (LENGTH bc.consts)) (list2btree bc.consts)`;

val flat_alist_def = Define `
  (flat_alist [] = []) /\
  (flat_alist ((x,(y,z))::xs) = Sym x::(Dot (Val y) (Val z))::flat_alist xs)`;

val bc_state_tree_def = Define `
  bc_state_tree bc = Dot (Sym "NIL") (list2sexp (flat_alist bc.compiled))`;

val bc_inv_ADD_CONST = prove(
  ``(bc_inv (BC_ADD_CONST bc s) = bc_inv bc) /\
    ((BC_ADD_CONST bc s).compiled = bc.compiled) /\
    (bc_state_tree (BC_ADD_CONST bc s) = bc_state_tree bc)``,
  SIMP_TAC (srw_ss()) [bc_inv_def,BC_ADD_CONST_def,BC_CODE_OK_def,bc_state_tree_def]);

(*

(* add const *)

val (_,mc_add_const_def,mc_add_const_pre_def) = compile "x64" ``
  mc_add_const (x2,x3,x5,xs) =
    let xs = x2::xs in
    let xs = x3::xs in
    let xs = x5::xs in
    let x5 = CAR x5 in
    let x0 = CAR x5 in
    let x0 = LISP_ADD x0 (Val 1) in
    let x3 = x2 in
    let x2 = CDR x5 in
    let x1 = x2 in
    let (x0,x1,x2,x3,xs) = mc_btree_insert (x0,x1,x2,x3,xs) in
    let x0 = Dot x0 x3 in
    let x5 = x0 in
    let x3 = HD xs in
    let xs = TL xs in
    let x3 = CDR x3 in
    let x5 = Dot x5 x3 in
    let x3 = HD xs in
    let xs = TL xs in
    let x2 = HD xs in
    let xs = TL xs in
    let x0 = Sym "NIL" in
    let x1 = Sym "NIL" in
      (x0,x1,x2,x3,x5,xs)``;

val mc_add_const_thm = prove(
  ``mc_add_const_pre (x2,x3,bc_state_tree bc,xs) /\
    (mc_add_const (x2,x3,bc_state_tree bc,xs) =
      (Sym "NIL",Sym "NIL",x2,x3,bc_state_tree (BC_ADD_CONST bc x2),xs))``,
  SIMP_TAC std_ss [const_tree_def,mc_add_const_def,mc_add_const_pre_def,LET_DEF,CAR_def,
     mc_btree_insert_thm,CDR_def,LISP_ADD_def,getVal_def,btree_insert_tr_thm,
     btree_insert_thm,TL,HD,bc_state_tree_def,SExp_11,isVal_def,isDot_def,NOT_CONS_NIL]
  \\ REPEAT STRIP_TAC \\ SIMP_TAC (srw_ss()) [BC_ADD_CONST_def]);

*)


(* popn and pops *)

val (_,mc_pops_def,mc_pops_pre_def) = compile "x64" ``
  mc_pops (x0,code) =
    if x0 = Val 0 then (x0,code) else
      let code = WRITE_CODE code [iPOPS (getVal x0)] in
        (x0,code)``;

val (_,mc_popn_def,mc_popn_pre_def) = compile "x64" ``
  mc_popn (x0,code) =
    if x0 = Val 0 then let x0 = Sym "NIL" in (x0,code) else
      let x0 = LISP_SUB x0 (Val 1) in
      let (x0,code) = mc_pops (x0,code) in
      let code = WRITE_CODE code [iPOP] in
      let x0 = Sym "NIL" in
        (x0,code)``;

val mc_pops_thm = prove(
  ``mc_pops_pre (Val n,code) /\
    (mc_pops (Val n,code) = (Val n, WRITE_CODE code (gen_pops n)))``,
  SRW_TAC [] [mc_pops_def,mc_pops_pre_def,gen_pops_def,LET_DEF,
    WRITE_CODE_NIL,getVal_def,isVal_def]);

val mc_popn_thm = prove(
  ``mc_popn_pre (Val n,code) /\
    (mc_popn (Val n,code) = (Sym "NIL", WRITE_CODE code (gen_popn n)))``,
  SRW_TAC [] [mc_popn_def,mc_popn_pre_def,LET_DEF,LISP_SUB_def,WRITE_CODE_APPEND,
    WRITE_CODE_NIL,getVal_def,isVal_def,mc_pops_thm,gen_popn_def]);


(* drop *)

val (_,mc_drop_def,mc_drop_pre_def) = compile "x64" ``
  mc_drop (x0,x3) =
    if ~(isDot x3) then let x0 = Sym "NIL" in (x0,x3) else
      if x0 = Val 0 then let x0 = Sym "NIL" in (x0,x3) else
        let x0 = LISP_SUB x0 (Val 1) in
        let x3 = SAFE_CDR x3 in
          mc_drop (x0,x3)``;

val mc_drop_thm = prove(
  ``!a n.
      mc_drop_pre (Val n,a2sexp a) /\
      (mc_drop (Val n,a2sexp a) = (Sym "NIL", a2sexp (DROP n a)))``,
  Induct \\ ONCE_REWRITE_TAC [mc_drop_def,mc_drop_pre_def]
  \\ SIMP_TAC std_ss [DROP_def,a2sexp_def,MAP,list2sexp_def,SExp_distinct,SExp_11,isDot_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `n = 0` \\ ASM_SIMP_TAC std_ss [LET_DEF]
  \\ FULL_SIMP_TAC std_ss [MAP,a2sexp_def,list2sexp_def,CDR_def,LISP_SUB_def,
       getVal_def,isVal_def,SAFE_CDR_def]);


(* length *)

val (_,mc_length_def,mc_length_pre_def) = compile "x64" ``
  mc_length (x0,x1) =
    if ~(isDot x0) then (x0,x1) else
      let x0 = CDR x0 in
      let x1 = LISP_ADD x1 (Val 1) in
        mc_length (x0,x1)``

val mc_length_thm = prove(
  ``!xs n.
       mc_length_pre (list2sexp xs,Val n) /\
       (mc_length (list2sexp xs,Val n) = (Sym "NIL",Val (n + LENGTH xs)))``,
  Induct \\ ASM_SIMP_TAC std_ss [list2sexp_def,Once mc_length_def,isDot_def,
    LENGTH,CDR_def,LISP_ADD_def,getVal_def,Once mc_length_pre_def,LET_DEF,isVal_def]
  \\ SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM,ADD1]);


(* append the reverse onto alist *)

val (_,mc_rev_append_def,mc_rev_append_pre_def) = compile "x64" ``
  mc_rev_append (x0,x1,x3) =
    if ~(isDot x0) then (let x1 = x0 in (x0,x1,x3)) else
      let x1 = x0 in
      let x0 = x3 in
      let x3 = CAR x1 in
      let x3 = Dot x3 x0 in
      let x0 = CDR x1 in
        mc_rev_append (x0,x1,x3)``;

val mc_rev_append_thm = prove(
  ``!xs ys y. (mc_rev_append_pre (list2sexp (MAP Sym xs),y,a2sexp ys)) /\
              (mc_rev_append (list2sexp (MAP Sym xs),y,a2sexp ys) =
                (Sym "NIL",Sym "NIL",a2sexp (MAP ssVAR (REVERSE xs) ++ ys)))``,
  Induct \\ SIMP_TAC std_ss [MAP,list2sexp_def,REVERSE_DEF,APPEND,LET_DEF,
      Once mc_rev_append_def,Once mc_rev_append_pre_def,isDot_def,
      CAR_def,CDR_def,SAFE_CAR_def,SAFE_CDR_def]
  \\ ASM_SIMP_TAC std_ss [MAP_APPEND,GSYM APPEND_ASSOC,MAP,LET_DEF]
  \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (ASSUME_TAC o Q.SPECL [`[ssVAR h] ++ ys`,`Dot (Sym h) (list2sexp (MAP Sym xs))`])
  \\ FULL_SIMP_TAC std_ss [a2sexp_def,MAP,a2sexp_aux_def,list2sexp_def,APPEND]);


(* loops which write some instructions n times *)

val (i,mc_stores_def,mc_stores_pre_def) = compile "x64" ``
  mc_stores (x0,x1,code) =
    if x1 = Val 0 then (x0,x1,code) else
      let x1 = LISP_SUB x1 (Val 1) in
      let code = WRITE_CODE code [iSTORE (getVal x0)] in
        mc_stores (x0,x1,code)``

val (_,mc_cons_list_def,mc_cons_list_pre_def) = compile "x64" ``
  mc_cons_list (x1,code) =
    if x1 = Val 0 then (x1,code) else
      let x1 = LISP_SUB x1 (Val 1) in
      let code = WRITE_CODE code [iDATA opCONS] in
        mc_cons_list (x1,code)``

val (_,mc_push_nils_def,mc_push_nils_pre_def) = compile "x64" ``
  mc_push_nils (x0,x1,x3,code) =
    if x1 = Val 0 then (x0,x1,x3,code) else
      let x1 = LISP_SUB x1 (Val 1) in
      let x0 = x3 in
      let x3 = Val 0 in
      let x3 = Dot x3 x0 in
      let x0 = Sym "NIL" in
      let code = WRITE_CODE code [iCONST_SYM (getSym x0)] in
        mc_push_nils (x0,x1,x3,code)``

val mc_stores_thm = prove(
  ``!n code. mc_stores_pre (Val k,Val n,code) /\
             (mc_stores (Val k,Val n,code) =
               (Val k, Val 0, WRITE_CODE code (n_times n (iSTORE k))))``,
  Induct \\ ASM_SIMP_TAC (srw_ss()) [Once mc_stores_def,
    Once mc_stores_pre_def,n_times_def,LET_DEF,isVal_def,
    WRITE_CODE_NIL,LISP_SUB_def,getVal_def,WRITE_CODE_APPEND]);

val mc_cons_list_thm = prove(
  ``!n code. mc_cons_list_pre (Val n,code) /\
             (mc_cons_list (Val n,code) =
               (Val 0, WRITE_CODE code (n_times n (iDATA opCONS))))``,
  Induct \\ ASM_SIMP_TAC (srw_ss()) [Once mc_cons_list_def,
    Once mc_cons_list_pre_def,n_times_def,LET_DEF,isVal_def,
    WRITE_CODE_NIL,LISP_SUB_def,getVal_def,WRITE_CODE_APPEND]);

val n_times_LEMMA = prove(
  ``!n x ys. n_times n x ++ x::ys = x::(n_times n x ++ ys)``,
  Induct \\ ASM_SIMP_TAC std_ss [n_times_def,APPEND]);

val mc_push_nils_thm = prove(
  ``!n a code.
      mc_push_nils_pre (Sym "NIL",Val n,a2sexp a,code) /\
      (mc_push_nils (Sym "NIL",Val n,a2sexp a,code) =
               (Sym "NIL", Val 0, a2sexp (n_times n ssTEMP ++ a),
                WRITE_CODE code (n_times n (iCONST_SYM "NIL"))))``,
  Induct \\ ASM_SIMP_TAC (srw_ss()) [Once mc_push_nils_def,getSym_def,
    Once mc_push_nils_pre_def,n_times_def,LET_DEF,isSym_def,isVal_def,
    WRITE_CODE_NIL,LISP_SUB_def,getVal_def,WRITE_CODE_APPEND]
  \\ REPEAT STRIP_TAC \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `ssTEMP::a`)
  \\ FULL_SIMP_TAC std_ss [a2sexp_def,a2sexp_aux_def,MAP,list2sexp_def,
       WRITE_CODE_APPEND,APPEND,n_times_LEMMA]);


(* write primitive instruction *)

val (_,mc_primitive_def,mc_primitivie_pre_def) = compile "x64" ``
  mc_primitive (x0,x1,code) =
    if x1 = Val 2 then
      if x0 = Sym "CONS" then
        let code = WRITE_CODE code [iDATA opCONS] in (x0,x1,code) else
      if x0 = Sym "EQUAL" then
        let code = WRITE_CODE code [iDATA opEQUAL] in (x0,x1,code) else
      if x0 = Sym "<" then
        let code = WRITE_CODE code [iDATA opLESS] in (x0,x1,code) else
      if x0 = Sym "SYMBOL-<" then
        let code = WRITE_CODE code [iDATA opSYMBOL_LESS] in (x0,x1,code) else
      if x0 = Sym "+" then
        let code = WRITE_CODE code [iDATA opADD] in (x0,x1,code) else
      if x0 = Sym "-" then
        let code = WRITE_CODE code [iDATA opSUB] in (x0,x1,code) else
      (* incorrect arity *)
        let code = WRITE_CODE code [iFAIL] in (x0,x1,code) else
    if x1 = Val 1 then
      if x0 = Sym "CONSP" then
        let code = WRITE_CODE code [iDATA opCONSP] in (x0,x1,code) else
      if x0 = Sym "NATP" then
        let code = WRITE_CODE code [iDATA opNATP] in (x0,x1,code) else
      if x0 = Sym "SYMBOLP" then
        let code = WRITE_CODE code [iDATA opSYMBOLP] in (x0,x1,code) else
      if x0 = Sym "CAR" then
        let code = WRITE_CODE code [iDATA opCAR] in (x0,x1,code) else
      if x0 = Sym "CDR" then
        let code = WRITE_CODE code [iDATA opCDR] in (x0,x1,code) else
      (* incorrect arity *)
        let code = WRITE_CODE code [iFAIL] in (x0,x1,code) else
    (* incorrect arity *)
      let code = WRITE_CODE code [iFAIL] in (x0,x1,code)``;


(* check function name *)

val BC_is_reserved_name_def = Define `
  BC_is_reserved_name exp =
    if MEM exp (MAP Sym macro_names) then Val 0 else
    if MEM exp (MAP Sym reserved_names) then exp else Sym "NIL"`;

val (_,mc_is_reserved_name_def,mc_is_reserved_name_pre_def) = compile "x64" ``
  mc_is_reserved_name (x0) =
    if x0 = Sym "LET" then let x0 = Val 0 in x0 else
    if x0 = Sym "LET*" then let x0 = Val 0 in x0 else
    if x0 = Sym "COND" then let x0 = Val 0 in x0 else
    if x0 = Sym "AND" then let x0 = Val 0 in x0 else
    if x0 = Sym "FIRST" then let x0 = Val 0 in x0 else
    if x0 = Sym "SECOND" then let x0 = Val 0 in x0 else
    if x0 = Sym "THIRD" then let x0 = Val 0 in x0 else
    if x0 = Sym "FOURTH" then let x0 = Val 0 in x0 else
    if x0 = Sym "FIFTH" then let x0 = Val 0 in x0 else
    if x0 = Sym "LIST" then let x0 = Val 0 in x0 else
    if x0 = Sym "DEFUN" then let x0 = Val 0 in x0 else
    if x0 = Sym "QUOTE" then x0 else
    if x0 = Sym "IF" then x0 else
    if x0 = Sym "OR" then x0 else
    if x0 = Sym "DEFINE" then x0 else
    if x0 = Sym "PRINT" then x0 else
    if x0 = Sym "ERROR" then x0 else
    if x0 = Sym "FUNCALL" then x0 else
    if x0 = Sym "CAR" then x0 else
    if x0 = Sym "CDR" then x0 else
    if x0 = Sym "SYMBOLP" then x0 else
    if x0 = Sym "NATP" then x0 else
    if x0 = Sym "CONSP" then x0 else
    if x0 = Sym "+" then x0 else
    if x0 = Sym "-" then x0 else
    if x0 = Sym "SYMBOL-<" then x0 else
    if x0 = Sym "<" then x0 else
    if x0 = Sym "EQUAL" then x0 else
    if x0 = Sym "CONS" then x0 else
      let x0 = Sym "NIL" in x0``

val mc_is_reserved_name_thm = prove(
  ``!exp. mc_is_reserved_name exp = BC_is_reserved_name exp``,
  SIMP_TAC std_ss [mc_is_reserved_name_def,BC_is_reserved_name_def,
    macro_names_def,MEM,MAP,reserved_names_def,APPEND,LET_DEF]
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss []);

val NOT_isFun_IMP_guard = prove(
  ``~isFun fc ==>
    ~(BC_is_reserved_name (CAR (term2sexp (App fc xs))) = Sym "NIL") /\
    ~(BC_is_reserved_name (HD (func2sexp fc)) = Sym "NIL") /\
    ~(BC_is_reserved_name (CAR (term2sexp (App fc xs))) = Val 0)``,
  Cases_on `fc` \\ FULL_SIMP_TAC std_ss [isFun_def]
  \\ REPEAT (Cases_on `l`) \\ EVAL_TAC);

val BC_is_reserved_name_Fun = prove(
  ``BC_is_reserved_name (CAR (term2sexp (App (Fun fc) xs))) = Sym "NIL"``,
  SIMP_TAC std_ss [term2sexp_def,BC_is_reserved_name_def,func2sexp_def]
  \\ Cases_on `MEM fc reserved_names` \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [APPEND,list2sexp_def,CAR_def]
  \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [MEM,reserved_names_def,macro_names_def,APPEND]
  \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [MEM,reserved_names_def,APPEND]);


(* strip application *)

val (_,mc_strip_app_def,mc_strip_app_pre_def) = compile "x64" ``
  mc_strip_app (x0:SExp,x1:SExp) =
    let x0 = CAR x1 in
      if ~(isVal x0) then (x0,x1) else
        let x1 = CDR x1 in (x0,x1)``

val mc_strip_app_thm = prove(
  ``mc_strip_app_pre (x,term2sexp (App (Fun fc) xs)) /\
    (mc_strip_app (x,term2sexp (App (Fun fc) xs)) =
     (CAR (term2sexp (App (Fun fc) xs)),
      list2sexp (Sym fc :: MAP term2sexp xs)))``,
  SIMP_TAC std_ss [term2sexp_def,func2sexp_def]
  \\ Cases_on `MEM fc reserved_names` \\ POP_ASSUM MP_TAC
  \\ ASM_SIMP_TAC std_ss [mc_strip_app_def,mc_strip_app_pre_def,LET_DEF]
  \\ ASM_SIMP_TAC std_ss [] \\ EVAL_TAC \\ ASM_SIMP_TAC std_ss []
  \\ EVAL_TAC \\ ASM_SIMP_TAC std_ss []);


(* return code *)

val (_,mc_return_code_def,mc_return_code_pre_def) = compile "x64" ``
  mc_return_code (x0:SExp,x1:SExp,x3,x4,code) =
    if x4 (* ret *) = Sym "NIL" then
      let x0 = Sym "NIL" in
      let x1 = Sym "NIL" in
        (x0,x1,x3,x4,code)
    else
      let x1 = Val 0 in
      let x0 = x3 in
      let (x0,x1) = mc_length (x0,x1) in
      let x0 = x1 in
      let x1 = Val 1 in
      let x0 = LISP_SUB x0 x1 in
      let (x0,code) = mc_pops (x0,code) in
      let code = WRITE_CODE code [iRETURN] in
      let x0 = Sym "NIL" in
      let x1 = Sym "NIL" in
        (x0,x1,x3,x4,code)``

val mc_return_code_thm = prove(
  ``mc_return_code_pre (x0,x1,a2sexp a,bool2sexp ret,code) /\
    (mc_return_code (x0,x1,a2sexp a,bool2sexp ret,code) =
      (Sym "NIL",Sym "NIL",a2sexp a,bool2sexp ret,WRITE_CODE code (BC_return_code ret a)))``,
  Cases_on `ret` \\ FULL_SIMP_TAC std_ss [mc_return_code_def,LET_DEF,bool2sexp_def,
                      mc_return_code_pre_def]
  \\ FULL_SIMP_TAC (srw_ss()) [a2sexp_def,mc_length_thm,LISP_SUB_def,isVal_def,
       getVal_def,mc_pops_thm,WRITE_CODE_APPEND,BC_return_code_def,WRITE_CODE_NIL]);


(* lookup variable location *)

val (_,mc_alist_lookup_def,mc_alist_lookup_pre_def) = compile "x64" ``
  mc_alist_lookup (x0,x1,x2,x3) =
    if ~(isDot x3) then let x1 = Sym "NIL" in (x0,x1,x2,x3) else
      let x0 = CAR x3 in
        if x0 = x2 then (x0,x1,x2,x3) else
          let x1 = LISP_ADD x1 (Val 1) in
          let x3 = CDR x3 in
            mc_alist_lookup (x0,x1,x2,x3)``

val mc_alist_lookup_thm = prove(
  ``!a v n k x0.
      (var_lookup k v a = SOME n) ==>
      ?y0 y1 y3.
        mc_alist_lookup_pre (x0,Val k,Sym v,a2sexp a) /\
        (mc_alist_lookup (x0,Val k,Sym v,a2sexp a) = (y0,Val n,y1,y3))``,
  Induct \\ SIMP_TAC std_ss [var_lookup_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `h` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ ONCE_REWRITE_TAC [mc_alist_lookup_def,mc_alist_lookup_pre_def]
  \\ FULL_SIMP_TAC (srw_ss()) [a2sexp_def,a2sexp_aux_def,MAP,list2sexp_def,
        CAR_def,CDR_def,LISP_ADD_def,getVal_def,isDot_def,LET_DEF,isVal_def,
        markerTheory.Abbrev_def] \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `s = v` \\ FULL_SIMP_TAC std_ss [getVal_def,SExp_11]);

val mc_alist_lookup_NONE = prove(
  ``!a v n k x0.
      (var_lookup k v a = NONE) ==>
      ?y0 y1 y3.
        mc_alist_lookup_pre (x0,Val k,Sym v,a2sexp a) /\
        (mc_alist_lookup (x0,Val k,Sym v,a2sexp a) = (y0,Sym "NIL",y1,y3))``,
  Induct \\ SIMP_TAC std_ss [var_lookup_def] \\ REPEAT STRIP_TAC
  \\ REPEAT (Cases_on `h` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ ONCE_REWRITE_TAC [mc_alist_lookup_def,mc_alist_lookup_pre_def]
  \\ FULL_SIMP_TAC (srw_ss()) [a2sexp_def,a2sexp_aux_def,MAP,list2sexp_def,
        CAR_def,CDR_def,LISP_ADD_def,getVal_def,isDot_def,LET_DEF,isVal_def,
        markerTheory.Abbrev_def]
  \\ Cases_on `s = v` \\ FULL_SIMP_TAC std_ss [getVal_def,SExp_11]);


(* lookup function location *)

val (_,mc_fun_lookup_def,mc_fun_lookup_pre_def) = compile "x64" ``
  mc_fun_lookup (x0,x1,x2) =
    if ~(isDot x1) then (x0,x1,x2) else
      let x0 = CAR x1 in
      let x1 = CDR x1 in
        if x0 = x2 then
          let x1 = CAR x1 in
            (x0,x1,x2)
        else
          let x1 = CDR x1 in
            mc_fun_lookup (x0,x1,x2)``

val lookup_result_def = Define `
  (lookup_result NONE = Sym "NIL") /\
  (lookup_result (SOME (x,y)) = Dot (Val x) (Val y))`;

val mc_fun_lookup_thm = prove(
  ``!xs y fc. ?y0 y1.
      mc_fun_lookup_pre (y,list2sexp (flat_alist xs),Sym fc) /\
      (mc_fun_lookup (y,list2sexp (flat_alist xs),Sym fc) =
         (y0,lookup_result (FUN_LOOKUP xs fc),y1))``,
  Induct \\ SIMP_TAC std_ss [flat_alist_def,list2sexp_def]
  \\ ONCE_REWRITE_TAC [mc_fun_lookup_def,mc_fun_lookup_pre_def]
  \\ SIMP_TAC std_ss [isDot_def,FUN_LOOKUP_def,lookup_result_def]
  \\ Cases_on `h` \\ Cases_on `r` \\ SIMP_TAC (srw_ss()) [isDot_def,FUN_LOOKUP_def,
       lookup_result_def,LET_DEF,flat_alist_def,list2sexp_def,CAR_def,CDR_def,
       markerTheory.Abbrev_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `q = fc` \\ FULL_SIMP_TAC std_ss [lookup_result_def]);

val mc_fun_lookup_NONE_bc = prove(
  ``bc_inv bc /\ (FUN_LOOKUP bc.compiled fc = NONE) ==>
    ?y0 y1.
      mc_fun_lookup_pre (x0,CDR (bc_state_tree bc),Sym fc) /\
      (mc_fun_lookup (x0,CDR (bc_state_tree bc),Sym fc) = (y0,Sym "NIL",y1))``,
  FULL_SIMP_TAC std_ss [bc_inv_def,bc_state_tree_def,CDR_def]
  \\ METIS_TAC [mc_fun_lookup_thm,lookup_result_def]);

val mc_fun_lookup_SOME_bc = prove(
  ``bc_inv bc /\ (FUN_LOOKUP bc.compiled fc = SOME (n,m)) ==>
    ?y0 y1.
      mc_fun_lookup_pre (x0,CDR (bc_state_tree bc),Sym fc) /\
      (mc_fun_lookup (x0,CDR (bc_state_tree bc),Sym fc) = (y0,Dot (Val n) (Val m),y1))``,
  FULL_SIMP_TAC std_ss [bc_inv_def,bc_state_tree_def,CDR_def]
  \\ METIS_TAC [mc_fun_lookup_thm,lookup_result_def]);


(* implementation of iCALL_SYM (and iJUMP_SYM) *)

val (mc_fun_lookup_full_spec,mc_fun_lookup_full_def,mc_fun_lookup_full_pre_def) = compile "x64" ``
  mc_fun_lookup_full (x0,x1:SExp,x2,x5,(xs:SExp list),io) =
    let x1 = CDR x5 in
    let x2 = x0 in
    let (x0,x1,x2) = mc_fun_lookup (x0,x1,x2) in
      if ~(isDot x1) then
        let x0 = x2 in
        let io = IO_WRITE io (sexp2string x0) in
        let io = IO_WRITE io "\n" in
        let x0 = no_such_function x0 in
          (x0,x1,x2,x5,xs,io)
      else
        let x2 = CAR x1 in
        let x1 = CDR x1 in
        let x0 = HD xs in
          if ~(x0 = x1) then
            let x0 = x2 in
            let io = IO_WRITE io (sexp2string x0) in
            let io = IO_WRITE io "\n" in
            let x0 = no_such_function x0 in
              (x0,x1,x2,x5,xs,io)
          else
            let x1 = x2 in
            let xs = TL xs in
            let x0 = HD xs in
            let xs = TL xs in
              (x0,x1,x2,x5,xs,io)``

val mc_fun_lookup_full_thm = prove(
  ``bc_inv bc /\ (FUN_LOOKUP bc.compiled fc = SOME (i,m)) ==>
    mc_fun_lookup_full_pre (Sym fc,x1,x2,bc_state_tree bc,Val m::x::xs,io) /\
    (mc_fun_lookup_full (Sym fc,x1,x2,bc_state_tree bc,Val m::x::xs,io) =
       (x,Val i,Val i,bc_state_tree bc,xs,io))``,
  SIMP_TAC std_ss [mc_fun_lookup_full_def,mc_fun_lookup_full_pre_def,LET_DEF,TL,HD]
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC mc_fun_lookup_SOME_bc
  \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `Sym fc`)
  \\ ASM_SIMP_TAC std_ss [NOT_CONS_NIL,isVal_def]
  \\ FULL_SIMP_TAC std_ss [bc_state_tree_def,isDot_def,CDR_def,markerTheory.Abbrev_def,CAR_def]);

(*
val th = mc_fun_lookup_full_spec
  |> Q.INST [`x0`|->`Sym fc`,`x5`|->`bc_state_tree bc`,`xs`|->`Val k::x::xs`]
  |> DISCH ``bc_inv bc /\ (FUN_LOOKUP bc.compiled fc = SOME (i,m))``
  |> SIMP_RULE std_ss [mc_fun_lookup_full_thm]
  |> UNDISCH
  |> CONV_RULE (REWRITE_CONV [UNDISCH mc_fun_lookup_full_thm])
  |> SIMP_RULE std_ss [LET_DEF]
  |> DISCH_ALL |> SIMP_RULE (std_ss++sep_cond_ss) [GSYM SPEC_MOVE_COND]
  |> (fn th => SPEC_COMPOSE_RULE [th,X64_LISP_JUMP_TO_CODE])
  |> SIMP_RULE std_ss [isVal_def,getVal_def,SEP_CLAUSES]
  (* followed by either jmp r2 or call r2 *)
*)


(* map car and map car_cdr *)

val (_,mc_map_car1_def,mc_map_car1_pre_def) = compile "x64" ``
  mc_map_car1 (x0,x1,x2,x3,xs) =
    if ~(isDot x0) then
      let x1 = Sym "NIL" in
      let x2 = Sym "NIL" in
        (x0,x1,x2,x3,xs)
    else
      let x1 = CAR x0 in
      let x2 = SAFE_CDR x1 in
      let x2 = SAFE_CAR x2 in
      let xs = x2::xs in
      let x1 = SAFE_CAR x1 in
      let xs = x1::xs in
      let x3 = LISP_ADD x3 (Val 1) in
      let x0 = CDR x0 in
        mc_map_car1 (x0,x1,x2,x3,xs)``

val (_,mc_map_car2_def,mc_map_car2_pre_def) = compile "x64" ``
  mc_map_car2 (x0,x1,x2,x3,xs) =
    if x3 = Val 0 then let x0 = Sym "NIL" in (x0,x1,x2,x3,xs) else
      let x0 = x1 in
      let x1 = HD xs in
      let x1 = Dot x1 x0 in
      let xs = TL xs in
      let x0 = x2 in
      let x2 = HD xs in
      let x2 = Dot x2 x0 in
      let xs = TL xs in
      let x3 = LISP_SUB x3 (Val 1) in
        mc_map_car2 (x0,x1,x2,x3,xs)``

val (_,mc_map_car_def,mc_map_car_pre_def) = compile "x64" ``
  mc_map_car (x0:SExp,x1:SExp,x2:SExp,x3:SExp,xs:SExp list) =
    let x3 = Val 0 in
    let (x0,x1,x2,x3,xs) = mc_map_car1 (x0,x1,x2,x3,xs) in
    let (x0,x1,x2,x3,xs) = mc_map_car2 (x0,x1,x2,x3,xs) in
      (x0,x1,x2,x3,xs)``

val map_car_flatten_def = Define `
  (map_car_flatten [] = []) /\
  (map_car_flatten (x::xs) = CAR x :: CAR (CDR x) :: map_car_flatten xs)`;

val map_car_flatten_APPEND = prove(
  ``!xs ys. map_car_flatten (xs ++ ys) = map_car_flatten xs ++ map_car_flatten ys``,
  Induct \\ FULL_SIMP_TAC std_ss [map_car_flatten_def,APPEND]);

val mc_map_car1_thm = prove(
  ``!x0 x1 x2 n xs. ?y.
      mc_map_car1_pre (x0,x1,x2,Val n,xs) /\
      (mc_map_car1 (x0,x1,x2,Val n,xs) =
        (y, Sym "NIL", Sym "NIL", Val (LENGTH (sexp2list x0) + n),
         map_car_flatten (REVERSE (sexp2list x0)) ++ xs))``,
  Induct \\ ONCE_REWRITE_TAC [mc_map_car1_def,mc_map_car1_pre_def]
  \\ ASM_SIMP_TAC std_ss [list2sexp_def,map_car_flatten_def,APPEND,LENGTH,
       LET_DEF,isDot_def,CAR_def,CDR_def,LISP_ADD_def,getVal_def,REVERSE_DEF,
       map_car_flatten_APPEND,GSYM APPEND_ASSOC,APPEND,isVal_def,SAFE_CAR_def,
       SAFE_CDR_def,sexp2list_def]
  \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM,ADD1]
  \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [`CAR x0`,`CAR (CDR x0)`,
       `n+1`,`CAR x0::CAR (CDR x0)::xs`])
  \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM,ADD1]);

val mc_map_car2_thm = prove(
  ``!ys ys1 ys2 x1 x2 xs.
      mc_map_car2_pre (x1,list2sexp ys1,list2sexp ys2,Val (LENGTH ys),map_car_flatten ys ++ xs) /\
      (mc_map_car2 (x1,list2sexp ys1,list2sexp ys2,Val (LENGTH ys),map_car_flatten ys ++ xs) =
        (Sym "NIL", list2sexp (MAP CAR (REVERSE ys) ++ ys1),
         list2sexp (MAP (CAR o CDR) (REVERSE ys) ++ ys2), Val 0, xs))``,
  Induct \\ SIMP_TAC std_ss [] \\ ONCE_REWRITE_TAC [mc_map_car2_def,mc_map_car2_pre_def]
  \\ SIMP_TAC std_ss [MAP,APPEND,REVERSE_DEF,map_car_flatten_def,LENGTH,LET_DEF,
       SExp_11,ADD1,TL,HD,LISP_SUB_def,getVal_def]
  \\ ASM_SIMP_TAC std_ss [GSYM list2sexp_def,MAP_APPEND,MAP,GSYM APPEND_ASSOC,
       APPEND,isVal_def,NOT_CONS_NIL]);

val mc_map_car_alternative_thm = prove(
  ``mc_map_car_pre (x0,x1,x2,x3,xs) /\
    (mc_map_car (x0,x1,x2,x3,xs) =
      (Sym "NIL", list2sexp (MAP CAR (sexp2list x0)),
       list2sexp (MAP (CAR o CDR) (sexp2list x0)), Val 0, xs))``,
  SIMP_TAC std_ss [mc_map_car_def,mc_map_car_pre_def,LET_DEF]
  \\ STRIP_ASSUME_TAC (Q.SPECL [`x0`,`x1`,`x2`,`0`,`xs`] mc_map_car1_thm)
  \\ ASM_SIMP_TAC std_ss [] \\ ONCE_REWRITE_TAC [GSYM LENGTH_REVERSE]
  \\ SIMP_TAC std_ss [GSYM list2sexp_def,mc_map_car2_thm,REVERSE_REVERSE,APPEND_NIL]);

val mc_map_car_thm = prove(
  ``mc_map_car_pre (list2sexp ys,x1,x2,x3,xs) /\
    (mc_map_car (list2sexp ys,x1,x2,x3,xs) =
      (Sym "NIL", list2sexp (MAP CAR ys), list2sexp (MAP (CAR o CDR) ys), Val 0, xs))``,
  ASM_SIMP_TAC std_ss [mc_map_car_alternative_thm,sexp2list_list2sexp]);


(* BC_expand_macro is a readable version of mc_expand_macro *)
val BC_expand_macro_def = Define `
  BC_expand_macro (temp:SExp,task,exp,a,ret,consts,xs) =
    let temp = exp in
    let exp = CAR exp in
      if exp = Sym "FIRST" then
        let exp = Dot (Sym "CAR") (CDR temp) in
          (Sym "NIL",task,exp,a,ret,consts,xs) else
      if exp = Sym "SECOND" then
        let exp = Dot (Sym "FIRST") (Dot (Dot (Sym "CDR") (CDR temp)) (Sym "NIL")) in
          (Sym "NIL",task,exp,a,ret,consts,xs) else
      if exp = Sym "THIRD" then
        let exp = Dot (Sym "SECOND") (Dot (Dot (Sym "CDR") (CDR temp)) (Sym "NIL")) in
          (Sym "NIL",task,exp,a,ret,consts,xs) else
      if exp = Sym "FOURTH" then
        let exp = Dot (Sym "THIRD") (Dot (Dot (Sym "CDR") (CDR temp)) (Sym "NIL")) in
          (Sym "NIL",task,exp,a,ret,consts,xs) else
      if exp = Sym "FIFTH" then
        let exp = Dot (Sym "FOURTH") (Dot (Dot (Sym "CDR") (CDR temp)) (Sym "NIL")) in
          (Sym "NIL",task,exp,a,ret,consts,xs) else
      if exp = Sym "LET" then
        let xs = a::ret::consts::xs in
        let (nil,vars,exps,zero,xs) = mc_map_car (CAR (CDR temp), exp, exp, exp, xs) in
        let lam = Dot (Sym "LAMBDA") (Dot vars (Dot (CAR (CDR (CDR temp))) (Sym "NIL"))) in
        let exp = Dot lam exps in
        let a = HD xs in
        let xs = TL xs in
        let ret = HD xs in
        let xs = TL xs in
        let consts = HD xs in
        let xs = TL xs in
        let task = Sym "NIL" in
          (Sym "NIL",task,exp,a,ret,consts,xs) else
      if exp = Sym "LET*" then
        let exp = CAR (CDR temp) in
          (if exp = Sym "NIL" then
             let exp = CAR (CDR (CDR temp)) in
               (Sym "NIL",task,exp,a,ret,consts,xs)
           else
             let rest = CDR exp in
             let head = CAR exp in
             let let_star = Dot (Sym "LET*") (Dot rest (Dot (CAR (CDR (CDR temp))) (Sym "NIL"))) in
             let assigns = Dot head (Sym "NIL") in
             let exp = Dot (Sym "LET") (Dot assigns (Dot (let_star) (Sym "NIL"))) in
               (Sym "NIL",task,exp,a,ret,consts,xs)) else
      if exp = Sym "COND" then
        let exp = CDR temp in
          (if exp = Sym "NIL" then
             let exp = Dot (Sym "QUOTE") (Dot (Sym "NIL") (Sym "NIL")) in
               (Sym "NIL",task,exp,a,ret,consts,xs)
           else
             let rest = CDR exp in
             let head = CAR exp in
             let rest = Dot (Sym "COND") rest in
             let exp = Dot (CAR (CDR head)) (Dot rest (Sym "NIL")) in
             let exp = Dot (Sym "IF") (Dot (CAR head) exp) in
               (Sym "NIL",task,exp,a,ret,consts,xs)) else
      if exp = Sym "AND" then
        let exp = CDR temp in
          (if exp = Sym "NIL" then
             let exp = Dot (Sym "QUOTE") (Dot (Sym "T") (Sym "NIL")) in
               (Sym "NIL",task,exp,a,ret,consts,xs)
           else
             let rest = CDR exp in
             let head = CAR exp in
               if isDot rest then
                 let exp = list2sexp
                   [Sym "IF"; head;
                    Dot (Sym "AND") rest;
                    list2sexp [Sym "QUOTE"; list2sexp []]] in
                   (Sym "NIL",task,exp,a,ret,consts,xs)
               else
                 let exp = head in
                   (Sym "NIL",task,exp,a,ret,consts,xs)) else
      if exp = Sym "LIST" then
        let exp = CDR temp in
          (if exp = Sym "NIL" then
             let exp = Dot (Sym "QUOTE") (Dot (Sym "NIL") (Sym "NIL")) in
               (Sym "NIL",task,exp,a,ret,consts,xs)
           else
             let rest = CDR exp in
             let head = CAR exp in
             let exp = list2sexp
               [Sym "CONS"; head;
                Dot (Sym "LIST") rest] in
               (Sym "NIL",task,exp,a,ret,consts,xs)) else
      if exp = Sym "DEFUN" then
        (let arg1 = list2sexp [Sym "QUOTE"; CAR (CDR temp)] in
         let arg2 = list2sexp [Sym "QUOTE"; CAR (CDR (CDR temp))] in
         let arg3 = list2sexp [Sym "QUOTE"; CAR (CDR (CDR (CDR temp)))] in
         let exp = list2sexp [Sym "DEFINE"; arg1; arg2; arg3] in
           (Sym "NIL",task,exp,a,ret,consts,xs)) else
      (Sym "NIL",task,temp,a,ret,consts,xs)`;

fun sexp_lets exp = let
  val expand = (cdr o concl o SIMP_CONV std_ss [list2sexp_def])
  fun flatten exp =
    if is_var exp then ([],exp) else
    if can (match_term ``Dot x y``) exp then let
      val (xs1,x1) = flatten (cdr (car exp))
      val (xs2,x2) = flatten (cdr exp)
      val v = genvar(``:SExp``)
      val new_exp = mk_comb(``Dot x0``,x2)
      in (xs2 @ xs1 @ [(``x0:SExp``,x1),(``x0:SExp``,new_exp),(v,``x0:SExp``)], v) end else
    if can (match_term ``CAR x``) exp then let
      val (xs1,x1) = flatten (cdr exp)
      val v = genvar(``:SExp``)
      val new_exp = mk_comb(``CAR``,x1)
      in (xs1 @ [(v,new_exp)], v) end else
    if can (match_term ``CDR x``) exp then let
      val (xs1,x1) = flatten (cdr exp)
      val v = genvar(``:SExp``)
      val new_exp = mk_comb(``CDR``,x1)
      in (xs1 @ [(v,new_exp)], v) end else
    if ((can (match_term ``Sym "NIL"``) exp) orelse
        (can (match_term ``Sym "T"``) exp)) then let
      val v = genvar(``:SExp``)
      in ([(v,exp)], v) end else
    if can (match_term ``Sym x``) exp then let
      val v = genvar(``:SExp``)
      in ([(``x0:SExp``,exp),(v,``x0:SExp``)], v) end else
    ([],exp)
  val regs = [``x2:SExp``,``x1:SExp``,``x3:SExp``,``x4:SExp``,``x5:SExp``,
              ``t1:SExp``,``t2:SExp``,``t3:SExp``,``t4:SExp``,``t5:SExp``,``x0:SExp``]
  fun all_clashes v tm =
    if is_var tm then [] else let
      val (xs,rest) = pairSyntax.dest_anylet tm
      val (lhs,rhs) = hd xs
      in if not (tmem v (free_vars rest)) then [] else
           free_vars lhs @ all_clashes v rest end
  fun select_reg lhs tm = let
    val vs = free_vars tm
    val possible_regs = if is_var tm then regs
                        else filter (fn x => tmem x vs) regs
    val clashes = all_clashes lhs tm
    in hd (filter (fn x => not (tmem x clashes)) regs) end
  fun build ([],v) = v
    | build ((lhs,rhs)::xs,v) =
        if tmem lhs regs then pairSyntax.mk_anylet([(lhs,rhs)],build (xs,v))
        else let
          val tm = build (xs,v)
          val reg_name = select_reg lhs tm
          val tm = subst [lhs |-> reg_name] tm
        in pairSyntax.mk_anylet([(reg_name,rhs)],tm) end
  fun clean_up tm =
    if is_var tm then tm else let
      val (xs,rest) = pairSyntax.dest_anylet tm
      val rest = clean_up rest
      val (lhs,rhs) = hd xs
      in if lhs ~~ rhs then rest else
           pairSyntax.mk_anylet([(lhs,rhs)],rest) end
  val full = clean_up o build o flatten o expand
  val result = full exp
  val thm = SIMP_CONV std_ss [LET_DEF] (mk_eq(result,expand exp))
  val _ = (cdr (concl thm) ~~ ``T``) orelse fail()
  in result end

val (_,mc_expand_macro_def,mc_expand_macro_pre_def) = compile "x64" ``
  mc_expand_macro (x0:SExp,x1:SExp,x2:SExp,x3:SExp,x4:SExp,x5:SExp,xs:SExp list) =
    let x0 = SAFE_CAR x2 in
      if x0 = Sym "FIRST" then
        let x2 = SAFE_CDR x2 in
        let x0 = Sym "CAR" in
        let x0 = Dot x0 x2 in
        let x2 = x0 in
        let x0 = Sym "NIL" in
          (x0,x1,x2,x3,x4,x5,xs) else
      if x0 = Sym "SECOND" then
        let x2 = SAFE_CDR x2 in
        let x0 = Sym "CDR" in
        let x0 = Dot x0 x2 in
        let x2 = Sym "NIL" in
        let x0 = Dot x0 x2 in
        let x2 = x0 in
        let x0 = Sym "FIRST" in
        let x0 = Dot x0 x2 in
        let x2 = x0 in
        let x0 = Sym "NIL" in
          (x0,x1,x2,x3,x4,x5,xs) else
      if x0 = Sym "THIRD" then
        let x2 = SAFE_CDR x2 in
        let x0 = Sym "CDR" in
        let x0 = Dot x0 x2 in
        let x2 = Sym "NIL" in
        let x0 = Dot x0 x2 in
        let x2 = x0 in
        let x0 = Sym "SECOND" in
        let x0 = Dot x0 x2 in
        let x2 = x0 in
        let x0 = Sym "NIL" in
          (x0,x1,x2,x3,x4,x5,xs) else
      if x0 = Sym "FOURTH" then
        let x2 = SAFE_CDR x2 in
        let x0 = Sym "CDR" in
        let x0 = Dot x0 x2 in
        let x2 = Sym "NIL" in
        let x0 = Dot x0 x2 in
        let x2 = x0 in
        let x0 = Sym "THIRD" in
        let x0 = Dot x0 x2 in
        let x2 = x0 in
        let x0 = Sym "NIL" in
          (x0,x1,x2,x3,x4,x5,xs) else
      if x0 = Sym "FIFTH" then
        let x2 = SAFE_CDR x2 in
        let x0 = Sym "CDR" in
        let x0 = Dot x0 x2 in
        let x2 = Sym "NIL" in
        let x0 = Dot x0 x2 in
        let x2 = x0 in
        let x0 = Sym "FOURTH" in
        let x0 = Dot x0 x2 in
        let x2 = x0 in
        let x0 = Sym "NIL" in
          (x0,x1,x2,x3,x4,x5,xs) else
      if x0 = Sym "LET" then
        let xs = x5::xs in
        let xs = x4::xs in
        let xs = x3::xs in
        let x4 = x2 in
        let x1 = x0 in
        let x0 = SAFE_CDR x2 in
        let x0 = SAFE_CAR x0 in
        let x2 = x1 in
        let x3 = x1 in
        let (x0,x1,x2,x3,xs) = mc_map_car (x0, x1, x2, x3, xs) in
        let x4 = SAFE_CDR x4 in
        let x4 = SAFE_CDR x4 in
        let x4 = SAFE_CAR x4 in
        let x0 = Sym "NIL" in
        let x4 = Dot x4 x0 in
        let x1 = Dot x1 x4 in
        let x0 = Sym "LAMBDA" in
        let x0 = Dot x0 x1 in
        let x0 = Dot x0 x2 in
        let x2 = x0 in
        let x3 = HD xs in
        let xs = TL xs in
        let x4 = HD xs in
        let xs = TL xs in
        let x5 = HD xs in
        let xs = TL xs in
        let x1 = Sym "NIL" in
        let x0 = Sym "NIL" in
          (x0,x1,x2,x3,x4,x5,xs) else
      if x0 = Sym "LET*" then
        let x0 = SAFE_CDR x2 in
        let x0 = SAFE_CAR x0 in
          (if x0 = Sym "NIL" then
             let x2 = SAFE_CDR x2 in
             let x2 = SAFE_CDR x2 in
             let x2 = SAFE_CAR x2 in
             let x0 = Sym "NIL" in
               (x0,x1,x2,x3,x4,x5,xs)
           else
             let xs = x5::xs in
             let xs = x4::xs in
             let xs = x3::xs in
             let xs = x1::xs in
             let x5 = x0 in
             let x4 = x2 in
  (* sexp_lets list2sexp [Sym "LET"; list2sexp [SAFE_CAR x5]; list2sexp [Sym "LET*"; SAFE_CDR x5; SAFE_CAR (SAFE_CDR (SAFE_CDR x4))]] *)
  let x3 = Sym "NIL" in
  let x1 = Sym "NIL" in
  let x2 = SAFE_CDR x4 in
  let x2 = SAFE_CDR x2 in
  let x2 = SAFE_CAR x2 in
  let x0 = x2 in
  let x0 = Dot x0 x1 in
  let x1 = x0 in
  let x2 = SAFE_CDR x5 in
  let x0 = x2 in
  let x0 = Dot x0 x1 in
  let x1 = x0 in
  let x0 = Sym "LET*" in
  let x2 = x0 in
  let x0 = x2 in
  let x0 = Dot x0 x1 in
  let x2 = x0 in
  let x0 = x2 in
  let x0 = Dot x0 x3 in
  let x3 = x0 in
  let x1 = Sym "NIL" in
  let x2 = SAFE_CAR x5 in
  let x0 = x2 in
  let x0 = Dot x0 x1 in
  let x2 = x0 in
  let x0 = x2 in
  let x0 = Dot x0 x3 in
  let x1 = x0 in
  let x0 = Sym "LET" in
  let x2 = x0 in
  let x0 = x2 in
  let x0 = Dot x0 x1 in
  let x2 = x0 in
             let x1 = HD xs in
             let xs = TL xs in
             let x3 = HD xs in
             let xs = TL xs in
             let x4 = HD xs in
             let xs = TL xs in
             let x5 = HD xs in
             let xs = TL xs in
             let x0 = Sym "NIL" in
               (x0,x1,x2,x3,x4,x5,xs)) else
      if x0 = Sym "COND" then
        let x0 = SAFE_CDR x2 in
          (if x0 = Sym "NIL" then
             let x0 = Sym "NIL" in
             let x2 = Sym "NIL" in
             let x2 = Dot x2 x0 in
             let x0 = Sym "QUOTE" in
             let x0 = Dot x0 x2 in
             let x2 = x0 in
             let x0 = Sym "NIL" in
               (x0,x1,x2,x3,x4,x5,xs)
           else
             let xs = x5::xs in
             let xs = x4::xs in
             let xs = x3::xs in
             let xs = x1::xs in
             let x5 = x0 in
  (* sexp_lets list2sexp [Sym "IF"; CAR (CAR x5); CAR (CDR (CAR x5)); Dot (Sym "COND") (CDR x5)] *)
  let x3 = Sym "NIL" in
  let x1 = SAFE_CDR x5 in
  let x0 = Sym "COND" in
  let x2 = x0 in
  let x0 = x2 in
  let x0 = Dot x0 x1 in
  let x2 = x0 in
  let x0 = x2 in
  let x0 = Dot x0 x3 in
  let x1 = x0 in
  let x2 = SAFE_CAR x5 in
  let x2 = SAFE_CDR x2 in
  let x2 = SAFE_CAR x2 in
  let x0 = x2 in
  let x0 = Dot x0 x1 in
  let x1 = x0 in
  let x2 = SAFE_CAR x5 in
  let x2 = SAFE_CAR x2 in
  let x0 = x2 in
  let x0 = Dot x0 x1 in
  let x1 = x0 in
  let x0 = Sym "IF" in
  let x2 = x0 in
  let x0 = x2 in
  let x0 = Dot x0 x1 in
  let x2 = x0 in
             let x1 = HD xs in
             let xs = TL xs in
             let x3 = HD xs in
             let xs = TL xs in
             let x4 = HD xs in
             let xs = TL xs in
             let x5 = HD xs in
             let xs = TL xs in
             let x0 = Sym "NIL" in
               (x0,x1,x2,x3,x4,x5,xs)) else
      if x0 = Sym "AND" then
        let x0 = SAFE_CDR x2 in
          (if x0 = Sym "NIL" then
             let x2 = Sym "T" in
             let x0 = Sym "NIL" in
             let x2 = Dot x2 x0 in
             let x0 = Sym "QUOTE" in
             let x0 = Dot x0 x2 in
             let x2 = x0 in
             let x0 = Sym "NIL" in
               (x0,x1,x2,x3,x4,x5,xs)
           else
             let xs = x5::xs in
             let xs = x4::xs in
             let xs = x3::xs in
             let xs = x1::xs in
             let x5 = x0 in
             let x4 = SAFE_CDR x5 in
               if isDot x4 then
  (* sexp_lets list2sexp [Sym "IF"; (SAFE_CAR x5); Dot (Sym "AND") (SAFE_CDR x5); list2sexp [Sym "QUOTE"; list2sexp []]] *)
  let x3 = Sym "NIL" in
  let x1 = Sym "NIL" in
  let x2 = Sym "NIL" in
  let x0 = x2 in
  let x0 = Dot x0 x1 in
  let x1 = x0 in
  let x0 = Sym "QUOTE" in
  let x2 = x0 in
  let x0 = x2 in
  let x0 = Dot x0 x1 in
  let x2 = x0 in
  let x0 = x2 in
  let x0 = Dot x0 x3 in
  let x3 = x0 in
  let x1 = SAFE_CDR x5 in
  let x0 = Sym "AND" in
  let x2 = x0 in
  let x0 = x2 in
  let x0 = Dot x0 x1 in
  let x2 = x0 in
  let x0 = x2 in
  let x0 = Dot x0 x3 in
  let x1 = x0 in
  let x2 = SAFE_CAR x5 in
  let x0 = x2 in
  let x0 = Dot x0 x1 in
  let x1 = x0 in
  let x0 = Sym "IF" in
  let x2 = x0 in
  let x0 = x2 in
  let x0 = Dot x0 x1 in
  let x2 = x0 in
                 let x1 = HD xs in
                 let xs = TL xs in
                 let x3 = HD xs in
                 let xs = TL xs in
                 let x4 = HD xs in
                 let xs = TL xs in
                 let x5 = HD xs in
                 let xs = TL xs in
                 let x0 = Sym "NIL" in
                   (x0,x1,x2,x3,x4,x5,xs)
               else
                 let x2 = SAFE_CAR x0 in
                 let x1 = HD xs in
                 let xs = TL xs in
                 let x3 = HD xs in
                 let xs = TL xs in
                 let x4 = HD xs in
                 let xs = TL xs in
                 let x5 = HD xs in
                 let xs = TL xs in
                 let x0 = Sym "NIL" in
                   (x0,x1,x2,x3,x4,x5,xs)) else
      if x0 = Sym "LIST" then
        let x0 = SAFE_CDR x2 in
          (if x0 = Sym "NIL" then
             let x0 = Sym "NIL" in
             let x2 = Sym "NIL" in
             let x2 = Dot x2 x0 in
             let x0 = Sym "QUOTE" in
             let x0 = Dot x0 x2 in
             let x2 = x0 in
             let x0 = Sym "NIL" in
               (x0,x1,x2,x3,x4,x5,xs)
           else
             let xs = x5::xs in
             let xs = x4::xs in
             let xs = x3::xs in
             let xs = x1::xs in
             let x5 = x0 in
             (* let x2 = list2sexp [Sym "CONS"; (SAFE_CAR x5); Dot (Sym "LIST") (SAFE_CDR x5)] in *)
  let x3 = Sym "NIL" in
  let x1 = SAFE_CDR x5 in
  let x0 = Sym "LIST" in
  let x2 = x0 in
  let x2 = Dot x2 x1 in
  let x1 = x2 in
  let x1 = Dot x1 x3 in
  let x2 = SAFE_CAR x5 in
  let x0 = x2 in
  let x0 = Dot x0 x1 in
  let x1 = x0 in
  let x0 = Sym "CONS" in
  let x2 = x0 in
  let x2 = Dot x2 x1 in
             let x1 = HD xs in
             let xs = TL xs in
             let x3 = HD xs in
             let xs = TL xs in
             let x4 = HD xs in
             let xs = TL xs in
             let x5 = HD xs in
             let xs = TL xs in
             let x0 = Sym "NIL" in
               (x0,x1,x2,x3,x4,x5,xs)) else
      if x0 = Sym "DEFUN" then
       (let xs = x5::xs in
        let xs = x4::xs in
        let xs = x3::xs in
        let xs = x1::xs in
        let x5 = x2 in
  let x3 = Sym "NIL" in
  let x2 = Sym "NIL" in
  let x0 = SAFE_CDR x5 in
  let x0 = SAFE_CDR x0 in
  let x0 = SAFE_CDR x0 in
  let x0 = SAFE_CAR x0 in
  let x0 = Dot x0 x2 in
  let x1 = x0 in
  let x0 = Sym "QUOTE" in
  let x2 = x0 in
  let x0 = x2 in
  let x0 = Dot x0 x1 in
  let x2 = x0 in
  let x0 = x2 in
  let x0 = Dot x0 x3 in
  let x3 = x0 in
  let x2 = Sym "NIL" in
  let x0 = SAFE_CDR x5 in
  let x0 = SAFE_CDR x0 in
  let x0 = SAFE_CAR x0 in
  let x0 = Dot x0 x2 in
  let x1 = x0 in
  let x0 = Sym "QUOTE" in
  let x2 = x0 in
  let x0 = x2 in
  let x0 = Dot x0 x1 in
  let x2 = x0 in
  let x0 = x2 in
  let x0 = Dot x0 x3 in
  let x3 = x0 in
  let x2 = Sym "NIL" in
  let x0 = SAFE_CDR x5 in
  let x0 = SAFE_CAR x0 in
  let x0 = Dot x0 x2 in
  let x1 = x0 in
  let x0 = Sym "QUOTE" in
  let x2 = x0 in
  let x0 = x2 in
  let x0 = Dot x0 x1 in
  let x2 = x0 in
  let x0 = x2 in
  let x0 = Dot x0 x3 in
  let x1 = x0 in
  let x0 = Sym "DEFINE" in
  let x2 = x0 in
  let x0 = x2 in
  let x0 = Dot x0 x1 in
  let x2 = x0 in
        let x1 = HD xs in
        let xs = TL xs in
        let x3 = HD xs in
        let xs = TL xs in
        let x4 = HD xs in
        let xs = TL xs in
        let x5 = HD xs in
        let xs = TL xs in
        let x0 = Sym "NIL" in
          (x0,x1,x2,x3,x4,x5,xs)) else
      let x0 = Sym "NIL" in
        (x0,x1,x2,x3,x4,x5,xs)``;

val mc_expand_macro_thm = prove(
  ``(mc_expand_macro = BC_expand_macro) /\ !x. mc_expand_macro_pre x``,
  STRIP_TAC THEN1
   (SIMP_TAC std_ss [FUN_EQ_THM,FORALL_PROD,BC_expand_macro_def,
      mc_expand_macro_def,LET_DEF,HD,TL,list2sexp_def,SAFE_CAR_def,SAFE_CDR_def]
    \\ SRW_TAC [] [])
  \\ FULL_SIMP_TAC std_ss [FORALL_PROD,mc_expand_macro_pre_def,
       LET_DEF,HD,TL,NOT_CONS_NIL,mc_map_car_alternative_thm]);

(* BC_aux_ev is a readable version of mc_aux_ev *)
val BC_aux_ev_def = Define `
  BC_aux_ev (temp:SExp,task,exp,a,ret,consts:SExp,xs,xs1,code) =
      if isSym exp then
       (let (t1,loc,t2,t3) = mc_alist_lookup (task,Val 0,exp,a) in
          if loc = Sym "NIL" then
            let code = WRITE_CODE code [iFAIL] in
            let task = ^CONTINUE in
            let a = Dot (Val 0) a in
            let (t1,t2,a,ret,code) = mc_return_code (task,task,a,ret,code) in
              (Sym "NIL",task,exp,a,ret,consts,xs,xs1,code)
          else
            let code = WRITE_CODE code [iLOAD (getVal loc)] in
            let task = ^CONTINUE in
            let a = Dot (Val 0) a in
            let (t1,t2,a,ret,code) = mc_return_code (task,task,a,ret,code) in
              (Sym "NIL",task,exp,a,ret,consts,xs,xs1,code))
      else if CAR exp = Sym "IF" then
        let temp = ret in
        let xs = CAR exp::Dot a (CDR (CDR exp))::temp::xs in (* put if on todo list *)
        let exp = CAR (CDR exp) in
        let ret = Sym "NIL" in
          (Sym "NIL",task,exp,a,ret,consts,xs,xs1,code)
      else if CAR exp = Sym "OR" then
        if ~(isDot (CDR exp)) then
          let exp = Sym "NIL" in
          let code = WRITE_CODE code [iCONST_SYM (getSym exp)] in
          let task = ^CONTINUE in
          let a = Dot (Val 0) a in
          let (t1,t2,a,ret,code) = mc_return_code (task,task,a,ret,code) in
            (Sym "NIL",task,exp,a,ret,consts,xs,xs1,code)
        else
          let temp = ret in
          let xs = CAR exp::Dot a (CDR (CDR exp))::temp::xs in (* put if on todo list *)
          let exp = CAR (CDR exp) in
          let ret = Sym "NIL" in
            (Sym "NIL",task,exp,a,ret,consts,xs,xs1,code)
      else if isQuote exp then
        let exp = CAR (CDR exp) in
          if isVal exp then
            let code = WRITE_CODE code [iCONST_NUM (getVal exp)] in
            let task = ^CONTINUE in
            let a = Dot (Val 0) a in
            let (t1,t2,a,ret,code) = mc_return_code (task,task,a,ret,code) in
              (Sym "NIL",task,exp,a,ret,consts,xs,xs1,code)
          else if isSym exp then
            let code = WRITE_CODE code [iCONST_SYM (getSym exp)] in
            let task = ^CONTINUE in
            let a = Dot (Val 0) a in
            let (t1,t2,a,ret,code) = mc_return_code (task,task,a,ret,code) in
              (Sym "NIL",task,exp,a,ret,consts,xs,xs1,code)
          else
            let (task,xs1) = (Val (LENGTH xs1),xs1 ++ [exp]) in
            let code = WRITE_CODE code [iCONST_NUM (getVal task)] in
            let code = WRITE_CODE code [iCONST_LOOKUP] in
            let task = ^CONTINUE in
            let a = Dot (Val 0) a in
            let (t1,t2,a,ret,code) = mc_return_code (task,task,a,ret,code) in
              (Sym "NIL",task,exp,a,ret,consts,xs,xs1,code)
      else if isDot (CAR exp) then (* lambda *)
        let temp = ret in
        let xs = ^COMPILE_LAM1::exp::temp::a::xs in
        let exp = CDR exp in
        let ret = Sym "NIL" in
        let task = ^COMPILE_EVL in
          (Sym "NIL",task,exp,a,ret,consts,xs,xs1,code)
      else if isVal exp then
        let exp = Dot (Sym "QUOTE") (Dot exp (Sym "NIL")) in
          (Sym "NIL",task,exp,a,ret,consts,xs,xs1,code)
      else (* function application or macro *)
        let temp = exp in
        let exp = CAR exp in
        let exp = BC_is_reserved_name exp in
          if exp = Sym "NIL" then (* user-defined function *)
            (let (t1,temp) = mc_strip_app (ret,temp) in
               if ret = Sym "NIL" then
                 let xs = ^COMPILE_CALL::temp::xs in
                 let ret = Sym "NIL" in
                 let exp = CDR temp in
                 let task = ^COMPILE_EVL in
                   (Sym "NIL",task,exp,a,ret,consts,xs,xs1,code)
               else (* tail-optimisation *)
                 let (t1,al) = mc_length (a,Val 0) in
                 let (t1,xl) = mc_length (CDR temp,Val 0) in
                 let padding = LISP_SUB xl al in
                 let (t1,t2,a,code) = mc_push_nils (Sym "NIL",padding,a,code) in
                 let xs = ^COMPILE_TAILOPT::Dot al xl::^COMPILE_SET_RET::ret::^COMPILE_CALL::temp::xs in
                 let ret = Sym "NIL" in
                 let exp = CDR temp in
                 let task = ^COMPILE_EVL in
                   (Sym "NIL",task,exp,a,ret,consts,xs,xs1,code))
          else
            (if exp = Val 0 then (* macro *)
               let exp = temp in
               let task = ^COMPILE_MACRO in
                 (Sym "NIL",task,exp,a,ret,consts,xs,xs1,code)
             else
               (* built-in function *)
               let exp = temp in
               let temp = CDR temp in
               let (t1,temp) = mc_length (temp,Val 0) in
               let temp = Dot (CAR exp) temp in
               let xs = ^COMPILE_SET_RET::ret::^COMPILE_AP::temp::xs in
               let ret = Sym "NIL" in
               let exp = CDR exp in
               let task = ^COMPILE_EVL in
                 (Sym "NIL",task,exp,a,ret,consts,xs,xs1,code))`;

(* val mc_aux_ev_def = Define *)
val (thm,mc_aux_ev_def,mc_aux_ev_pre_def) = compile "x64" ``
  mc_aux_ev (x0:SExp,x1,x2,x3,x4,x5:SExp,xs,xs1,code) =
      if isSym x2 then
       (let x0 = x1 in
        let x1 = Val 0 in
        let xs = x2::xs in
        let xs = x3::xs in
        let (x0,x1,x2,x3) = mc_alist_lookup (x0,x1,x2,x3) in
        let x3 = HD xs in
        let xs = TL xs in
        let x2 = HD xs in
        let xs = TL xs in
        let x0 = Val 0 in
        let x0 = Dot x0 x3 in
        let x3 = x0 in
          if x1 = Sym "NIL" then
            let code = WRITE_CODE code [iFAIL] in
            let x0 = ^CONTINUE in
            let x1 = ^CONTINUE in
            let (x0,x1,x3,x4,code) = mc_return_code (x0,x1,x3,x4,code) in
            let x1 = ^CONTINUE in
            let x0 = Sym "NIL" in
              (x0,x1,x2,x3,x4,x5,xs,xs1,code)
          else
            let x0 = x1 in
            let code = WRITE_CODE code [iLOAD (getVal x0)] in
            let x0 = ^CONTINUE in
            let x1 = ^CONTINUE in
            let (x0,x1,x3,x4,code) = mc_return_code (x0,x1,x3,x4,code) in
            let x1 = ^CONTINUE in
            let x0 = Sym "NIL" in
              (x0,x1,x2,x3,x4,x5,xs,xs1,code))
(*
      else let x0 = SAFE_CAR x2 in if x0 = Val 1 then
       (let x2 = SAFE_CDR x2 in
        let x0 = x1 in
        let x1 = Val 0 in
        let xs = x2::xs in
        let xs = x3::xs in
        let (x0,x1,x2,x3) = mc_alist_lookup (x0,x1,x2,x3) in
        let x3 = HD xs in
        let xs = TL xs in
        let x2 = HD xs in
        let xs = TL xs in
        let x0 = Val 0 in
        let x0 = Dot x0 x3 in
        let x3 = x0 in
          if x1 = Sym "NIL" then
            let code = WRITE_CODE code [iFAIL] in
            let x0 = ^CONTINUE in
            let x1 = ^CONTINUE in
            let (x0,x1,x3,x4,code) = mc_return_code (x0,x1,x3,x4,code) in
            let x1 = ^CONTINUE in
            let x0 = Sym "NIL" in
              (x0,x1,x2,x3,x4,x5,xs,xs1,code)
          else
            let x0 = x1 in
            let code = WRITE_CODE code [iLOAD (getVal x0)] in
            let x0 = ^CONTINUE in
            let x1 = ^CONTINUE in
            let (x0,x1,x3,x4,code) = mc_return_code (x0,x1,x3,x4,code) in
            let x1 = ^CONTINUE in
            let x0 = Sym "NIL" in
              (x0,x1,x2,x3,x4,x5,xs,xs1,code))
*)
      else let x0 = SAFE_CAR x2 in if x0 = Sym "IF" then (* put if on todo list *)
        let xs = x4::xs in
        let x4 = SAFE_CDR x2 in
        let x4 = SAFE_CDR x4 in
        let x0 = x3 in
        let x0 = Dot x0 x4 in
        let xs = x0::xs in
        let x0 = SAFE_CAR x2 in
        let xs = x0::xs in
        let x2 = SAFE_CDR x2 in
        let x2 = SAFE_CAR x2 in
        let x4 = Sym "NIL" in
        let x0 = Sym "NIL" in
          (x0,x1,x2,x3,x4,x5,xs,xs1,code)
      else let x0 = SAFE_CAR x2 in if x0 = Sym "OR" then
        let x0 = SAFE_CDR x2 in if ~(isDot x0) then
          let x0 = Sym "NIL" in
          let code = WRITE_CODE code [iCONST_SYM (getSym x0)] in
          let x0 = x3 in
          let x3 = Val 0 in
          let x3 = Dot x3 x0 in
          let x0 = ^CONTINUE in
          let x1 = ^CONTINUE in
          let (x0,x1,x3,x4,code) = mc_return_code (x0,x1,x3,x4,code) in
          let x0 = Sym "NIL" in
          let x1 = ^CONTINUE in
          let x2 = Sym "NIL" in
            (x0,x1,x2,x3,x4,x5,xs,xs1,code)
        else
          let xs = x4::xs in
          let x0 = SAFE_CDR x2 in
          let x0 = SAFE_CDR x0 in
          let x4 = x3 in
          let x4 = Dot x4 x0 in
          let xs = x4::xs in
          let x0 = SAFE_CAR x2 in
          let xs = x0::xs in
          let x2 = SAFE_CDR x2 in
          let x2 = SAFE_CAR x2 in
          let x0 = Sym "NIL" in
          let x4 = Sym "NIL" in
            (x0,x1,x2,x3,x4,x5,xs,xs1,code)
      else let x0 = x2 in let x0 = LISP_TEST (isQuote x0) in if x0 = Sym "T" then
        let x2 = SAFE_CDR x2 in
        let x2 = SAFE_CAR x2 in
          if isVal x2 then
            let x0 = x2 in
            let code = WRITE_CODE code [iCONST_NUM (getVal x0)] in
            let x0 = Val 0 in
            let x0 = Dot x0 x3 in
            let x3 = x0 in
            let x0 = ^CONTINUE in
            let x1 = ^CONTINUE in
            let (x0,x1,x3,x4,code) = mc_return_code (x0,x1,x3,x4,code) in
            let x1 = ^CONTINUE in
            let x0 = Sym "NIL" in
              (x0,x1,x2,x3,x4,x5,xs,xs1,code)
          else if isSym x2 then
            let x0 = x2 in
            let code = WRITE_CODE code [iCONST_SYM (getSym x0)] in
            let x0 = Val 0 in
            let x0 = Dot x0 x3 in
            let x3 = x0 in
            let x0 = ^CONTINUE in
            let x1 = ^CONTINUE in
            let (x0,x1,x3,x4,code) = mc_return_code (x0,x1,x3,x4,code) in
            let x1 = ^CONTINUE in
            let x0 = Sym "NIL" in
              (x0,x1,x2,x3,x4,x5,xs,xs1,code)
          else
            let x0 = x2 in
            let (x0,xs1) = (Val (LENGTH xs1),xs1 ++ [x0]) in
            let code = WRITE_CODE code [iCONST_NUM (getVal x0)] in
            let code = WRITE_CODE code [iCONST_LOOKUP] in
            let x0 = Val 0 in
            let x0 = Dot x0 x3 in
            let x3 = x0 in
            let x0 = ^CONTINUE in
            let x1 = ^CONTINUE in
            let (x0,x1,x3,x4,code) = mc_return_code (x0,x1,x3,x4,code) in
            let x1 = ^CONTINUE in
            let x0 = Sym "NIL" in
              (x0,x1,x2,x3,x4,x5,xs,xs1,code)
      else let x0 = SAFE_CAR x2 in if isDot x0 then (* lambda *)
        let x0 = x4 in
        let xs = x3::xs in
        let xs = x0::xs in
        let xs = x2::xs in
        let x0 = ^COMPILE_LAM1 in
        let xs = x0::xs in
        let x2 = SAFE_CDR x2 in
        let x4 = Sym "NIL" in
        let x1 = ^COMPILE_EVL in
        let x0 = Sym "NIL" in
          (x0,x1,x2,x3,x4,x5,xs,xs1,code)
      else if isVal x2 then
        let x0 = Sym "NIL" in
        let x2 = Dot x2 x0 in
        let x0 = Sym "QUOTE" in
        let x0 = Dot x0 x2 in
        let x2 = x0 in
        let x0 = Sym "NIL" in
          (x0,x1,x2,x3,x4,x5,xs,xs1,code)
      else (* function application or macro *)
        let x0 = SAFE_CAR x2 in
        let x0 = mc_is_reserved_name x0 in
          if x0 = Sym "NIL" then (* user-defined function *)
            (let x0 = x4 in
             let x1 = x2 in
             let (x0,x1) = mc_strip_app (x0,x1) in
             let x0 = x1 in
               if x4 = Sym "NIL" then
                 let xs = x0::xs in
                 let x0 = ^COMPILE_CALL in
                 let xs = x0::xs in
                 let x4 = Sym "NIL" in
                 let x2 = SAFE_CDR x1 in
                 let x1 = ^COMPILE_EVL in
                 let x0 = Sym "NIL" in
                   (x0,x1,x2,x3,x4,x5,xs,xs1,code)
               else (* tail-optimisation *)
                 let xs = x0::xs in
                 let x1 = ^COMPILE_CALL in
                 let xs = x1::xs in
                 let xs = x4::xs in
                 let x1 = ^COMPILE_SET_RET in
                 let xs = x1::xs in
                 let xs = x0::xs in
                 let x0 = x3 in
                 let x1 = Val 0 in
                 let (x0,x1) = mc_length (x0,x1) in
                 let x0 = HD xs in
                 let xs = x1::xs in
                 let x0 = SAFE_CDR x0 in
                 let x1 = Val 0 in
                 let (x0,x1) = mc_length (x0,x1) in
                 let x4 = HD xs in
                 let xs = TL xs in
                 let x0 = HD xs in
                 let xs = TL xs in
                 let x4 = Dot x4 x1 in
                 let xs = x4::xs in
                 let x2 = x0 in
                 let x0 = ^COMPILE_TAILOPT in
                 let xs = x0::xs in
                 let x4 = SAFE_CAR x4 in
                 let x0 = x1 in
                 let x1 = x4 in
                 let x0 = LISP_SUB x0 x1 in
                 let x1 = x0 in
                 let x0 = Sym "NIL" in
                 let (x0,x1,x3,code) = mc_push_nils (x0,x1,x3,code) in
                 let x4 = Sym "NIL" in
                 let x2 = SAFE_CDR x2 in
                 let x1 = ^COMPILE_EVL in
                 let x0 = Sym "NIL" in
                   (x0,x1,x2,x3,x4,x5,xs,xs1,code))
          else
            (if x0 = Val 0 then (* macro *)
               let x0 = ^COMPILE_MACRO in
               let x1 = x0 in
               let x0 = Sym "NIL" in
                 (x0,x1,x2,x3,x4,x5,xs,xs1,code)
             else
               (* built-in function *)
               let x0 = SAFE_CDR x2 in
               let x1 = Val 0 in
               let (x0,x1) = mc_length (x0,x1) in
               let x0 = x1 in
               let x1 = SAFE_CAR x2 in
               let x1 = Dot x1 x0 in
               let xs = x1::xs in
               let x0 = ^COMPILE_AP in
               let xs = x0::xs in
               let xs = x4::xs in
               let x0 = ^COMPILE_SET_RET in
               let xs = x0::xs in
               let x4 = Sym "NIL" in
               let x2 = SAFE_CDR x2 in
               let x1 = ^COMPILE_EVL in
               let x0 = Sym "NIL" in
                 (x0,x1,x2,x3,x4,x5,xs,xs1,code))``;

val LISP_TEST_EQ_T = prove(``!b. (LISP_TEST b = Sym "T") = b``, Cases \\ EVAL_TAC);

val mc_aux_ev_thm = prove(
  ``mc_aux_ev = BC_aux_ev``,
  SIMP_TAC std_ss [FUN_EQ_THM,FORALL_PROD,BC_aux_ev_def,LISP_TEST_EQ_T,CAR_def,
    mc_aux_ev_def,LET_DEF,HD,TL,list2sexp_def,mc_is_reserved_name_thm,CDR_def,
    SAFE_CAR_def,SAFE_CDR_def] \\ SRW_TAC [] []);


val BC_aux_ap_def = Define `
  BC_aux_ap (temp:SExp,task:SExp,exp,a,ret,xs:SExp list,code) =
      if CAR exp = Sym "DEFINE" then
        let code = WRITE_CODE code [iCOMPILE] in
        let task = ^CONTINUE in
        let (temp,a) = mc_drop (CDR exp,a) in
        let a = Dot (Val 0) a in
        let (t1,t2,a,ret,code) = mc_return_code (task,task,a,ret,code) in
          (Sym "NIL", task,exp,a,ret,xs,code)
      else if CAR exp = Sym "PRINT" then
        let code = WRITE_CODE code [iCONST_SYM "NIL"] in
        let (t1,code) = mc_cons_list (CDR exp,code) in
        let code = WRITE_CODE code [iCONST_SYM "PRINT"] in
        let code = WRITE_CODE code [iLOAD 1] in
        let code = WRITE_CODE code [iDATA opCONS] in
        let code = WRITE_CODE code [iPRINT] in
        let code = WRITE_CODE code [iCONST_SYM "NIL"] in
        let code = WRITE_CODE code [iPOPS 2] in
        let task = ^CONTINUE in
        let (temp,a) = mc_drop (CDR exp,a) in
        let a = Dot (Val 0) a in
        let (t1,t2,a,ret,code) = mc_return_code (task,task,a,ret,code) in
          (Sym "NIL", task,exp,a,ret,xs,code)
      else if CAR exp = Sym "ERROR" then
        let code = WRITE_CODE code [iCONST_SYM "NIL"] in
        let (t1,code) = mc_cons_list (CDR exp,code) in
        let code = WRITE_CODE code [iCONST_SYM "ERROR"] in
        let code = WRITE_CODE code [iLOAD 1] in
        let code = WRITE_CODE code [iDATA opCONS] in
        let code = WRITE_CODE code [iPRINT] in
        let code = WRITE_CODE code [iFAIL] in
        let task = ^CONTINUE in
        let (temp,a) = mc_drop (CDR exp,a) in
        let a = Dot (Val 0) a in
        let (t1,t2,a,ret,code) = mc_return_code (task,task,a,ret,code) in
          (Sym "NIL", task,exp,a,ret,xs,code)
      else if CAR exp = Sym "FUNCALL" then
        let task = LISP_SUB (CDR exp) (Val 1) in
        let code = WRITE_CODE code [iCONST_NUM (getVal task)] in
        let code = WRITE_CODE code [iLOAD (getVal (CDR exp))] in
        let code = WRITE_CODE code [iCALL_SYM] in
        let code = WRITE_CODE code [iPOPS 1] in
        let task = ^CONTINUE in
        let (temp,a) = mc_drop (CDR exp,a) in
        let a = Dot (Val 0) a in
        let (t1,t2,a,ret,code) = mc_return_code (task,task,a,ret,code) in
          (Sym "NIL", task,exp,a,ret,xs,code)
      else (* primitive function *)
        let (task,temp,code) = mc_primitive (CAR exp,CDR exp,code) in
        let task = ^CONTINUE in
        let (temp,a) = mc_drop (CDR exp,a) in
        let a = Dot (Val 0) a in
        let (t1,t2,a,ret,code) = mc_return_code (task,task,a,ret,code) in
          (Sym "NIL", task,exp,a,ret,xs,code)`;

(* val mc_aux_ap_def = Define *)
val (_,mc_aux_ap_def,mc_aux_ap_pre_def) = compile "x64" ``
  mc_aux_ap (x0:SExp,x1:SExp,x2:SExp,x3:SExp,x4:SExp,xs:SExp list,code) =
    let x0 = SAFE_CAR x2 in
      if x0 = Sym "DEFINE" then
        let code = WRITE_CODE code [iCOMPILE] in
        let x1 = ^CONTINUE in
        let x0 = SAFE_CDR x2 in
        let (x0,x3) = mc_drop (x0,x3) in
        let x0 = Val 0 in
        let x0 = Dot x0 x3 in
        let x3 = x0 in
        let x0 = ^CONTINUE in
        let x1 = ^CONTINUE in
        let (x0,x1,x3,x4,code) = mc_return_code (x0,x1,x3,x4,code) in
        let x1 = ^CONTINUE in
        let x0 = Sym "NIL" in
          (x0,x1,x2,x3,x4,xs,code)
      else if x0 = Sym "PRINT" then
        let x0 = Sym "NIL" in
        let code = WRITE_CODE code [iCONST_SYM (getSym x0)] in
        let x0 = x1 in
        let x1 = SAFE_CDR x2 in
        let (x1,code) = mc_cons_list (x1,code) in
        let x0 = Sym "PRINT" in
        let code = WRITE_CODE code [iCONST_SYM (getSym x0)] in
        let x0 = Val 1 in
        let code = WRITE_CODE code [iLOAD (getVal x0)] in
        let code = WRITE_CODE code [iDATA opCONS] in
        let code = WRITE_CODE code [iPRINT] in
        let x0 = Sym "NIL" in
        let code = WRITE_CODE code [iCONST_SYM (getSym x0)] in
        let x0 = Val 1 in
        let x0 = LISP_ADD x0 (Val 1) in
        let code = WRITE_CODE code [iPOPS (getVal x0)] in
        let x0 = SAFE_CDR x2 in
        let (x0,x3) = mc_drop (x0,x3) in
        let x0 = Val 0 in
        let x0 = Dot x0 x3 in
        let x3 = x0 in
        let x0 = ^CONTINUE in
        let x1 = ^CONTINUE in
        let (x0,x1,x3,x4,code) = mc_return_code (x0,x1,x3,x4,code) in
        let x1 = ^CONTINUE in
        let x0 = Sym "NIL" in
          (x0,x1,x2,x3,x4,xs,code)
      else if x0 = Sym "ERROR" then
        let x0 = Sym "NIL" in
        let code = WRITE_CODE code [iCONST_SYM (getSym x0)] in
        let x0 = x1 in
        let x1 = SAFE_CDR x2 in
        let (x1,code) = mc_cons_list (x1,code) in
        let x0 = Sym "ERROR" in
        let code = WRITE_CODE code [iCONST_SYM (getSym x0)] in
        let x0 = Val 1 in
        let code = WRITE_CODE code [iLOAD (getVal x0)] in
        let code = WRITE_CODE code [iDATA opCONS] in
        let code = WRITE_CODE code [iPRINT] in
        let code = WRITE_CODE code [iFAIL] in
        let x0 = SAFE_CDR x2 in
        let (x0,x3) = mc_drop (x0,x3) in
        let x0 = Val 0 in
        let x0 = Dot x0 x3 in
        let x3 = x0 in
        let x0 = ^CONTINUE in
        let x1 = ^CONTINUE in
        let (x0,x1,x3,x4,code) = mc_return_code (x0,x1,x3,x4,code) in
        let x1 = ^CONTINUE in
        let x0 = Sym "NIL" in
          (x0,x1,x2,x3,x4,xs,code)
      else if x0 = Sym "FUNCALL" then
        let x0 = SAFE_CDR x2 in
        let x1 = Val 1 in
        let x0 = LISP_SUB x0 x1 in
        let code = WRITE_CODE code [iCONST_NUM (getVal x0)] in
        let x0 = SAFE_CDR x2 in
        let code = WRITE_CODE code [iLOAD (getVal x0)] in
        let code = WRITE_CODE code [iCALL_SYM] in
        let x0 = Val 1 in
        let code = WRITE_CODE code [iPOPS (getVal x0)] in
        let x0 = SAFE_CDR x2 in
        let (x0,x3) = mc_drop (x0,x3) in
        let x0 = Val 0 in
        let x0 = Dot x0 x3 in
        let x3 = x0 in
        let x0 = ^CONTINUE in
        let x1 = ^CONTINUE in
        let (x0,x1,x3,x4,code) = mc_return_code (x0,x1,x3,x4,code) in
        let x1 = ^CONTINUE in
        let x0 = Sym "NIL" in
          (x0,x1,x2,x3,x4,xs,code)
      else (* primitive function *)
        let x0 = SAFE_CAR x2 in
        let x1 = SAFE_CDR x2 in
        let (x0,x1,code) = mc_primitive (x0,x1,code) in
        let x0 = SAFE_CDR x2 in
        let (x0,x3) = mc_drop (x0,x3) in
        let x0 = Val 0 in
        let x0 = Dot x0 x3 in
        let x3 = x0 in
        let x0 = ^CONTINUE in
        let x1 = ^CONTINUE in
        let (x0,x1,x3,x4,code) = mc_return_code (x0,x1,x3,x4,code) in
        let x1 = ^CONTINUE in
        let x0 = Sym "NIL" in
          (x0,x1,x2,x3,x4,xs,code)``;

val mc_aux_ap_thm = prove(
  ``mc_aux_ap = BC_aux_ap``,
  SIMP_TAC std_ss [FUN_EQ_THM,FORALL_PROD,BC_aux_ap_def,LISP_TEST_EQ_T,CAR_def,CDR_def,
    mc_aux_ap_def,LET_DEF,HD,TL,list2sexp_def,mc_is_reserved_name_thm,getSym_def,getVal_def,
    EVAL ``LISP_ADD (Val 1) (Val 1)``,SAFE_CAR_def,SAFE_CDR_def]);


val BC_aux_call_aux_def = Define `
  BC_aux_call_aux (temp,ll,a) =
    if temp = Sym "NIL" then (temp,ll,a) else
      let a = CDR temp in
        if a = ll then
          let temp = CAR temp in (temp,ll,a)
        else
          let temp = Sym "NIL" in (temp,ll,a)`;

val BC_aux_call_def = Define `
  BC_aux_call (temp:SExp,task:SExp,exp:SExp,a:SExp,ret:SExp,consts:SExp,xs:SExp list,code) =
      let (t1,temp,t2) = mc_fun_lookup (task,CDR consts,CAR exp) in
      let (t1,ll) = mc_length (CDR exp,Val 0) in
      let (t3,a) = mc_drop (ll,a) in
      let a = Dot (Val 0) a in
      let (temp,ll,a2) = BC_aux_call_aux (temp,ll,a) in
      let task = ^CONTINUE in
        if temp = Sym "NIL" then
          let code = WRITE_CODE code [iCONST_NUM (getVal ll)] in
          let code = WRITE_CODE code [iCONST_SYM (getSym (CAR exp))] in
          let exp = Sym "NIL" in
            if ret = Sym "NIL" then
              let code = WRITE_CODE code [iCALL_SYM] in
                (Sym "NIL",task,exp,a,ret,consts,xs,code)
            else
              let a = Sym "NIL" in
              let code = WRITE_CODE code [iJUMP_SYM] in
                (Sym "NIL",task,exp,a,ret,consts,xs,code)
        else
          let exp = Sym "NIL" in
            if ret = Sym "NIL" then
              let code = WRITE_CODE code [iCALL (getVal temp)] in
                (Sym "NIL",task,exp,a,ret,consts,xs,code)
            else
              let a = Sym "NIL" in
              let code = WRITE_CODE code [iJUMP (getVal temp)] in
                (Sym "NIL",task,exp,a,ret,consts,xs,code)`;

val (_,mc_aux_call_aux_def,mc_aux_call_aux_pre_def) = compile "x64" ``
  mc_aux_call_aux (x0:SExp,x1:SExp,x3:SExp) =
    if x0 = Sym "NIL" then (x0,x1,x3) else
      let x3 = CDR x0 in
        if x3 = x1 then
          let x0 = CAR x0 in (x0,x1,x3)
        else
          let x0 = Sym "NIL" in (x0,x1,x3)``;

(* val mc_aux_call_def = Define *)
val (_,mc_aux_call_def,mc_aux_call_pre_def) = compile "x64" ``
  mc_aux_call (x0:SExp,x1:SExp,x2:SExp,x3:SExp,x4:SExp,x5:SExp,xs:SExp list,code) =
      let xs = x2::xs in
      let x0 = x1 in
      let x1 = SAFE_CDR x5 in
      let x2 = SAFE_CAR x2 in
      let (x0,x1,x2) = mc_fun_lookup (x0,x1,x2) in
      let x0 = x1 in
      let x2 = HD xs in
      let xs = TL xs in
      let xs = x0::xs in
      let x0 = SAFE_CDR x2 in
      let x1 = Val 0 in
      let (x0,x1) = mc_length (x0,x1) in (* x1 is ll *)
      let x0 = x1 in
      let x1 = HD xs in
      let xs = TL xs in
      let xs = x0::xs in
      let (x0,x3) = mc_drop (x0,x3) in
      let x0 = Val 0 in
      let x0 = Dot x0 x3 in
      let x3 = x0 in
      let x0 = x1 in (* x1 is temp *)
      let x1 = HD xs in
      let xs = x3::xs in
      let (x0,x1,x3) = mc_aux_call_aux (x0,x1,x3) in
      let x3 = HD xs in
      let xs = TL xs in
      let xs = TL xs in
        if x0 = Sym "NIL" then
          let x0 = x1 in
          let code = WRITE_CODE code [iCONST_NUM (getVal x0)] in
          let x0 = SAFE_CAR x2 in
          let x2 = Sym "NIL" in
          let code = WRITE_CODE code [iCONST_SYM (getSym x0)] in
            if x4 = Sym "NIL" then
              let code = WRITE_CODE code [iCALL_SYM] in
              let x1 = ^CONTINUE in
              let x0 = Sym "NIL" in
                (x0,x1,x2,x3,x4,x5,xs,code)
            else
              let x3 = Sym "NIL" in
              let code = WRITE_CODE code [iJUMP_SYM] in
              let x1 = ^CONTINUE in
              let x0 = Sym "NIL" in
                (x0,x1,x2,x3,x4,x5,xs,code)
        else
          let x2 = Sym "NIL" in
            if x4 = Sym "NIL" then
              let code = WRITE_CODE code [iCALL (getVal x0)] in
              let x1 = ^CONTINUE in
              let x0 = Sym "NIL" in
                (x0,x1,x2,x3,x4,x5,xs,code)
            else
              let x3 = Sym "NIL" in
              let code = WRITE_CODE code [iJUMP (getVal x0)] in
              let x1 = ^CONTINUE in
              let x0 = Sym "NIL" in
                (x0,x1,x2,x3,x4,x5,xs,code)``

val mc_aux_call_aux_thm = prove(
  ``mc_aux_call_aux = BC_aux_call_aux``,
  SIMP_TAC std_ss [FUN_EQ_THM,FORALL_PROD,mc_aux_call_aux_def,BC_aux_call_aux_def]);

val mc_aux_call_thm = prove(
  ``mc_aux_call = BC_aux_call``,
  SIMP_TAC std_ss [FUN_EQ_THM,FORALL_PROD,BC_aux_call_def,CAR_def,CDR_def,mc_aux_call_aux_thm,
    mc_aux_call_def,LET_DEF,HD,TL,list2sexp_def,mc_is_reserved_name_thm,getSym_def,getVal_def,
    EVAL ``LISP_ADD (Val 1) (Val 1)``,SAFE_CAR_def,SAFE_CDR_def]);


(* this is an almost readable version of mc_aux_tail *)
val BC_aux_tail_def = Define `
  BC_aux_tail (temp:SExp,task,exp,a,ret,consts,xs,code) =
    if task = ^COMPILE_LAM1 then (* ex list has been compiled *)
      let ret = HD xs in
      let xs = ^COMPILE_LAM2::exp::xs in
      let (t1,l) = mc_length (CAR (CDR (CAR exp)),Val 0) in
      let (temp,a) = mc_drop (l,a) in
      let (t1,t2,a) = mc_rev_append (CAR (CDR (CAR exp)),temp,a) in
      let task = ^COMPILE_EV in
      let exp = CAR (CDR (CDR (CAR exp))) in
        (Sym "NIL",task,exp,a,ret,consts,xs,code)
    else if task = ^COMPILE_LAM2 then (* add last append *)
      let task = ^CONTINUE in
      let temp = HD xs in
      let xs = TL xs in
      let a = Dot (Val 0) (HD xs) in
      let xs = TL xs in
        if temp = Sym "T" then
          (Sym "NIL",task,exp,a,ret,consts,xs,code)
        else
          let (t1,l) = mc_length (CAR (CDR (CAR exp)),Val 0) in
          let code = WRITE_CODE code [iPOPS (getVal l)] in
            (Sym "NIL",task,exp,a,ret,consts,xs,code)
    else if task = ^COMPILE_SET_RET then (* assign value to ret *)
      let ret = exp in
      let task = ^CONTINUE in
        (Sym "NIL",task,exp,a,ret,consts,xs,code)
    else if task = Sym "IF" then (* guard has been compiled *)
      let temp = HD xs in
      let ret = temp in
      let xs = TL xs in
      let task = Val (code_ptr code) in
      let xs = task::xs in
      let xs = exp::xs in
      let exp = Val 0 in
      let code = WRITE_CODE code [iJNIL (getVal exp)] in
      let exp = HD xs in
      let a = CAR exp in
      let exp = CDR exp in
      let xs = (^COMPILE_IF2)::xs in
      let exp = CAR exp in
      let task = ^COMPILE_EV in
        (Sym "NIL",task,exp,a,ret,consts,xs,code)
    else if task = Sym "OR" then (* guard has been compiled *)
      let temp = HD xs in
      let ret = temp in
      let xs = TL xs in
      let temp2 = Val 0 in
      let code = WRITE_CODE code [iLOAD (getVal temp2)] in
      let loc = Val (code_ptr code) in
      let exp1 = Val 0 in
      let code = WRITE_CODE code [iJNIL (getVal exp1)] in
      let a = Dot (Val 0) (CAR exp) in
      let (t1,t2,a,ret,code) = mc_return_code (task,task,a,ret,code) in
      let task = Val (code_ptr code) in
      let xs = task::xs in
      let xs = exp::xs in
      let exp1 = Val 0 in
      let code = WRITE_CODE code [iJUMP (getVal exp1)] in
      let task = Val (code_ptr code) in
      let code = WRITE_CODE code [iPOP] in
      let code = REPLACE_CODE code (getVal loc) (iJNIL (getVal task)) in
      let exp = HD xs in
      let a = CAR exp in
      let exp = CDR exp in
      let xs = (^COMPILE_OR2)::xs in
      let exp = Dot (Sym "OR") exp in
      let task = ^COMPILE_EV in
        (Sym "NIL",task,exp,a,ret,consts,xs,code)
    else if task = ^COMPILE_IF2 then (* exp for first case has been compiled *)
      let task = Val (code_ptr code) in
      let temp = HD xs in
      let xs = TL xs in
      let xs = task::xs in
      let xs = exp::xs in
      let exp = Val 0 in
      let code = WRITE_CODE code [iJUMP (getVal exp)] in
      let task = Val (code_ptr code) in
      let code = REPLACE_CODE code (getVal temp) (iJNIL (getVal task)) in
      let exp = HD xs in
      let a = CAR exp in
      let xs = a::xs in
      let exp = CDR exp in
      let xs = TL xs in
      let xs = (^COMPILE_IF3)::xs in
      let exp = CAR (CDR exp) in
      let task = ^COMPILE_EV in
        (Sym "NIL",task,exp,a,ret,consts,xs,code)
    else if task = ^COMPILE_IF3 then (* exp for fst and snd case have been compiled *)
      let a = exp in
      let a = CAR a in
      let a = Dot (Val 0) a in
      let exp = HD xs in
      let xs = TL xs in
      let task = Val (code_ptr code) in
      let code = REPLACE_CODE code (getVal exp) (iJUMP (getVal task)) in
      let exp = Sym "NIL" in
      let task = ^CONTINUE in
        (Sym "NIL",task,exp,a,ret,consts,xs,code)
    else if task = ^COMPILE_OR2 then (* just fix the iJUMP *)
      let a = exp in
      let a = CAR a in
      let a = Dot (Val 0) a in
      let exp = HD xs in
      let xs = TL xs in
      let task = Val (code_ptr code) in
      let code = REPLACE_CODE code (getVal exp) (iJUMP (getVal task)) in
      let exp = Sym "NIL" in
      let task = ^CONTINUE in
        (Sym "NIL",task,exp,a,ret,consts,xs,code)
    else if task = ^COMPILE_TAILOPT then (* rearrange stack for tail call *)
      let al = CAR exp in
      let xl = CDR exp in
      let padding = LISP_SUB xl al in
      let (t1,t2,code) = mc_stores (LISP_SUB (LISP_ADD al padding) (Val 1),xl,code) in
      let (temp,code) = mc_popn (LISP_SUB al xl,code) in
      let task = ^CONTINUE in
        (Sym "NIL",task,exp,a,ret,consts,xs,code)
    else if task = ^COMPILE_CALL then (* implements BC_call *)
      let temp = Sym "NIL" in
      let (temp,task,exp,a,ret,consts,xs,code) = BC_aux_call (temp,task,exp,a,ret,consts,xs,code) in
        (Sym "NIL",task,exp,a,ret,consts,xs,code)
    else (* if task = ^COMPILE_MACRO then ... *)
      let temp = Sym "NIL" in
      let (temp,task,exp,a,ret,consts,xs) = mc_expand_macro (temp,task,exp,a,ret,consts,xs) in
      let task = ^COMPILE_EV in
        (Sym "NIL",task,exp,a,ret,consts,xs,code)`;

(* val mc_aux_tail_def = Define *)
val (_,mc_aux_tail_def,mc_aux_tail_pre_def) = compile "x64" ``
  mc_aux_tail (x0:SExp,x1,x2,x3,x4,x5,xs,code) =
    let x0 = x1 in
    if x0 = ^COMPILE_LAM1 then (* ex list has been compiled *)
      let x4 = HD xs in
      let xs = x2::xs in
      let x0 = ^COMPILE_LAM2 in
      let xs = x0::xs in
      let x0 = SAFE_CAR x2 in
      let x0 = SAFE_CDR x0 in
      let x0 = SAFE_CAR x0 in
      let x1 = Val 0 in
      let (x0,x1) = mc_length (x0,x1) in
      let x0 = x1 in
      let (x0,x3) = mc_drop (x0,x3) in
      let x1 = x0 in
      let x0 = SAFE_CAR x2 in
      let x0 = SAFE_CDR x0 in
      let x0 = SAFE_CAR x0 in
      let (x0,x1,x3) = mc_rev_append (x0,x1,x3) in
      let x1 = ^COMPILE_EV in
      let x2 = SAFE_CAR x2 in
      let x2 = SAFE_CDR x2 in
      let x2 = SAFE_CDR x2 in
      let x2 = SAFE_CAR x2 in
      let x0 = Sym "NIL" in
        (x0,x1,x2,x3,x4,x5,xs,code)
    else if x0 = ^COMPILE_LAM2 then (* add last append *)
      let x0 = HD xs in
      let xs = TL xs in
      let x1 = HD xs in
      let x3 = Val 0 in
      let x3 = Dot x3 x1 in
      let x1 = ^CONTINUE in
      let xs = TL xs in
        if x0 = Sym "T" then
          let x0 = Sym "NIL" in
            (x0,x1,x2,x3,x4,x5,xs,code)
        else
          let x0 = SAFE_CAR x2 in
          let x0 = SAFE_CDR x0 in
          let x0 = SAFE_CAR x0 in
          let x1 = Val 0 in
          let (x0,x1) = mc_length (x0,x1) in
          let x0 = x1 in
          let code = WRITE_CODE code [iPOPS (getVal x0)] in
          let x1 = ^CONTINUE in
          let x0 = Sym "NIL" in
            (x0,x1,x2,x3,x4,x5,xs,code)
    else if x0 = ^COMPILE_SET_RET then (* assign value to x4 *)
      let x4 = x2 in
      let x1 = ^CONTINUE in
      let x0 = Sym "NIL" in
        (x0,x1,x2,x3,x4,x5,xs,code)
    else if x0 = Sym "IF" then (* guard has been compiled *)
      let x0 = HD xs in
      let x4 = x0 in
      let xs = TL xs in
      let x0 = Val (code_ptr code) in
      let xs = x0::xs in
      let xs = x2::xs in
      let x0 = Val 0 in
      let code = WRITE_CODE code [iJNIL (getVal x0)] in
      let x2 = HD xs in
      let x3 = SAFE_CAR x2 in
      let x2 = SAFE_CDR x2 in
      let x0 = ^COMPILE_IF2 in
      let xs = x0::xs in
      let x2 = SAFE_CAR x2 in
      let x1 = ^COMPILE_EV in
      let x0 = Sym "NIL" in
        (x0,x1,x2,x3,x4,x5,xs,code)
    else if x0 = Sym "OR" then
      let x4 = HD xs in
      let xs = TL xs in
      let x0 = Val 0 in
      let code = WRITE_CODE code [iLOAD (getVal x0)] in
      let x0 = Val (code_ptr code) in
      let x5 = Dot x5 x0 in
      let x0 = Val 0 in
      let code = WRITE_CODE code [iJNIL (getVal x0)] in
      let x0 = SAFE_CAR x2 in
      let x3 = Val 0 in
      let x3 = Dot x3 x0 in
      let x0 = x1 in
      let (x0,x1,x3,x4,code) = mc_return_code (x0,x1,x3,x4,code) in
      let x1 = CDR x5 in
      let x5 = CAR x5 in
      let x0 = Val (code_ptr code) in
      let xs = x0::xs in
      let xs = x2::xs in
      let x0 = Val 0 in
      let code = WRITE_CODE code [iJUMP (getVal x0)] in
      let x0 = Val (code_ptr code) in
      let code = WRITE_CODE code [iPOP] in
      let code = REPLACE_CODE code (getVal x1) (iJNIL (getVal x0)) in
      let x2 = HD xs in
      let x3 = SAFE_CAR x2 in
      let x2 = SAFE_CDR x2 in
      let x0 = ^COMPILE_OR2 in
      let xs = x0::xs in
      let x0 = Sym "OR" in
      let x0 = Dot x0 x2 in
      let x2 = x0 in
      let x1 = ^COMPILE_EV in
      let x0 = Sym "NIL" in
        (x0,x1,x2,x3,x4,x5,xs,code)
    else if x0 = ^COMPILE_IF2 then (* x2 for first case has been compiled *)
      let x0 = Val (code_ptr code) in
      let x1 = HD xs in
      let xs = TL xs in
      let xs = x0::xs in
      let xs = x2::xs in
      let x0 = Val 0 in
      let code = WRITE_CODE code [iJUMP (getVal x0)] in
      let x0 = Val (code_ptr code) in
      let code = REPLACE_CODE code (getVal x1) (iJNIL (getVal x0)) in
      let x2 = HD xs in
      let x3 = SAFE_CAR x2 in
      let xs = x3::xs in
      let x2 = SAFE_CDR x2 in
      let xs = TL xs in
      let x0 = ^COMPILE_IF3 in
      let xs = x0::xs in
      let x2 = SAFE_CDR x2 in
      let x2 = SAFE_CAR x2 in
      let x1 = ^COMPILE_EV in
      let x0 = Sym "NIL" in
        (x0,x1,x2,x3,x4,x5,xs,code)
    else if x0 = ^COMPILE_IF3 then (* x2 for fst and snd case have been compiled *)
      let x3 = x2 in
      let x3 = SAFE_CAR x3 in
      let x0 = Val 0 in
      let x0 = Dot x0 x3 in
      let x3 = x0 in
      let x2 = HD xs in
      let xs = TL xs in
      let x0 = Val (code_ptr code) in
      let x1 = x2 in
      let code = REPLACE_CODE code (getVal x1) (iJUMP (getVal x0)) in
      let x2 = Sym "NIL" in
      let x1 = ^CONTINUE in
      let x0 = Sym "NIL" in
        (x0,x1,x2,x3,x4,x5,xs,code)
    else if x0 = ^COMPILE_OR2 then (* just fix the iJUMP *)
      let x3 = x2 in
      let x3 = SAFE_CAR x3 in
      let x0 = x3 in
      let x3 = Val 0 in
      let x3 = Dot x3 x0 in
      let x2 = HD xs in
      let xs = TL xs in
      let x0 = Val (code_ptr code) in
      let x1 = x2 in
      let code = REPLACE_CODE code (getVal x1) (iJUMP (getVal x0)) in
      let x2 = Sym "NIL" in
      let x1 = ^CONTINUE in
      let x0 = Sym "NIL" in
        (x0,x1,x2,x3,x4,x5,xs,code)
    else if x0 = ^COMPILE_TAILOPT then (* rearrange stack for tail call *)
      let xs = x4::xs in
      let x1 = SAFE_CAR x2 in
      let x0 = SAFE_CDR x2 in
      let x4 = x0 in
      let x0 = LISP_SUB x0 x1 in
      let x0 = LISP_ADD x0 x1 in
      let x1 = Val 1 in
      let x0 = LISP_SUB x0 x1 in
      let x1 = x4 in
      let (x0,x1,code) = mc_stores (x0,x1,code) in
      let x4 = HD xs in
      let xs = TL xs in
      let x0 = SAFE_CAR x2 in
      let x1 = SAFE_CDR x2 in
      let x0 = LISP_SUB x0 x1 in
      let (x0,code) = mc_popn (x0,code) in
      let x1 = ^CONTINUE in
      let x0 = Sym "NIL" in
        (x0,x1,x2,x3,x4,x5,xs,code)
    else if x0 = ^COMPILE_CALL then (* implements BC_call *)
      let x0 = Sym "NIL" in
      let (x0,x1,x2,x3,x4,x5,xs,code) = mc_aux_call (x0,x1,x2,x3,x4,x5,xs,code) in
      let x0 = Sym "NIL" in
        (x0,x1,x2,x3,x4,x5,xs,code)
    else (* if x1 = ^COMPILE_MACRO then ... *)
      let x0 = Sym "NIL" in
      let (x0,x1,x2,x3,x4,x5,xs) = mc_expand_macro (x0,x1,x2,x3,x4,x5,xs) in
      let x1 = ^COMPILE_EV in
      let x0 = Sym "NIL" in
        (x0,x1,x2,x3,x4,x5,xs,code)``;

val mc_aux_tail_thm = prove(
  ``mc_aux_tail = BC_aux_tail``,
  SIMP_TAC std_ss [FUN_EQ_THM,FORALL_PROD,BC_aux_tail_def,CAR_def,CDR_def,
    mc_aux_tail_def,LET_DEF,HD,TL,list2sexp_def,mc_is_reserved_name_thm,getSym_def,getVal_def,
    mc_aux_call_thm, LISP_ADD_def,AC ADD_COMM ADD_ASSOC,SAFE_CAR_def,SAFE_CDR_def]);


val BC_aux1_def = Define `
  BC_aux1 (temp:SExp,task,exp,a,ret,consts,xs,xs1,code) =
    if task = ^COMPILE_EV then
      let (temp,task,exp,a,ret,consts,xs,xs1,code) = BC_aux_ev (temp,task,exp,a,ret,consts,xs,xs1,code) in
        (temp,task,exp,a,ret,consts,xs,xs1,code)
    else if task = ^COMPILE_EVL then
      if isDot exp then
        let xs = ^COMPILE_EVL::(CDR exp)::xs in
        let exp = CAR exp in
        let task = ^COMPILE_EV in
          (temp,task,exp,a,ret,consts,xs,xs1,code)
      else
        let task = ^CONTINUE in
          (temp,task,exp,a,ret,consts,xs,xs1,code)
    else if task = ^COMPILE_AP then
      let (temp,task,exp,a,ret,xs,code) = BC_aux_ap (temp,task,exp,a,ret,xs,code) in
        (temp,task,exp,a,ret,consts,xs,xs1,code)
    else
      let (temp,task,exp,a,ret,consts,xs,code) = BC_aux_tail (temp,task,exp,a,ret,consts,xs,code) in
        (temp,task,exp,a,ret,consts,xs,xs1,code)`;

(* val mc_aux1_def = Define *)
val (_,mc_aux1_def,mc_aux1_pre_def) = compile "x64" ``
  mc_aux1 (x0:SExp,x1,x2,x3,x4,x5,xs,xs1,code) =
    if x1 = ^COMPILE_EV then
      let (x0,x1,x2,x3,x4,x5,xs,xs1,code) = mc_aux_ev (x0,x1,x2,x3,x4,x5,xs,xs1,code) in
        (x0,x1,x2,x3,x4,x5,xs,xs1,code)
    else if x1 = ^COMPILE_EVL then
      if isDot x2 then
        let x1 = CDR x2 in
        let xs = x1::xs in
        let x1 = ^COMPILE_EVL in
        let xs = x1::xs in
        let x2 = CAR x2 in
        let x1 = ^COMPILE_EV in
          (x0,x1,x2,x3,x4,x5,xs,xs1,code)
      else
        let x1 = ^CONTINUE in
          (x0,x1,x2,x3,x4,x5,xs,xs1,code)
    else if x1 = ^COMPILE_AP then
      let (x0,x1,x2,x3,x4,xs,code) = mc_aux_ap (x0,x1,x2,x3,x4,xs,code) in
        (x0,x1,x2,x3,x4,x5,xs,xs1,code)
    else
      let (x0,x1,x2,x3,x4,x5,xs,code) = mc_aux_tail (x0,x1,x2,x3,x4,x5,xs,code) in
        (x0,x1,x2,x3,x4,x5,xs,xs1,code)``;

val (_,mc_loop_def,mc_loop_pre_def) = compile "x64" ``
  mc_loop (x0:SExp,x1,x2,x3,x4,x5,xs,xs1,code) =
    if x1 = ^CONTINUE then
      let x1 = HD xs in
      let xs = TL xs in
        if x1 = ^CONTINUE then
          (x0,x1,x2,x3,x4,x5,xs,xs1,code)
        else
          let x2 = HD xs in
          let xs = TL xs in
            mc_loop (x0,x1,x2,x3,x4,x5,xs,xs1,code)
    else
      let (x0,x1,x2,x3,x4,x5,xs,xs1,code) = mc_aux1 (x0,x1,x2,x3,x4,x5,xs,xs1,code) in
        mc_loop (x0,x1,x2,x3,x4,x5,xs,xs1,code)``;



val mc_loop_unroll =
  RW [mc_aux1_def,BC_aux_ev_def,BC_aux_ap_def,BC_aux_call_aux_def,BC_aux_call_def,BC_aux_tail_def,
      mc_aux_ev_thm,mc_aux_ap_thm,mc_aux_tail_thm,mc_aux_call_thm,
      mc_aux1_pre_def,mc_aux_ev_pre_def,mc_aux_ap_pre_def,
      mc_aux_tail_pre_def,mc_aux_call_pre_def,
      SAFE_CAR_def,SAFE_CDR_def] mc_loop_def;

val mc_loop_unroll_pre =
  RW [mc_aux1_def,BC_aux_ev_def,BC_aux_ap_def,BC_aux_call_aux_def,BC_aux_call_def,BC_aux_tail_def,
      mc_aux_ev_thm,mc_aux_ap_thm,mc_aux_tail_thm,mc_aux_call_thm,mc_aux_call_aux_thm,
      mc_aux1_pre_def,mc_aux_ev_pre_def,mc_aux_ap_pre_def,
      mc_aux_tail_pre_def,mc_aux_call_pre_def,mc_aux_call_aux_pre_def,
      SAFE_CAR_def,SAFE_CDR_def] mc_loop_pre_def;

val UNROLL_TAC =
  REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [Once mc_loop_unroll]
  \\ SIMP_TAC std_ss [Once mc_loop_unroll_pre]
  \\ SIMP_TAC std_ss [LET_DEF,SExp_11,SExp_distinct,term2sexp_def,func2sexp_def,isSym_def,prim2sym_def,mc_primitive_def]
  \\ SIMP_TAC std_ss [list2sexp_def,MAP,isDot_def,CAR_def,CDR_def,isSym_def,HD,TL]
  \\ SIMP_TAC (srw_ss()) []

val END_PROOF_TAC =
  FULL_SIMP_TAC std_ss [BC_return_def,mc_return_code_thm,APPEND_NIL,s2sexp_retract]
  \\ FULL_SIMP_TAC std_ss [a2sexp_def,a2sexp_aux_def,MAP,list2sexp_def,getVal_def,isVal_def]
  \\ FULL_SIMP_TAC std_ss [sexp2list_def,LENGTH,ADD1,ADD_SUB,sexp2list_list2sexp,
       LENGTH_MAP,WRITE_CODE_APPEND,code_ptr_WRITE_CODE,iLENGTH_thm]
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC std_ss [GSYM BC_ADD_CONST_def,bc_inv_ADD_CONST,iLENGTH_thm]
  \\ METIS_TAC [];

val bc_length_iJUMP = prove(
  ``!n. (bc_length (iJUMP n) = bc_length (iJUMP 0)) /\
        (bc_length (iJNIL n) = bc_length (iJNIL 0))``,
  EVAL_TAC \\ SIMP_TAC std_ss []);

val silly_lemma = prove(
  ``((if n2 = 2 then (x,Val 2,WRITE_CODE code [c1]) else
      if n2 = 1 then (x,Val 1,WRITE_CODE code [c2]) else
                     (x,Val n2,WRITE_CODE code [c2])) =
     (x,Val n2,WRITE_CODE code [if 2 = n2 then c1 else c2])) /\
    ((if n2 = 2 then (x,Val 2,WRITE_CODE code [c2]) else
      if n2 = 1 then (x,Val 1,WRITE_CODE code [c1]) else
                     (x,Val n2,WRITE_CODE code [c2])) =
     (x,Val n2,WRITE_CODE code [if 1 = n2 then c1 else c2]))``,
  Cases_on `n2 = 2` \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `n2 = 1` \\ FULL_SIMP_TAC std_ss []);


val mc_loop_lemma = prove(
  ``(!ret fc_n_a_q_bc new_code_a2_q2_bc2.
      BC_ap ret fc_n_a_q_bc new_code_a2_q2_bc2 ==>
        !fc n a fl q bc new_code a2 q2 bc2 xs code.
          (fc_n_a_q_bc = (fc,n,a,q,bc)) /\ (new_code_a2_q2_bc2 = (new_code,a2,q2,bc2)) /\
          bc_inv bc /\ (q = code_ptr code) ==>
          ?exp2.
             (mc_loop_pre (Sym "NIL",^COMPILE_AP,Dot (HD (func2sexp fc)) (Val n),a2sexp a,bool2sexp ret,bc_state_tree bc,xs,bc.consts,code) =
              mc_loop_pre (Sym "NIL",^CONTINUE,exp2,a2sexp a2,bool2sexp ret,bc_state_tree bc2,xs,bc2.consts,WRITE_CODE code new_code)) /\
             (mc_loop (Sym "NIL",^COMPILE_AP,Dot (HD (func2sexp fc)) (Val n),a2sexp a,bool2sexp ret,bc_state_tree bc,xs,bc.consts,code) =
              mc_loop (Sym "NIL",^CONTINUE,exp2,a2sexp a2,bool2sexp ret,bc_state_tree bc2,xs,bc2.consts,WRITE_CODE code new_code)) /\
             bc_inv bc2 /\ (bc2.compiled = bc.compiled) /\ (q2 = code_ptr (WRITE_CODE code new_code))) /\
    (!xs_a_q_bc new_code_a2_q2_bc2.
      BC_evl xs_a_q_bc new_code_a2_q2_bc2 ==>
        !xs a q bc new_code a2 q2 bc2 ys code.
          (xs_a_q_bc = (xs,a,q,bc)) /\ (new_code_a2_q2_bc2 = (new_code,a2,q2,bc2)) /\
          bc_inv bc /\ (q = code_ptr code) ==>
          ?exp2.
             (mc_loop_pre (Sym "NIL",^COMPILE_EVL,list2sexp (MAP term2sexp xs),a2sexp a,bool2sexp F,bc_state_tree bc,ys,bc.consts,code) =
              mc_loop_pre (Sym "NIL",^CONTINUE,exp2,a2sexp a2,bool2sexp F,bc_state_tree bc2,ys,bc2.consts,WRITE_CODE code new_code)) /\
             (mc_loop (Sym "NIL",^COMPILE_EVL,list2sexp (MAP term2sexp xs),a2sexp a,bool2sexp F,bc_state_tree bc,ys,bc.consts,code) =
              mc_loop (Sym "NIL",^CONTINUE,exp2,a2sexp a2,bool2sexp F,bc_state_tree bc2,ys,bc2.consts,WRITE_CODE code new_code)) /\
             bc_inv bc2 /\ (bc2.compiled = bc.compiled) /\ (q2 = code_ptr (WRITE_CODE code new_code))) /\
    (!ret x_a_q_bc new_code_a2_q2_bc2.
      BC_ev ret x_a_q_bc new_code_a2_q2_bc2 ==>
        !x a q bc new_code a2 q2 bc2 xs code.
          (x_a_q_bc = (x,a,q,bc)) /\ (new_code_a2_q2_bc2 = (new_code,a2,q2,bc2)) /\
          bc_inv bc /\ (q = code_ptr code) ==>
          ?exp2.
             (mc_loop_pre (Sym "NIL",^COMPILE_EV,term2sexp x,a2sexp a,bool2sexp ret,bc_state_tree bc,xs,bc.consts,code) =
              mc_loop_pre (Sym "NIL",^CONTINUE,exp2,a2sexp a2,bool2sexp ret,bc_state_tree bc2,xs,bc2.consts,WRITE_CODE code new_code)) /\
             (mc_loop (Sym "NIL",^COMPILE_EV,term2sexp x,a2sexp a,bool2sexp ret,bc_state_tree bc,xs,bc.consts,code) =
              mc_loop (Sym "NIL",^CONTINUE,exp2,a2sexp a2,bool2sexp ret,bc_state_tree bc2,xs,bc2.consts,WRITE_CODE code new_code)) /\
             bc_inv bc2 /\ (bc2.compiled = bc.compiled) /\ (q2 = code_ptr (WRITE_CODE code new_code)))``,
  HO_MATCH_MP_TAC BC_ev_ind \\ SIMP_TAC std_ss []
  \\ STRIP_TAC (* quote *) THEN1
   (STRIP_TAC \\ FULL_SIMP_TAC std_ss [term2sexp_def]
    \\ SIMP_TAC std_ss [Once mc_loop_unroll]
    \\ SIMP_TAC std_ss [Once mc_loop_unroll_pre,LISP_TEST_EQ_T]
    \\ SIMP_TAC std_ss [LET_DEF,SExp_11,SExp_distinct,term2sexp_def,isSym_def]
    \\ SIMP_TAC std_ss [list2sexp_def,CAR_def,CDR_def,isDot_def,isSym_def,isVal_def,isQuote_def,LISP_TEST_EQ_T]
    \\ SIMP_TAC (srw_ss()) [] \\ NTAC 3 STRIP_TAC
    \\ Cases_on `isVal s` \\ FULL_SIMP_TAC std_ss [] THEN1
     (`~(isDot s)` by FULL_SIMP_TAC std_ss [isDot_def,isVal_thm]
      \\ FULL_SIMP_TAC std_ss [] \\ END_PROOF_TAC)
    \\ Cases_on `isSym s` \\ FULL_SIMP_TAC std_ss [] THEN1
     (`~(isDot s)` by FULL_SIMP_TAC std_ss [isDot_def,isSym_thm]
      \\ FULL_SIMP_TAC std_ss [] \\ END_PROOF_TAC)
    \\ `isDot s` by (Cases_on `s` \\ FULL_SIMP_TAC std_ss [isDot_def,isSym_def,isVal_def])
    \\ FULL_SIMP_TAC std_ss [getVal_def,BC_ADD_CONST_def]
    \\ END_PROOF_TAC)
  \\ STRIP_TAC (* var lookup *) THEN1
   (STRIP_TAC \\ FULL_SIMP_TAC std_ss [term2sexp_def]
    \\ SIMP_TAC std_ss [Once mc_loop_unroll]
    \\ SIMP_TAC std_ss [Once mc_loop_unroll_pre,LISP_TEST_EQ_T]
    \\ SIMP_TAC std_ss [LET_DEF,SExp_11,SExp_distinct,term2sexp_def,isSym_def]
    \\ SIMP_TAC (srw_ss()) [HD,TL,NOT_CONS_NIL]
    \\ NTAC 5 STRIP_TAC \\ Cases_on `var_lookup 0 v a`
    \\ IMP_RES_TAC mc_alist_lookup_NONE
    \\ IMP_RES_TAC mc_alist_lookup_thm
    \\ REPEAT (Q.PAT_X_ASSUM `!x0.bbb` (STRIP_ASSUME_TAC o Q.SPEC `Val 0`))
    \\ ASM_SIMP_TAC std_ss [SExp_distinct,getVal_def]
    \\ END_PROOF_TAC)
  \\ STRIP_TAC (* FunApp *) THEN1
   (REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [Once mc_loop_unroll]
    \\ SIMP_TAC std_ss [Once mc_loop_unroll_pre]
    \\ SIMP_TAC std_ss [LET_DEF,SExp_11,SExp_distinct,isSym_def,prim2sym_def,mc_primitive_def]
    \\ ASM_SIMP_TAC std_ss [term2sexp_guard_lemma,NOT_isFun_IMP_guard]
    \\ `(CDR (term2sexp (App fc xs)) = list2sexp (MAP term2sexp xs)) /\
        (CAR (term2sexp (App fc xs)) = HD (func2sexp fc))` by
      (Cases_on `fc` \\ FULL_SIMP_TAC std_ss [term2sexp_def,isFun_def,
        func2sexp_def,APPEND,list2sexp_def,CDR_def,CAR_def,ETA_AX,HD])
    \\ ASM_SIMP_TAC std_ss [mc_length_thm,LENGTH_MAP,CAR_def,CDR_def,NOT_CONS_NIL,
         HD,TL,LISP_TEST_EQ_T,term2sexp_guard_lemma,mc_is_reserved_name_thm,
         NOT_isFun_IMP_guard]
    \\ Q.PAT_ABBREV_TAC `xsss = ^COMPILE_SET_RET::nothing`
    \\ Q.PAT_X_ASSUM `!xs.bbb` MP_TAC
    \\ Q.PAT_X_ASSUM `!xs.bbb` (STRIP_ASSUME_TAC o Q.SPECL [`xsss`,`code`])
    \\ FULL_SIMP_TAC std_ss [bool2sexp_def] \\ POP_ASSUM (K ALL_TAC)
    \\ Q.UNABBREV_TAC `xsss`
    \\ UNROLL_TAC
    \\ UNROLL_TAC
    \\ UNROLL_TAC
    \\ Q.PAT_X_ASSUM `!xs.bbb` (STRIP_ASSUME_TAC o Q.SPECL [`xs'`,`WRITE_CODE code code1`])
    \\ FULL_SIMP_TAC std_ss [WRITE_CODE_APPEND] \\ METIS_TAC [])
  \\ STRIP_TAC (* iDATA *) THEN1
   (REPEAT STRIP_TAC \\ Cases_on `fc`
    \\ Q.PAT_X_ASSUM `EVAL_DATA_OP xxx = (f,n1)` (ASSUME_TAC o RW [EVAL_DATA_OP_def] o GSYM)
    \\ UNROLL_TAC \\ FULL_SIMP_TAC std_ss [silly_lemma,mc_drop_thm]
    \\ Q.PAT_X_ASSUM `BC_return ret xxx = yyy` (ASSUME_TAC o GSYM) \\ END_PROOF_TAC)
  \\ STRIP_TAC (* App -- ret false *) THEN1
   (REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [Once mc_loop_unroll]
    \\ SIMP_TAC std_ss [Once mc_loop_unroll_pre]
    \\ SIMP_TAC std_ss [LET_DEF,SExp_11,SExp_distinct,isSym_def,prim2sym_def,mc_primitive_def]
    \\ ASM_SIMP_TAC std_ss [term2sexp_guard_lemma,bool2sexp_def]
    \\ FULL_SIMP_TAC std_ss [BC_is_reserved_name_Fun,bool2sexp_def,
         mc_is_reserved_name_thm,mc_strip_app_thm,LISP_TEST_EQ_T]
    \\ Q.PAT_ABBREV_TAC `xsss = ^COMPILE_CALL::nothing`
    \\ Q.PAT_X_ASSUM `!ys.bbb` (STRIP_ASSUME_TAC o RW [] o Q.SPECL [`xsss`,`code'`])
    \\ ASM_SIMP_TAC std_ss [list2sexp_def,CDR_def]
    \\ Q.UNABBREV_TAC `xsss`
    \\ UNROLL_TAC
    \\ UNROLL_TAC
    \\ FULL_SIMP_TAC std_ss [mc_length_thm,mc_drop_thm]
    \\ Cases_on `FUN_LOOKUP bc2.compiled fc` THEN1
     (Q.PAT_X_ASSUM `bc2.compiled = bc.compiled` (ASSUME_TAC o GSYM)
      \\ ASM_SIMP_TAC std_ss [BC_call_def,BC_call_aux_def,APPEND,WRITE_CODE_APPEND,getSym_def]
      \\ IMP_RES_TAC mc_fun_lookup_NONE_bc \\ ASM_SIMP_TAC std_ss []
      \\ Q.PAT_X_ASSUM `!x0:SExp.bbb` (STRIP_ASSUME_TAC o Q.SPEC `^COMPILE_CALL`)
      \\ FULL_SIMP_TAC std_ss [mc_length_thm,mc_drop_thm,LENGTH_MAP,getVal_def]
      \\ FULL_SIMP_TAC std_ss [a2sexp_def,MAP,a2sexp_aux_def,list2sexp_def,isVal_def]
      \\ Q.EXISTS_TAC `Sym "NIL"` \\ ASM_SIMP_TAC std_ss []
      \\ IMP_RES_TAC iLENGTH_thm
      \\ ASM_SIMP_TAC std_ss [code_ptr_WRITE_CODE,code_length_APPEND,AC ADD_COMM ADD_ASSOC])
    \\ Q.PAT_X_ASSUM `bc2.compiled = bc.compiled` (ASSUME_TAC o GSYM)
    \\ Cases_on `x`
    \\ ASM_SIMP_TAC std_ss [BC_call_def,APPEND,WRITE_CODE_APPEND,getSym_def]
    \\ IMP_RES_TAC mc_fun_lookup_SOME_bc \\ ASM_SIMP_TAC std_ss []
    \\ REPEAT (Q.PAT_X_ASSUM `!x0:SExp.bbb` (STRIP_ASSUME_TAC o Q.SPEC `^COMPILE_CALL`))
    \\ FULL_SIMP_TAC std_ss [mc_length_thm,mc_drop_thm,LENGTH_MAP,getVal_def]
    \\ FULL_SIMP_TAC std_ss [a2sexp_def,MAP,a2sexp_aux_def,list2sexp_def,isVal_def]
    \\ SIMP_TAC (srw_ss()) [CDR_def,CAR_def]
    \\ Cases_on `r = LENGTH xs` \\ ASM_SIMP_TAC (srw_ss()) []
    \\ Q.EXISTS_TAC `Sym "NIL"` \\ ASM_SIMP_TAC std_ss [BC_call_aux_def,getVal_def]
    \\ IMP_RES_TAC iLENGTH_thm
    \\ ASM_SIMP_TAC std_ss [code_ptr_WRITE_CODE,code_length_APPEND,AC ADD_COMM ADD_ASSOC]
    \\ SIMP_TAC std_ss [isDot_def,isVal_def,markerTheory.Abbrev_def])
  \\ STRIP_TAC (* App -- ret true *) THEN1
   (REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [Once mc_loop_unroll]
    \\ SIMP_TAC std_ss [Once mc_loop_unroll_pre]
    \\ SIMP_TAC std_ss [LET_DEF,SExp_11,SExp_distinct,isSym_def,prim2sym_def,mc_primitive_def]
    \\ ASM_SIMP_TAC std_ss [term2sexp_guard_lemma,bool2sexp_def]
    \\ FULL_SIMP_TAC std_ss [BC_is_reserved_name_Fun,bool2sexp_def,
         mc_is_reserved_name_thm,mc_strip_app_thm]
    \\ SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC std_ss [list2sexp_def,CDR_def]
    \\ FULL_SIMP_TAC std_ss [a2sexp_def,mc_length_thm,LENGTH_MAP]
    \\ SIMP_TAC std_ss [LISP_SUB_def,getVal_def]
    \\ FULL_SIMP_TAC std_ss [GSYM a2sexp_def,mc_push_nils_thm,LISP_TEST_EQ_T,CAR_def,isVal_def]
    \\ Q.PAT_ABBREV_TAC `xsss = ^COMPILE_TAILOPT::nothing`
    \\ Q.PAT_X_ASSUM `!ys.bbb` (MP_TAC o RW [] o Q.SPECL [`xsss`,`WRITE_CODE code'
         (n_times (LENGTH (xs:term list) - LENGTH (a:stack_slot list)) (iCONST_SYM "NIL"))`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (IMP_RES_TAC iLENGTH_thm
      \\ FULL_SIMP_TAC std_ss [code_ptr_WRITE_CODE,code_length_def])
    \\ STRIP_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.UNABBREV_TAC `xsss`
    \\ UNROLL_TAC
    \\ UNROLL_TAC
    \\ FULL_SIMP_TAC std_ss [LISP_ADD_def,LISP_SUB_def,getVal_def,
         mc_popn_thm,mc_stores_thm,WRITE_CODE_APPEND,APPEND_ASSOC]
    \\ UNROLL_TAC
    \\ UNROLL_TAC
    \\ UNROLL_TAC
    \\ UNROLL_TAC
    \\ FULL_SIMP_TAC std_ss [isVal_def,getSym_def,mc_length_thm,mc_drop_thm]
    \\ FULL_SIMP_TAC std_ss [WRITE_CODE_APPEND,APPEND]
    \\ Q.PAT_X_ASSUM `bc2.compiled = bc.compiled` (ASSUME_TAC o GSYM)
    \\ Cases_on `FUN_LOOKUP bc2.compiled fc` THEN1
     (Q.PAT_X_ASSUM `_.compiled = _.compiled` (ASSUME_TAC o GSYM)
      \\ ASM_SIMP_TAC std_ss [BC_call_def,BC_call_aux_def,APPEND,WRITE_CODE_APPEND,getSym_def]
      \\ IMP_RES_TAC mc_fun_lookup_NONE_bc \\ ASM_SIMP_TAC std_ss []
      \\ Q.PAT_X_ASSUM `!x0:SExp.bbb` (STRIP_ASSUME_TAC o Q.SPEC `^COMPILE_CALL`)
      \\ FULL_SIMP_TAC std_ss [mc_length_thm,mc_drop_thm,LENGTH_MAP,getVal_def]
      \\ FULL_SIMP_TAC std_ss [a2sexp_def,MAP,a2sexp_aux_def,list2sexp_def,isVal_def]
      \\ Q.EXISTS_TAC `Sym "NIL"` \\ ASM_SIMP_TAC std_ss [BC_call_def,BC_call_aux_def]
      \\ IMP_RES_TAC iLENGTH_thm
      \\ ASM_SIMP_TAC std_ss [code_ptr_WRITE_CODE,code_length_APPEND,AC ADD_COMM ADD_ASSOC])
    \\ Q.PAT_X_ASSUM `_.compiled = _.compiled` (ASSUME_TAC o GSYM)
    \\ Cases_on `x`
    \\ ASM_SIMP_TAC std_ss [BC_call_def,APPEND,WRITE_CODE_APPEND,getSym_def]
    \\ IMP_RES_TAC mc_fun_lookup_SOME_bc \\ ASM_SIMP_TAC std_ss []
    \\ REPEAT (Q.PAT_X_ASSUM `!x0:SExp.bbb` (STRIP_ASSUME_TAC o Q.SPEC `^COMPILE_CALL`))
    \\ FULL_SIMP_TAC std_ss [mc_length_thm,mc_drop_thm,LENGTH_MAP,getVal_def]
    \\ FULL_SIMP_TAC std_ss [a2sexp_def,MAP,a2sexp_aux_def,list2sexp_def,isVal_def]
    \\ SIMP_TAC (srw_ss()) [CDR_def,CAR_def]
    \\ Cases_on `r = LENGTH xs` \\ ASM_SIMP_TAC (srw_ss()) []
    \\ Q.EXISTS_TAC `Sym "NIL"` \\ ASM_SIMP_TAC std_ss [BC_call_def,BC_call_aux_def,getVal_def]
    \\ IMP_RES_TAC iLENGTH_thm
    \\ ASM_SIMP_TAC std_ss [code_ptr_WRITE_CODE,code_length_APPEND,AC ADD_COMM ADD_ASSOC]
    \\ SIMP_TAC std_ss [isDot_def,isVal_def,markerTheory.Abbrev_def])
  \\ STRIP_TAC (* If *) THEN1
   (ASM_SIMP_TAC std_ss [] \\ UNROLL_TAC \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_ABBREV_TAC `xsss = Sym "IF"::nothing`
    \\ Q.PAT_X_ASSUM `!xs.bbb` MP_TAC \\ Q.PAT_X_ASSUM `!xs.bbb` MP_TAC
    \\ Q.PAT_X_ASSUM `!xs.bbb` (STRIP_ASSUME_TAC o Q.SPECL [`xsss`,`code`])
    \\ Q.UNABBREV_TAC `xsss`
    \\ FULL_SIMP_TAC std_ss [bool2sexp_def] \\ POP_ASSUM (K ALL_TAC)
    \\ UNROLL_TAC
    \\ UNROLL_TAC
    \\ SIMP_TAC (srw_ss()) [getVal_def,isVal_def]
    \\ Q.PAT_ABBREV_TAC `xsss = ^COMPILE_IF2::nothing`
    \\ Q.PAT_X_ASSUM `!xs.bbb` MP_TAC
    \\ Q.PAT_X_ASSUM `!xs.bbb` (MP_TAC o Q.SPECL [`xsss`,`WRITE_CODE (WRITE_CODE code x_code) [iJNIL 0]`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (FULL_SIMP_TAC std_ss [code_ptr_WRITE_CODE,code_length_def,bc_inv_def] \\ EVAL_TAC)
    \\ STRIP_TAC
    \\ Q.UNABBREV_TAC `xsss`
    \\ ASM_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC) \\ REPEAT STRIP_TAC
    \\ UNROLL_TAC
    \\ UNROLL_TAC
    \\ SIMP_TAC std_ss [getVal_def]
    \\ Q.PAT_ABBREV_TAC `xsss = ^COMPILE_IF3::nothing`
    \\ Q.PAT_ABBREV_TAC `rep_code = REPLACE_CODE xx yy zz`
    \\ Q.PAT_X_ASSUM `!xs.bbb` (MP_TAC o Q.SPECL [`xsss`,`rep_code`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (Q.UNABBREV_TAC `rep_code`
      \\ FULL_SIMP_TAC std_ss [code_ptr_WRITE_CODE,code_ptr_REPLACE_CODE,
           code_length_def,bc_inv_def] \\ EVAL_TAC)
    \\ STRIP_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
    \\ Q.UNABBREV_TAC `xsss` \\ Q.UNABBREV_TAC `rep_code`
    \\ UNROLL_TAC
    \\ UNROLL_TAC
    \\ Q.EXISTS_TAC `Sym "NIL"`
    \\ ASM_SIMP_TAC std_ss [a2sexp_def,a2sexp_aux_def,MAP,list2sexp_def,getVal_def,isVal_def]
    \\ SIMP_TAC std_ss [CONJ_ASSOC]
    \\ REVERSE STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [code_ptr_WRITE_CODE,code_ptr_REPLACE_CODE,
           code_length_def,bc_inv_def,code_length_APPEND]
      \\ ONCE_REWRITE_TAC [bc_length_iJUMP]
      \\ FULL_SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC])
    \\ ASM_SIMP_TAC std_ss [WRITE_CODE_APPEND]
    \\ ASM_SIMP_TAC std_ss [SND_WRITE_CODE]
    \\ Q.PAT_ABBREV_TAC `new_jnil_offset = (code_ptr code + code_length (xxss ++ yyss))`
    \\ `bc_length (iJNIL 0) = bc_length (iJNIL new_jnil_offset)` by EVAL_TAC
    \\ IMP_RES_TAC REPLACE_CODE_RW \\ ASM_SIMP_TAC std_ss []
    \\ ASM_SIMP_TAC std_ss [SND_WRITE_CODE,WRITE_CODE_APPEND,code_ptr_REPLACE_CODE]
    \\ Q.ABBREV_TAC `new_jump_offset = (code_ptr code +
            code_length
              (x_code ++ ([iJNIL new_jnil_offset] ++ (y_code ++ [iJUMP 0]))) +
            code_length z_code)`
    \\ `bc_length (iJUMP 0) = bc_length (iJUMP new_jump_offset)` by EVAL_TAC
    \\ IMP_RES_TAC REPLACE_CODE_RW \\ ASM_SIMP_TAC std_ss []
    \\ POP_ASSUM (ASSUME_TAC o Q.SPECL [`z_code`,`x_code ++ [iJNIL new_jnil_offset] ++ y_code`])
    \\ FULL_SIMP_TAC std_ss [code_length_APPEND,code_length_def,APPEND_ASSOC,
         AC ADD_COMM ADD_ASSOC,getVal_def,isVal_def]
    \\ ASM_SIMP_TAC std_ss [APPEND_11,CONS_11]
    \\ SIMP_TAC (srw_ss()) []
    \\ Q.UNABBREV_TAC `new_jnil_offset`
    \\ ONCE_REWRITE_TAC [bc_length_iJUMP]
    \\ FULL_SIMP_TAC std_ss [bc_inv_def]
    \\ Q.PAT_ABBREV_TAC `xxx = mc_loop_pre xxxx`
    \\ Cases_on `xxx` \\ ASM_SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [bc_length_iJUMP]
    \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ SIMP_TAC std_ss [code_mem_WRITE_CODE]
    \\ Q.PAT_ABBREV_TAC `jnil = iJNIL (xxx + yyy)`
    \\ `x_code ++ jnil::(y_code ++ iJUMP 0::z_code) =
        (x_code ++ jnil::y_code) ++ iJUMP 0::z_code` by
      (FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND])
    \\ Q.PAT_ABBREV_TAC `l = code_length x_code + xxx`
    \\ `l = code_length (x_code ++ jnil::y_code) + code_ptr code` by
     (Q.UNABBREV_TAC `l` \\ Q.UNABBREV_TAC `jnil`
      \\ SIMP_TAC std_ss [code_length_APPEND,code_length_def]
      \\ ONCE_REWRITE_TAC [bc_length_iJUMP]
      \\ SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM])
    \\ FULL_SIMP_TAC std_ss [code_mem_WRITE_CODE])
  \\ STRIP_TAC (* Or -- base case *) THEN1
   (REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [term2sexp_def]
    \\ SIMP_TAC std_ss [Once mc_loop_unroll]
    \\ SIMP_TAC std_ss [Once mc_loop_unroll_pre]
    \\ SIMP_TAC std_ss [LET_DEF,SExp_11,SExp_distinct,isSym_def,prim2sym_def,
                        mc_primitive_def,list2sexp_def,MAP,CAR_def,CDR_def,isDot_def]
    \\ ASM_SIMP_TAC (srw_ss()) [getSym_def]
    \\ Q.PAT_X_ASSUM `!xs.bbb` (STRIP_ASSUME_TAC o RW [] o Q.SPECL [`xs`,`code'`] o GSYM)
    \\ Q.EXISTS_TAC `exp2` \\ ASM_SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ SIMP_TAC std_ss [Once mc_loop_unroll]
    \\ SIMP_TAC std_ss [Once mc_loop_unroll_pre]
    \\ SIMP_TAC std_ss [LET_DEF,SExp_11,SExp_distinct,isSym_def,prim2sym_def,isQuote_def,
                        mc_primitive_def,list2sexp_def,MAP,CAR_def,CDR_def,isDot_def,isVal_def]
    \\ ASM_SIMP_TAC (srw_ss()) [getSym_def,isSym_def,LISP_TEST_EQ_T])
  \\ STRIP_TAC (* Or -- step case *) THEN1
   (ASM_SIMP_TAC std_ss [] \\ UNROLL_TAC \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_ABBREV_TAC `xsss = Sym "OR"::nothing`
    \\ Q.PAT_X_ASSUM `!xs.bbb` MP_TAC
    \\ Q.PAT_X_ASSUM `!xs.bbb` (STRIP_ASSUME_TAC o Q.SPECL [`xsss`,`code`])
    \\ Q.UNABBREV_TAC `xsss`
    \\ FULL_SIMP_TAC std_ss [bool2sexp_def]
    \\ UNROLL_TAC
    \\ UNROLL_TAC
    \\ SIMP_TAC (srw_ss()) [getVal_def]
    \\ SIMP_TAC std_ss [WRITE_CODE_APPEND,code_ptr_WRITE_CODE,s2sexp_retract,
         mc_return_code_thm,APPEND_ASSOC,ETA_AX]
    \\ Q.PAT_ABBREV_TAC `xsss = ^COMPILE_OR2::nothing`
    \\ FULL_SIMP_TAC std_ss [term2sexp_def,list2sexp_def,ETA_AX]
    \\ Q.PAT_ABBREV_TAC `new_code = REPLACE_CODE xx yy zz`
    \\ Q.PAT_X_ASSUM `!xx yy. bb` (MP_TAC o RW [] o Q.SPECL [`xsss`,`new_code`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
      (Q.UNABBREV_TAC `new_code` \\ IMP_RES_TAC iLENGTH_thm
       \\ FULL_SIMP_TAC std_ss [code_ptr_WRITE_CODE,
            code_length_def,code_ptr_REPLACE_CODE,iLENGTH_thm]
       \\ FULL_SIMP_TAC std_ss [code_length_APPEND,AC ADD_COMM ADD_ASSOC,
            code_length_def] \\ ONCE_REWRITE_TAC [bc_length_iJUMP]
       \\ FULL_SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC])
    \\ STRIP_TAC
    \\ ASM_SIMP_TAC std_ss [isVal_def]
    \\ Q.UNABBREV_TAC `xsss`
    \\ ASM_SIMP_TAC std_ss []
    \\ UNROLL_TAC
    \\ UNROLL_TAC
    \\ SIMP_TAC std_ss [getVal_def,s2sexp_retract,isVal_def]
    \\ Q.EXISTS_TAC `Sym "NIL"`
    \\ ASM_SIMP_TAC std_ss [code_ptr_WRITE_CODE]
    \\ SIMP_TAC std_ss [CONJ_ASSOC]
    \\ REVERSE STRIP_TAC THEN1
     (Q.UNABBREV_TAC `new_code`
      \\ FULL_SIMP_TAC std_ss [code_ptr_WRITE_CODE,code_ptr_REPLACE_CODE,
           code_length_def,bc_inv_def,code_length_APPEND]
      \\ ONCE_REWRITE_TAC [bc_length_iJUMP]
      \\ FULL_SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC])
    \\ ASM_SIMP_TAC std_ss []
    \\ Q.UNABBREV_TAC `new_code`
    \\ ASM_SIMP_TAC std_ss [SND_WRITE_CODE,WRITE_CODE_APPEND,code_ptr_REPLACE_CODE]
    \\ Q.ABBREV_TAC `new_jnil_offset = (code_ptr code +
            code_length
              (x_code ++ [iLOAD 0] ++ [iJNIL 0] ++
               BC_return_code ret (ssTEMP::a)) +
            code_length [iJUMP 0])`
    \\ Q.ABBREV_TAC `new_jump_offset = (code_ptr code +
         code_length
          (x_code ++ [iLOAD 0] ++ [iJNIL 0] ++
           BC_return_code ret (ssTEMP::a) ++ [iJUMP 0] ++ [iPOP]) +
          code_length z_code)`
    \\ `bc_length (iJNIL 0) = bc_length (iJNIL new_jnil_offset)` by EVAL_TAC
    \\ IMP_RES_TAC REPLACE_CODE_RW
    \\ POP_ASSUM (ASSUME_TAC o Q.SPECL [`BC_return_code ret (ssTEMP::a) ++ [iJUMP 0] ++ [iPOP]`,
             `x_code ++ [iLOAD 0]`,`code`])
    \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC,code_length_APPEND,ADD_ASSOC,WRITE_CODE_APPEND]
    \\ `bc_length (iJUMP 0) = bc_length (iJUMP new_jump_offset)` by EVAL_TAC
    \\ Q.PAT_X_ASSUM `bc_length (iJNIL 0) = bc_length (iJNIL new_jnil_offset)` MP_TAC
    \\ IMP_RES_TAC REPLACE_CODE_RW
    \\ POP_ASSUM (ASSUME_TAC o Q.SPECL [`[iPOP] ++ z_code`,
             `x_code ++ [iLOAD 0] ++ [iJNIL new_jnil_offset] ++
              BC_return_code ret (ssTEMP::a)`,`code`])
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC,code_length_APPEND,
         AC ADD_COMM ADD_ASSOC,WRITE_CODE_APPEND,code_length_def]
    \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ `new_jnil_offset = addr + code_ptr code` by
      (Q.UNABBREV_TAC `new_jnil_offset`
       \\ Q.PAT_X_ASSUM `addr = xxx` (fn th => ONCE_REWRITE_TAC [th])
       \\ SIMP_TAC std_ss [code_ptr_WRITE_CODE,code_ptr_REPLACE_CODE,
            code_length_def,bc_inv_def,code_length_APPEND]
       \\ IMP_RES_TAC iLENGTH_thm
       \\ ASM_SIMP_TAC std_ss [code_length_def,code_length_APPEND]
       \\ ONCE_REWRITE_TAC [bc_length_iJUMP]
       \\ FULL_SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC])
    \\ ASM_SIMP_TAC std_ss []
    \\ Q.PAT_ABBREV_TAC `xxx = mc_loop_pre yyy`
    \\ Cases_on `xxx` \\ ASM_SIMP_TAC std_ss []
    \\ REPEAT STRIP_TAC THEN1
     (SIMP_TAC std_ss [APPEND_ASSOC,Once (GSYM (EVAL ``[x;y]++xs``))]
      \\ MATCH_MP_TAC code_mem_WRITE_CODE_IMP
      \\ SIMP_TAC std_ss [code_length_APPEND,code_length_def,
           AC ADD_ASSOC ADD_COMM])
    \\ SIMP_TAC std_ss [APPEND_ASSOC,Once (GSYM (EVAL ``[x]++xs``))]
    \\ MATCH_MP_TAC code_mem_WRITE_CODE_IMP
    \\ SIMP_TAC std_ss [code_length_APPEND,code_length_def,
           AC ADD_ASSOC ADD_COMM])
  \\ STRIP_TAC (* LamApp *) THEN1
   (REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [Once mc_loop_unroll]
    \\ SIMP_TAC std_ss [Once mc_loop_unroll_pre]
    \\ SIMP_TAC std_ss [LET_DEF,SExp_11,SExp_distinct,term2sexp_def,func2sexp_def,isSym_def]
    \\ SIMP_TAC std_ss [list2sexp_def,MAP,isDot_def,CAR_def,CDR_def,mc_drop_thm]
    \\ SIMP_TAC (srw_ss()) [isSym_def,isQuote_def,CAR_def,CDR_def,LISP_TEST_EQ_T]
    \\ Q.PAT_ABBREV_TAC `lambda = Dot (Dot (Sym "LAMBDA") xx) yy`
    \\ Q.PAT_X_ASSUM `!x.bbb` MP_TAC
    \\ Q.PAT_X_ASSUM `!x.bbb` (STRIP_ASSUME_TAC o RW [] o Q.SPECL [`^COMPILE_LAM1::lambda::bool2sexp ret::a2sexp a::xs'`,`code`])
    \\ `(\a. term2sexp a) = term2sexp` by FULL_SIMP_TAC std_ss [FUN_EQ_THM]
    \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [bool2sexp_def]
    \\ UNROLL_TAC
    \\ UNROLL_TAC
    \\ `CAR (CDR (CDR (CAR lambda))) = term2sexp x` by
         (Q.UNABBREV_TAC `lambda` \\ EVAL_TAC)
    \\ `CAR (CDR (CAR lambda)) = list2sexp (MAP Sym xs)` by
         (Q.UNABBREV_TAC `lambda` \\ EVAL_TAC)
    \\ ASM_SIMP_TAC std_ss [mc_length_thm,LENGTH_MAP,mc_drop_thm,mc_rev_append_thm]
    \\ Q.PAT_X_ASSUM `!xs.bbb` (MP_TAC o Q.SPECL [`^COMPILE_LAM2::lambda::bool2sexp ret::a2sexp a::xs'`,`WRITE_CODE code code1`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (IMP_RES_TAC iLENGTH_thm
      \\ FULL_SIMP_TAC std_ss [code_ptr_WRITE_CODE,code_length_def])
    \\ STRIP_TAC
    \\ ASM_SIMP_TAC std_ss []
    \\ UNROLL_TAC
    \\ UNROLL_TAC
    \\ Cases_on `ret`
    \\ IMP_RES_TAC iLENGTH_thm
    \\ FULL_SIMP_TAC std_ss [bc_inv_def]
    \\ ASM_SIMP_TAC std_ss [code_ptr_WRITE_CODE,code_length_def,code_length_APPEND]
    \\ ASM_SIMP_TAC (srw_ss()) [a2sexp_def,MAP,a2sexp_aux_def,list2sexp_def,
         bool2sexp_def,mc_length_thm,LENGTH_MAP,WRITE_CODE_APPEND,APPEND_NIL,
         APPEND_ASSOC,getVal_def,AC ADD_COMM ADD_ASSOC,isVal_def]
    \\ METIS_TAC [])
  \\ STRIP_TAC (* Print *) THEN1
   (REPEAT STRIP_TAC \\ SIMP_TAC std_ss [Once mc_loop_unroll]
    \\ SIMP_TAC std_ss [Once mc_loop_unroll_pre]
    \\ SIMP_TAC std_ss [LET_DEF,SExp_11,SExp_distinct,term2sexp_def,func2sexp_def,isSym_def]
    \\ SIMP_TAC std_ss [list2sexp_def,MAP,isDot_def,CAR_def,CDR_def,mc_drop_thm]
    \\ SIMP_TAC (srw_ss()) [WRITE_CODE_APPEND,LISP_SUB_def,LISP_ADD_def,getVal_def,
         mc_cons_list_thm,isVal_def] \\ FULL_SIMP_TAC std_ss [APPEND]
    \\ Q.PAT_X_ASSUM `BC_return ret xxx = yyy` (ASSUME_TAC o GSYM) \\ END_PROOF_TAC)
  \\ STRIP_TAC (* Error *) THEN1
   (REPEAT STRIP_TAC \\ SIMP_TAC std_ss [Once mc_loop_unroll]
    \\ SIMP_TAC std_ss [Once mc_loop_unroll_pre]
    \\ SIMP_TAC std_ss [LET_DEF,SExp_11,SExp_distinct,term2sexp_def,func2sexp_def,isSym_def]
    \\ SIMP_TAC std_ss [list2sexp_def,MAP,isDot_def,CAR_def,CDR_def,mc_drop_thm]
    \\ SIMP_TAC (srw_ss()) [WRITE_CODE_APPEND,LISP_SUB_def,LISP_ADD_def,getVal_def,
         mc_cons_list_thm] \\ FULL_SIMP_TAC std_ss [APPEND]
    \\ Q.PAT_X_ASSUM `BC_return ret xxx = yyy` (ASSUME_TAC o GSYM) \\ END_PROOF_TAC)
  \\ STRIP_TAC (* Compile *) THEN1
   (REPEAT STRIP_TAC \\ SIMP_TAC std_ss [Once mc_loop_unroll]
    \\ SIMP_TAC std_ss [Once mc_loop_unroll_pre]
    \\ SIMP_TAC std_ss [LET_DEF,SExp_11,SExp_distinct,term2sexp_def,func2sexp_def,isSym_def,HD]
    \\ SIMP_TAC std_ss [list2sexp_def,MAP,isDot_def,CAR_def,CDR_def,mc_drop_thm]
    \\ Q.PAT_X_ASSUM `BC_return ret xxx = yyy` (ASSUME_TAC o GSYM) \\ END_PROOF_TAC)
  \\ STRIP_TAC (* Funcall *) THEN1
   (REPEAT STRIP_TAC \\ SIMP_TAC std_ss [Once mc_loop_unroll]
    \\ SIMP_TAC std_ss [Once mc_loop_unroll_pre]
    \\ SIMP_TAC std_ss [LET_DEF,SExp_11,SExp_distinct,term2sexp_def,func2sexp_def,isSym_def,HD]
    \\ SIMP_TAC std_ss [list2sexp_def,MAP,isDot_def,CAR_def,CDR_def,mc_drop_thm]
    \\ SIMP_TAC (srw_ss()) [WRITE_CODE_APPEND,LISP_SUB_def,LISP_ADD_def,getVal_def]
    \\ Q.PAT_X_ASSUM `BC_return ret xxx = yyy` (ASSUME_TAC o GSYM) \\ END_PROOF_TAC)
  \\ STRIP_TAC THEN1
   (UNROLL_TAC \\ SIMP_TAC std_ss [WRITE_CODE_NIL] \\ METIS_TAC [])
  \\ STRIP_TAC THEN1
   (UNROLL_TAC \\ FULL_SIMP_TAC std_ss [bool2sexp_def]
    \\ Q.PAT_X_ASSUM `!x.bbb` MP_TAC
    \\ Q.PAT_X_ASSUM `!x.bbb` (STRIP_ASSUME_TAC o RW [] o Q.SPECL [`Val 1::list2sexp (MAP term2sexp xs)::ys`,`code'`])
    \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ UNROLL_TAC
    \\ Q.PAT_X_ASSUM `!x.bbb` (STRIP_ASSUME_TAC o RW [] o Q.SPECL [`ys`,`WRITE_CODE code' code`])
    \\ ASM_SIMP_TAC std_ss [WRITE_CODE_APPEND]
    \\ METIS_TAC [])
  (* only macros below *)
  \\ REVERSE (REPEAT STRIP_TAC) THEN
   (FULL_SIMP_TAC std_ss [term2sexp_def,func2sexp_def,prim2sym_def,APPEND]
    \\ UNROLL_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [isQuote_def,isDot_def,CAR_def,CDR_def,isVal_def,LISP_TEST_EQ_T]
    \\ Q.PAT_ABBREV_TAC `foo1 = (BC_is_reserved_name xx = Sym "NIL")`
    \\ Q.PAT_ABBREV_TAC `foo2 = (BC_is_reserved_name xx = Val 0)`
    \\ `~foo1 /\ foo2` by
      (Q.UNABBREV_TAC `foo1` \\ Q.UNABBREV_TAC `foo2` \\ EVAL_TAC)
    \\ Q.UNABBREV_TAC `foo1` \\ Q.UNABBREV_TAC `foo2`
    \\ ASM_SIMP_TAC (srw_ss()) [mc_is_reserved_name_thm]
    \\ UNROLL_TAC
    \\ ASM_SIMP_TAC (srw_ss()) [mc_expand_macro_thm,BC_expand_macro_def,CAR_def,LET_DEF,HD,TL]
    \\ FULL_SIMP_TAC std_ss [list2sexp_def,CDR_def,CAR_def,ETA_AX,MAP,mc_map_car_thm,HD,TL]
    \\ FULL_SIMP_TAC std_ss [sexp2list_list2sexp,MAP_MAP_o,o_ABS_R,CAR_def,CDR_def,isDot_def]
    \\ FULL_SIMP_TAC (srw_ss()) [o_DEF]
    \\ FULL_SIMP_TAC std_ss [GSYM list2sexp_def]
    \\ FULL_SIMP_TAC std_ss [term2sexp_def,ETA_AX]
    \\ Q.PAT_X_ASSUM `!xs bbb. bbbb` (STRIP_ASSUME_TAC o RW [] o Q.SPECL [`xs`,`code'`])
    \\ Q.EXISTS_TAC `exp2`
    \\ FULL_SIMP_TAC std_ss [] \\ NO_TAC));

val mc_loop_thm =
  mc_loop_lemma |> CONJUNCTS |> el 3 |> SIMP_RULE std_ss [PULL_FORALL_IMP]
  |> SPEC_ALL |> Q.INST [`xs`|->`^CONTINUE::xs`] |> RW1 [EQ_SYM_EQ]
  |> SIMP_RULE (srw_ss()) [LET_DEF,Once mc_loop_unroll]
  |> SIMP_RULE (srw_ss()) [LET_DEF,Once mc_loop_unroll_pre] |> RW1 [EQ_SYM_EQ]


(* reverse append with sfix *)

val (_,mc_rev_sfix_append_def,mc_rev_sfix_append_pre_def) = compile "x64" ``
  mc_rev_sfix_append (x0,x1,x3) =
    if ~(isDot x0) then (let x0 = Sym "NIL" in let x1 = x0 in (x0,x1,x3)) else
      let x1 = x0 in
      let x0 = x3 in
      let x3 = CAR x1 in
      let x3 = SFIX x3 in
      let x3 = Dot x3 x0 in
      let x0 = CDR x1 in
        mc_rev_sfix_append (x0,x1,x3)``;

val SFIX_THM = prove(``!x. SFIX x = Sym (getSym x)``,Cases \\ EVAL_TAC);

val mc_rev_sfix_append_thm = prove(
  ``!x ys y. (mc_rev_sfix_append_pre (x,y,a2sexp ys)) /\
              (mc_rev_sfix_append (x,y,a2sexp ys) =
                (Sym "NIL",Sym "NIL",a2sexp (MAP ssVAR (REVERSE (MAP getSym (sexp2list x))) ++ ys)))``,
  REVERSE Induct
  \\ SIMP_TAC std_ss [MAP,list2sexp_def,REVERSE_DEF,APPEND,LET_DEF,
      Once mc_rev_sfix_append_def,Once mc_rev_sfix_append_pre_def,isDot_def,
      CAR_def,CDR_def,SAFE_CAR_def,SAFE_CDR_def,sexp2list_def] \\ STRIP_TAC
  \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `ssVAR (getSym x)::ys`)
  \\ FULL_SIMP_TAC std_ss [a2sexp_def,MAP,list2sexp_def,a2sexp_aux_def,SFIX_THM,
        REVERSE_APPEND,MAP_APPEND]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]);


(* top-level compile function *)

val (mc_only_compile_spec,mc_only_compile_def,mc_only_compile_pre_def) = compile "x64" ``
  mc_only_compile (x0:SExp,x1,x2,x3:SExp,x4:SExp,x5,xs,xs1,code) =
    (* x0 - params *)
    (* x2 - term to compile *)
    (* x5 - bc_state_tree *)
    (* others are preserved *)
    let x3 = Sym "NIL" in
    let xs = x3::xs in
    let x4 = Sym "T" in
    let (x0,x1,x3) = mc_rev_sfix_append (x0,x1,x3) in
    let (x0,x1,x2,xs) = mc_sexp2sexp (x0,x1,x2,xs) in
    let x1 = Val 0 in
    let (x0,x1,x2,x3,x4,x5,xs,xs1,code) = mc_loop (x0,x1,x2,x3,x4,x5,xs,xs1,code) in
    let x2 = Sym "NIL" in
    let x3 = Sym "NIL" in
      (x0,x1,x2,x3,x4,x5,xs,xs1,code)``;

val BC_EV_HILBERT_LEMMA = prove(
  ``bc_inv bc /\ BC_ev T (t,a,q,bc) y ==> ((@result. BC_ev T (t,a,q,bc) result) = y)``,
  METIS_TAC [BC_ev_DETERMINISTIC,bc_inv_def]);

val INSERT_UNION_INSERT = store_thm("INSERT_UNION_INSERT",
  ``x INSERT (y UNION (z INSERT t)) = x INSERT z INSERT (y UNION t)``,
  SIMP_TAC std_ss [EXTENSION,IN_INSERT,IN_UNION] \\ METIS_TAC []);

fun abbrev_code (th,def_name) = let
  fun mk_tuple [] = fail()
    | mk_tuple [x] = x
    | mk_tuple (x::xs) = pairSyntax.mk_pair(x,mk_tuple xs)
  val th = th |> RW [INSERT_UNION_INSERT,INSERT_UNION_EQ,UNION_EMPTY,
                     GSYM UNION_ASSOC,UNION_IDEMPOT]
  val (_,_,c,_) = dest_spec (concl th)
  val input = mk_tuple (free_vars c)
  val ty = type_of (pairSyntax.mk_pabs(input,c))
  val name = mk_var(def_name,ty)
  val def = Define [ANTIQUOTE (mk_eq(mk_comb(name,input),c))]
  val th = RW [GSYM def] th
  in th end;

val RETURN_CLEAR_CACHE = let
  val th1 = Q.INST [`qs`|->`q::qs`,`cu`|->`NONE`] X64_LISP_STRENGTHEN_CODE
  val th2 = SPEC_FRAME_RULE (Q.INST [`ddd`|->`SOME T`,`cu`|->`NONE`] X64_LISP_RET) ``~zS``
  val (_,_,_,q) = dest_spec (concl th1)
  val (_,p,_,_) = dest_spec (concl th2)
  val th3 = INST (fst (match_term p q)) th2
  val th = MATCH_MP SPEC_COMPOSE (CONJ th1 th3) |> RW [INSERT_UNION_EQ,UNION_EMPTY]
  in th end;

val (_,_,code,_) = dest_spec (concl RETURN_CLEAR_CACHE)

val SPEC_DISJ_INTRO = prove(
  ``!m p c q r. SPEC m p c q ==> SPEC m (p \/ r) c (q \/ r)``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC (GEN_ALL (RW [UNION_IDEMPOT]
       (Q.INST [`c1`|->`c`,`c2`|->`c`] (SPEC_ALL SPEC_MERGE))))
  \\ Q.EXISTS_TAC `SEP_F` \\ ASM_SIMP_TAC std_ss [SEP_CLAUSES,SPEC_REFL]);

val SPEC_PRE_DISJ_LEMMA = prove(
  ``SPEC m p c q /\ SPEC m p2 c q2 ==>
    SPEC m (p \/ p2) c (q \/ q2)``,
  SIMP_TAC std_ss [SPEC_PRE_DISJ] \\ REPEAT STRIP_TAC \\ IMP_RES_TAC SPEC_WEAKEN
  \\ REPEAT (POP_ASSUM (MP_TAC o Q.SPEC `q \/ q2`))
  \\ FULL_SIMP_TAC std_ss [SEP_IMP_def,SEP_DISJ_def]);

val X64_LISP_CODE_INTRO_RETURN_CLEAR_CACHE = prove(
  ``SPEC X64_MODEL pp cc
     (let (x0,x1,x2,x3,x4,x5,xs,xs1,code) = hoo in
        ~zS * zPC p *
        zLISP (a1,a2,sl,sl1,e,ex,cs,rbp,SOME F,NONE)
          (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,q::qs,code,amnt,ok) \/
        zLISP_FAIL (a1,a2,sl,sl1,e,ex,cs,rbp,SOME F,NONE)) ==>
    SPEC X64_MODEL pp (cc UNION ^code)
     (let (x0,x1,x2,x3,x4,x5,xs,xs1,code) = hoo in
        ~zS * zPC q *
        zLISP (a1,a2,sl,sl1,e,ex,cs,rbp,SOME T,NONE)
          (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok) \/
        zLISP_FAIL (a1,a2,sl,sl1,e,ex,cs,rbp,SOME T,NONE))``,
  `?x0 x1 x2 x3 x4 x5 xs xs1 code. hoo = (x0,x1,x2,x3,x4,x5,xs,xs1,code)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC (RW [GSYM AND_IMP_INTRO] SPEC_COMPOSE)
  \\ POP_ASSUM MATCH_MP_TAC
  \\ MATCH_MP_TAC SPEC_PRE_DISJ_LEMMA \\ STRIP_TAC
  THEN1 (SIMP_TAC (std_ss++star_ss) []
         \\ METIS_TAC [SIMP_RULE (std_ss++star_ss) [] RETURN_CLEAR_CACHE])
  \\ FULL_SIMP_TAC std_ss [zLISP_FAIL_def,SPEC_REFL]);

val X64_LISP_COMPILE = save_thm("X64_LISP_COMPILE",let
  val th = MATCH_MP X64_LISP_CODE_INTRO_RETURN_CLEAR_CACHE
             (Q.INST [`qs`|->`q::qs`] mc_only_compile_spec)
  val ff = Q.INST [`ddd`|->`SOME F`,`cu`|->`NONE`]
  val jump = ff X64_LISP_CALL_EL8
  val def_name = "abbrev_code_for_compile"
  val th = abbrev_code (th,def_name)
  val th = SPEC_COMPOSE_RULE [ff X64_LISP_WEAKEN_CODE,ff X64_LISP_CALL_EL8,th]
  val th = RW [STAR_ASSOC] th
  val _ = add_compiled [th]
  in th end);


(* code for iCOMPILE -- stores function definition into bc_state, i.e. x5 *)

val _ = let (* reload all primitive ops with SOME T for ddd *)
  val thms = DB.match [] ``SPEC X64_MODEL``
  val thms = filter (can (find_term (can (match_term ``zLISP``))) o car o concl)
                    (map (#1 o #2) thms)
  val thms = map (Q.INST [`ddd`|->`SOME T`,`cu`|->`NONE`]) thms
  val _ = map (fn th => add_compiled [th] handle e => ()) thms
  in () end;

val (_,mc_arg_length_def,mc_arg_length_pre_def) = compile "x64" ``
  mc_arg_length (x0,x1) =
    if ~(isDot x0) then let x0 = Sym "NIL" in (x0,x1) else
      let x0 = CDR x0 in
      let x1 = LISP_ADD x1 (Val 1) in
        mc_arg_length (x0,x1)``

val mc_arg_length_thm = prove(
  ``!x n.
       mc_arg_length_pre (x,Val n) /\
       (mc_arg_length (x,Val n) = (Sym "NIL",Val (n + LENGTH (sexp2list x))))``,
  Induct \\ ASM_SIMP_TAC std_ss [sexp2list_def,Once mc_arg_length_def,isDot_def,
    LENGTH,CDR_def,LISP_ADD_def,getVal_def,Once mc_arg_length_pre_def,LET_DEF,isVal_def]
  \\ SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM,ADD1]);

val (_,mc_store_fun_def,mc_store_fun_pre_def) = compile "x64" ``
  mc_store_fun (x0:SExp,x1:SExp,x3:SExp,x4:SExp,x5,code) =
    let x0 = x3 in
    let x1 = Val 0 in
    let (x0,x1) = mc_arg_length (x0,x1) in
    let x0 = Val (code_ptr code) in
    let x0 = Dot x0 x1 in
    let x1 = CDR x5 in
    let x0 = Dot x0 x1 in
    let x1 = x4 in
    let x1 = Dot x1 x0 in
    let x0 = CAR x5 in
    let x0 = Dot x0 x1 in
    let x5 = x0 in
      (x0,x1,x3,x4,x5,code)``

val list2sexp_11 = prove(
  ``!x y. (list2sexp x = list2sexp y) = (x = y)``,
  Induct \\ Cases_on `y` \\ EVAL_TAC \\ ASM_SIMP_TAC std_ss [])

val mc_store_fun_thm = prove(
  ``bc_inv bc ==>
      ?y0 y1 bc2.
        mc_store_fun_pre (x0,x1,params,Sym fname,bc_state_tree bc,code) /\
        (mc_store_fun (x0,x1,params,Sym fname,bc_state_tree bc,code) =
           (y0,y1,params,Sym fname,bc_state_tree bc2,code)) /\
        (bc2 = BC_STORE_COMPILED bc fname (code_ptr code,LENGTH (sexp2list params))) /\
        bc_inv bc2``,
  SIMP_TAC std_ss [mc_store_fun_def,mc_store_fun_pre_def,LET_DEF]
  \\ ASM_SIMP_TAC std_ss [mc_arg_length_thm,bc_state_tree_def,isDot_def,CAR_def,CDR_def]
  \\ FULL_SIMP_TAC (srw_ss()) [BC_STORE_COMPILED_def,bc_inv_def,const_tree_def]
  \\ FULL_SIMP_TAC std_ss [GSYM list2sexp_def,list2sexp_11,LENGTH,EVEN]
  \\ FULL_SIMP_TAC std_ss [flat_alist_def]
  \\ FULL_SIMP_TAC (srw_ss()) [BC_CODE_OK_def] \\ METIS_TAC []);

val (_,mc_fun_exists_def,mc_fun_exists_pre_def) = compile "x64" ``
  mc_fun_exists (x0,x1,x4) =
    if ~(isDot x1) then (x0,x1,x4) else
      let x0 = CAR x1 in
      let x1 = CDR x1 in
        if x0 = x4 then
          let x1 = Sym "T" in
            (x0,x1,x4)
        else
          let x1 = CDR x1 in
            mc_fun_exists (x0,x1,x4)``

val mc_fun_exists_thm = prove(
  ``!xs y fc. ?y0.
      mc_fun_exists_pre (y,list2sexp (flat_alist xs),Sym fc) /\
      (mc_fun_exists (y,list2sexp (flat_alist xs),Sym fc) =
         (y0,LISP_TEST (MEM fc (MAP FST xs)),Sym fc))``,
  Induct \\ SIMP_TAC std_ss [flat_alist_def,list2sexp_def,MAP,MEM]
  \\ ONCE_REWRITE_TAC [mc_fun_exists_def,mc_fun_exists_pre_def]
  \\ SIMP_TAC std_ss [isDot_def,LISP_TEST_def]
  \\ Cases_on `h` \\ Cases_on `r` \\ SIMP_TAC (srw_ss()) [isDot_def,
       LET_DEF,flat_alist_def,list2sexp_def,CAR_def,CDR_def,
       markerTheory.Abbrev_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `q = fc` \\ FULL_SIMP_TAC std_ss [LISP_TEST_def]);

val no_such_function_bool_def = Define `
  no_such_function_bool = F`;

val _ = let
  val thms = [SPEC_COMPOSE_RULE [X64_LISP_ERROR_11,X64_LISP_SET_OK_F]]
  val thms = map (RW [GSYM no_such_function_bool_def]) thms
  val thms = map (Q.INST [`ddd`|->`SOME T`,`cu`|->`NONE`]) thms
  val _ = map (fn th => add_compiled [th] handle e => ()) thms
  in () end;

val (_,mc_check_exists_def,mc_check_exists_pre_def) = compile "x64" ``
  mc_check_exists (x0,x1,x4,ok:bool) =
    let (x0,x1,x4) = mc_fun_exists (x0,x1,x4) in
      if x1 = Sym "NIL" then (x0,x1,x4,ok) else
        let (x0,ok) = (no_such_function x0,no_such_function_bool) in
          (x0,x1,x4,ok)``

val FUN_LOOKUP_EQ_NONE = prove(
  ``!xs. (FUN_LOOKUP xs y = NONE) = ~(MEM y (MAP FST xs))``,
  Induct \\ FULL_SIMP_TAC std_ss [FUN_LOOKUP_def,MAP,MEM,FORALL_PROD]
  \\ SRW_TAC [] []);

val mc_check_exists_thm = prove(
  ``!xs y fc ok.
      (FUN_LOOKUP xs fc = NONE) ==>
      ?y0.
        mc_check_exists_pre (y,list2sexp (flat_alist xs),Sym fc,ok) /\
        (mc_check_exists (y,list2sexp (flat_alist xs),Sym fc,ok) =
           (y0,Sym "NIL",Sym fc,ok))``,
  SIMP_TAC std_ss [mc_check_exists_def,mc_check_exists_pre_def,FUN_LOOKUP_EQ_NONE]
  \\ REPEAT STRIP_TAC \\ STRIP_ASSUME_TAC (SPEC_ALL mc_fun_exists_thm)
  \\ FULL_SIMP_TAC std_ss [LET_DEF,LISP_TEST_def]);

val mc_check_exists_thm_alt = prove(
  ``!xs y fc ok.
      ~(FUN_LOOKUP xs fc = NONE) ==>
      ?y0.
        mc_check_exists_pre (y,list2sexp (flat_alist xs),Sym fc,ok) /\
        (mc_check_exists (y,list2sexp (flat_alist xs),Sym fc,ok) =
           (y0,Sym "T",Sym fc,F))``,
  SIMP_TAC std_ss [mc_check_exists_def,mc_check_exists_pre_def,FUN_LOOKUP_EQ_NONE]
  \\ REPEAT STRIP_TAC \\ STRIP_ASSUME_TAC (SPEC_ALL mc_fun_exists_thm)
  \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF,LISP_TEST_def] \\ EVAL_TAC);

val (mc_compile_inst_spec,mc_compile_inst_def,mc_compile_inst_pre_def) = compile "x64" ``
  mc_compile_inst (x0:SExp,x1,x2:SExp,x3:SExp,x4:SExp,x5,xs,xs1,code,ok) =
    (* take args off stack *)
    let x2 = x0 in    (* body *)
    let x3 = HD xs in (* params *)
    let xs = TL xs in
    let x4 = HD xs in (* fname *)
    let x4 = SFIX x4 in
    let xs = TL xs in
    (* check that definition does not already exist *)
    let x1 = CDR x5 in
    let (x0,x1,x4,ok) = mc_check_exists (x0,x1,x4,ok) in
      if ~(x1 = Sym "NIL") then
        let x0 = Sym "NIL" in
        let x1 = Sym "NIL" in
        let x2 = Sym "NIL" in
        let x3 = Sym "NIL" in
        let x4 = Sym "NIL" in
          (x0,x1,x2,x3,x4,x5,xs,xs1,code,ok)
      else
        (* store definition *)
        let (x0,x1,x3,x4,x5,code) = mc_store_fun (x0,x1,x3,x4,x5,code) in
        (* compile *)
        let x0 = x3 in
        let (x0,x1,x2,x3,x4,x5,xs,xs1,code) = mc_only_compile (x0,x1,x2,x3,x4,x5,xs,xs1,code) in
        (* return nil *)
        let x0 = Sym "NIL" in
          (x0,x1,x2,x3,x4,x5,xs,xs1,code,ok)``;

val APPEND_NORMAL_RET = prove(
  ``SPEC X64_MODEL pp cc
    (let (x0,x1,x2,x3,x4,x5,xs,xs1,code,ok) = hoo in
       ~zS * zPC d * zLISP (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu)
          (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,q::qs,code,amnt,ok)
       \/ zLISP_FAIL (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu)) ==>
    SPEC X64_MODEL pp (cc UNION {(d,[0x48w; 0xC3w])})
    (let (x0,x1,x2,x3,x4,x5,xs,xs1,code,ok) = hoo in
       ~zS * zPC q * zLISP (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu)
          (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok)
       \/ zLISP_FAIL (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu))``,
  REPEAT STRIP_TAC
  \\ `?x0 x1 x2 x3 x4 x5 xs xs1 code ok. hoo = (x0,x1,x2,x3,x4,x5,xs,xs1,code,ok)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [LET_DEF] \\ POP_ASSUM (K ALL_TAC)
  \\ POP_ASSUM (fn th => MP_TAC (SPEC_COMPOSE_RULE [th,X64_LISP_RET]))
  \\ FULL_SIMP_TAC (std_ss++star_ss) []);

val bc_state_tree_code_end = prove(
  ``bc_state_tree (bc with code_end := x) = bc_state_tree bc``,
  FULL_SIMP_TAC (srw_ss()) [bc_state_tree_def,const_tree_def]);

val bc_state_tree_WRITE_BYTECODE = prove(
  ``!xs a bc. bc_state_tree (WRITE_BYTECODE bc a xs) = bc_state_tree bc``,
  Induct \\ FULL_SIMP_TAC std_ss [WRITE_BYTECODE_def]
  \\ FULL_SIMP_TAC (srw_ss()) [bc_state_tree_def,const_tree_def]);

val WRITE_BYTECODE_code_end = store_thm("WRITE_BYTECODE_code_end",
  ``!xs a bc. ((WRITE_BYTECODE bc a xs).code_end = bc.code_end) /\
              ((WRITE_BYTECODE bc a xs).instr_length = bc.instr_length) /\
              ((WRITE_BYTECODE bc a xs).consts = bc.consts)``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [WRITE_BYTECODE_def]);

val BC_CODE_OK_WRITE_BYTECODE_LEMMA = prove(
  ``!xs a bc x y.
      (WRITE_BYTECODE (bc with <|code := x; code_end := y|>) a xs).code =
      (WRITE_BYTECODE (bc with <|code := x|>) a xs).code``,
  Induct \\ ASM_SIMP_TAC (srw_ss()) [WRITE_BYTECODE_def]);

val WRITE_CODE_EQ_WRITE_BYTECODE = store_thm("WRITE_CODE_EQ_WRITE_BYTECODE",
  ``!xs bc.
     (bc_length = bc.instr_length) ==>
     (WRITE_CODE (BC_CODE (bc.code,bc.code_end)) xs =
      BC_CODE ((WRITE_BYTECODE bc bc.code_end xs).code,
               bc.code_end + iLENGTH bc_length xs))``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [WRITE_BYTECODE_def,WRITE_CODE_def,iLENGTH_def]
  \\ REPEAT STRIP_TAC
  \\ Q.PAT_X_ASSUM `!bc.bbb`
    (MP_TAC o Q.SPEC `(bc with code_end := bc.code_end + bc_length h)
                          with code := (bc.code_end =+ SOME h) bc.code`)
  \\ FULL_SIMP_TAC (srw_ss()) [ADD_ASSOC] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [BC_CODE_OK_WRITE_BYTECODE_LEMMA]);

val bc_inv_WRITE_BYTECODE = prove(
  ``!xs bc.
      bc_inv bc ==>
      bc_inv
       (WRITE_BYTECODE bc bc.code_end xs with
        code_end := bc.code_end + iLENGTH bc.instr_length xs)``,
  Induct \\ SIMP_TAC std_ss [bc_inv_def]
  THEN1 (SIMP_TAC (srw_ss()) [WRITE_BYTECODE_def,iLENGTH_def,BC_CODE_OK_def]
         \\ METIS_TAC []) \\ FULL_SIMP_TAC (srw_ss()) [WRITE_BYTECODE_code_end]
  \\ SIMP_TAC std_ss [WRITE_BYTECODE_def,iLENGTH_def] \\ REPEAT STRIP_TAC
  \\ `bc_inv (WRITE_BYTECODE bc bc.code_end [h] with
        code_end := bc.code_end + iLENGTH bc.instr_length [h])` by
   (FULL_SIMP_TAC (srw_ss()) [BC_CODE_OK_def,WRITE_BYTECODE_def,iLENGTH_def,
      APPLY_UPDATE_THM,bc_inv_def] \\ REPEAT STRIP_TAC
    THEN1 (Cases_on `h'` \\ EVAL_TAC \\ Cases_on `l` \\ EVAL_TAC)
    THEN1 EVAL_TAC THEN1 EVAL_TAC
    \\ `0 < bc.instr_length h` by METIS_TAC []
    \\ `bc.code_end <= i` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []
    \\ `0 < bc_length h` by METIS_TAC [] \\ DECIDE_TAC)
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [bc_inv_def]
  \\ FULL_SIMP_TAC (srw_ss()) [WRITE_BYTECODE_code_end,WRITE_BYTECODE_def,iLENGTH_def,ADD_ASSOC]
  \\ FULL_SIMP_TAC (srw_ss()) [BC_CODE_OK_def,WRITE_BYTECODE_code_end]
  \\ FULL_SIMP_TAC std_ss [BC_CODE_OK_WRITE_BYTECODE_LEMMA] \\ METIS_TAC []);

val mc_only_compile_lemma = prove(
  ``bc_inv bc /\ (BC_ev_fun (MAP getSym (sexp2list params),sexp2term body,bc) = (new_code,a2,q2,bc2)) ==>
      mc_only_compile_pre (params,x1,body,x3,
           x4,bc_state_tree bc,xs,bc.consts,BC_CODE (bc.code,bc.code_end)) /\
      (mc_only_compile (params,x1,body,x3,
           x4,bc_state_tree bc,xs,bc.consts,BC_CODE (bc.code,bc.code_end)) =
        (Sym "NIL",Sym "NIL",Sym "NIL",Sym "NIL",Sym "T",bc_state_tree bc2,
         xs,bc2.consts,WRITE_CODE (BC_CODE (bc.code,bc.code_end)) new_code)) /\
      bc_inv bc2``,
  SIMP_TAC std_ss [mc_only_compile_def,mc_only_compile_pre_def,
        LET_DEF,GSYM (EVAL ``a2sexp []``),mc_sexp2sexp_thm]
  \\ SIMP_TAC std_ss [sexp2sexp_thm]
  \\ Q.SPEC_TAC (`sexp2term body`,`bbody`) \\ STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [mc_rev_sfix_append_thm,APPEND_NIL]
  \\ SIMP_TAC std_ss [EVAL ``a2sexp []``,BC_ev_fun_def] \\ STRIP_TAC
  \\ `BC_JUMPS_OK bc` by
    (FULL_SIMP_TAC std_ss [bc_inv_def,BC_JUMPS_OK_def]
     \\ EVAL_TAC \\ SIMP_TAC std_ss [])
  \\ Q.ABBREV_TAC `ps = MAP getSym (sexp2list params)`
  \\ `?y. BC_ev T (bbody,MAP ssVAR (REVERSE ps),bc.code_end,bc) y` by METIS_TAC [BC_ev_TOTAL,bc_inv_def]
  \\ IMP_RES_TAC BC_EV_HILBERT_LEMMA \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `y = xxx` (fn th => FULL_SIMP_TAC std_ss [th])
  \\ IMP_RES_TAC (SIMP_RULE std_ss [code_ptr_def]
    (Q.INST [`code`|->`BC_CODE (bc.code,bc.code_end)`] mc_loop_thm))
  \\ POP_ASSUM (STRIP_ASSUME_TAC o SPEC_ALL)
  \\ FULL_SIMP_TAC std_ss [bool2sexp_def]);

val WRITE_BYTECODE_code = prove(
  ``!new_code bc bc3 a.
      (bc.code = bc3.code) /\ (bc.instr_length = bc3.instr_length) ==>
      ((WRITE_BYTECODE bc a new_code).code =
       (WRITE_BYTECODE bc3 a new_code).code)``,
  Induct \\ SIMP_TAC std_ss [WRITE_BYTECODE_def] \\ REPEAT STRIP_TAC
  \\ Q.ABBREV_TAC `bcA = (bc with code := (a =+ SOME h) bc3.code)`
  \\ Q.ABBREV_TAC `bc3A = (bc3 with code := (a =+ SOME h) bc3.code)`
  \\ `(bcA.code = bc3A.code) /\ (bcA.instr_length = bc3A.instr_length)` by
       (Q.UNABBREV_TAC `bc3A` \\ Q.UNABBREV_TAC `bcA` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ RES_TAC \\ ASM_SIMP_TAC std_ss []);

val mc_only_compile_thm = prove(
  ``bc_inv bc ==>
    let bc2 = BC_ONLY_COMPILE (MAP getSym (sexp2list params),sexp2term body,bc) in
      mc_only_compile_pre (params,x1,body,x3,
           x4,bc_state_tree bc,xs,bc.consts,BC_CODE (bc.code,bc.code_end)) /\
      (mc_only_compile (params,x1,body,x3,
           x4,bc_state_tree bc,xs,bc.consts,BC_CODE (bc.code,bc.code_end)) =
        (Sym "NIL",Sym "NIL",Sym "NIL",Sym "NIL",Sym "T",bc_state_tree bc2,
         xs,bc2.consts,BC_CODE (bc2.code,bc2.code_end))) /\
      bc_inv bc2``,
  STRIP_TAC
  \\ Q.ABBREV_TAC `ps = MAP getSym (sexp2list params)`
  \\ `?new_code a2 q2 bc3. (BC_ev_fun (ps,sexp2term body,bc) = (new_code,a2,q2,bc3))` by METIS_TAC [PAIR]
  \\ Q.UNABBREV_TAC `ps`
  \\ IMP_RES_TAC mc_only_compile_lemma
  \\ FULL_SIMP_TAC std_ss [LET_DEF,BC_ONLY_COMPILE_def]
  \\ FULL_SIMP_TAC std_ss [bc_state_tree_WRITE_BYTECODE,bc_state_tree_code_end]
  \\ `bc_length = bc.instr_length` by METIS_TAC [bc_inv_def]
  \\ FULL_SIMP_TAC std_ss [WRITE_CODE_EQ_WRITE_BYTECODE]
  \\ `BC_JUMPS_OK bc` by
    (FULL_SIMP_TAC std_ss [bc_inv_def,BC_JUMPS_OK_def,BC_CODE_OK_def])
  \\ Q.ABBREV_TAC `ps = MAP getSym (sexp2list params)`
  \\ `?y. BC_ev T (sexp2term body,MAP ssVAR (REVERSE ps),bc.code_end,bc) y` by METIS_TAC [BC_ev_TOTAL,bc_inv_def]
  \\ IMP_RES_TAC BC_ev_fun_CONSTS
  \\ IMP_RES_TAC bc_inv_WRITE_BYTECODE
  \\ FULL_SIMP_TAC (srw_ss()) [WRITE_BYTECODE_code_end]
  \\ REV_FULL_SIMP_TAC bool_ss []
  \\ MATCH_MP_TAC WRITE_BYTECODE_code \\ ASM_SIMP_TAC std_ss [])
  |> SIMP_RULE std_ss [LET_DEF];

val bc_inv_BC_ONLY_COMPILE = store_thm("bc_inv_BC_ONLY_COMPILE",
  ``bc_inv bc ==> bc_inv (BC_ONLY_COMPILE (MAP getSym (sexp2list params),sexp2term body,bc))``,
  ASM_SIMP_TAC std_ss [mc_only_compile_thm]);

val mc_compile_inst_thm = prove(
  ``bc_inv bc /\ (FUN_LOOKUP bc.compiled (getSym fname) = NONE) ==>
    let bc5 = BC_COMPILE (getSym fname,MAP getSym (sexp2list params),sexp2term body,bc) in
      mc_compile_inst_pre (body,x1,x2,x3,x4,bc_state_tree bc,
         params::fname::xs,bc.consts,BC_CODE (bc.code,bc.code_end),ok) /\
      (mc_compile_inst (body,x1,x2,x3,x4,bc_state_tree bc,
         params::fname::xs,bc.consts,BC_CODE (bc.code,bc.code_end),ok) =
         (Sym "NIL",Sym "NIL",Sym "NIL",Sym "NIL",Sym "T",
           bc_state_tree bc5,xs,bc5.consts,BC_CODE (bc5.code,bc5.code_end),ok)) /\ bc_inv bc5``,
  SIMP_TAC std_ss [LET_DEF,mc_compile_inst_def,mc_compile_inst_pre_def,HD,TL,SFIX_THM] \\ STRIP_TAC
  \\ IMP_RES_TAC mc_check_exists_thm \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [`body`,`ok`])
  \\ ASM_SIMP_TAC std_ss [bc_state_tree_def,CDR_def,isDot_def]
  \\ STRIP_ASSUME_TAC (UNDISCH (Q.INST [`x0`|->`y0`,`x1`|->`Sym "NIL"`,`ff`|->`getSym fname`,
       `code`|->`BC_CODE (bc.code,bc.code_end)`]
       (Q.INST [`fname`|->`ff`] (SIMP_RULE std_ss [] mc_store_fun_thm))))
  \\ FULL_SIMP_TAC std_ss [code_ptr_def,GSYM bc_state_tree_def,LENGTH_MAP]
  \\ FULL_SIMP_TAC std_ss [mc_only_compile_thm,NOT_CONS_NIL,LENGTH_MAP]
  \\ FULL_SIMP_TAC std_ss [BC_COMPILE_def,LET_DEF,LENGTH_MAP]
  \\ Q.PAT_ABBREV_TAC `bcA = BC_STORE_COMPILED bc (getSym fname) zzz`
  \\ `(bc.code = bcA.code) /\ (bc.code_end = bcA.code_end) /\
      (bc.consts = bcA.consts) /\ bc_inv bcA` by
    (FULL_SIMP_TAC std_ss [bc_inv_def,BC_CODE_OK_def] \\ Q.UNABBREV_TAC `bcA`
     \\ FULL_SIMP_TAC (srw_ss()) [BC_STORE_COMPILED_def] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [mc_only_compile_thm,NOT_CONS_NIL,LENGTH_MAP])
  |> SIMP_RULE std_ss [LET_DEF];

val bc_inv_BC_COMPILE = save_thm("bc_inv_BC_COMPILE",
  mc_compile_inst_thm |> UNDISCH |> CONJUNCT2 |> DISCH_ALL);

val X64_LISP_COMPILE_AUX = let
  val th = MATCH_MP APPEND_NORMAL_RET (Q.INST [`qs`|->`q::qs`] mc_compile_inst_spec)
  val def_name = "abbrev_code_for_compile_inst"
  val th = abbrev_code (th,def_name)
  in th end

val X64_LISP_COMPILE_INST = save_thm("X64_LISP_COMPILE_INST",let
  val th = X64_LISP_COMPILE_AUX
  val th = Q.INST [`x0`|->`body`,`x5`|->`bc_state_tree bc`,
                   `xs`|->`params::fname::xs`,
                   `xs1`|->`bc.consts`,
                   `code`|->`BC_CODE (bc.code,bc.code_end)`] th
           |> DISCH ``bc_inv bc /\ (FUN_LOOKUP bc.compiled (getSym fname) = NONE)``
           |> SIMP_RULE std_ss [mc_compile_inst_thm,LET_DEF,SEP_CLAUSES]
           |> RW [GSYM SPEC_MOVE_COND]
  in th end);

val mc_compile_inst_thm_alt = prove(
  ``bc_inv bc /\ ~(FUN_LOOKUP bc.compiled (getSym fname) = NONE) ==>
    let bc5 = BC_FAIL bc in
      mc_compile_inst_pre (body,x1,x2,x3,x4,bc_state_tree bc,
         params::fname::xs,bc.consts,BC_CODE (bc.code,bc.code_end),ok) /\
      (mc_compile_inst (body,x1,x2,x3,x4,bc_state_tree bc,
         params::fname::xs,bc.consts,BC_CODE (bc.code,bc.code_end),ok) =
         (Sym "NIL",Sym "NIL",Sym "NIL",Sym "NIL",Sym "NIL",
           bc_state_tree bc5,xs,bc5.consts,BC_CODE (bc5.code,bc5.code_end),F)) /\ bc_inv bc5``,
  SIMP_TAC std_ss [LET_DEF,mc_compile_inst_def,mc_compile_inst_pre_def,HD,TL,SFIX_THM] \\ STRIP_TAC
  \\ IMP_RES_TAC mc_check_exists_thm_alt
  \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [`body`,`ok`])
  \\ FULL_SIMP_TAC (srw_ss()) [bc_state_tree_def,CDR_def,BC_FAIL_def,isDot_def]
  \\ FULL_SIMP_TAC (srw_ss()) [bc_inv_def,BC_CODE_OK_def] \\ METIS_TAC [])
  |> SIMP_RULE std_ss [LET_DEF];

val X64_LISP_COMPILE_INST_FAIL = save_thm("X64_LISP_COMPILE_INST_FAIL",let
  val th = X64_LISP_COMPILE_AUX
  val th = Q.INST [`x0`|->`body`,`x5`|->`bc_state_tree bc`,
                   `xs`|->`params::fname::xs`,
                   `xs1`|->`bc.consts`,
                   `code`|->`BC_CODE (bc.code,bc.code_end)`] th
           |> DISCH ``bc_inv bc /\ ~(FUN_LOOKUP bc.compiled (getSym fname) = NONE)``
           |> SIMP_RULE std_ss [mc_compile_inst_thm_alt,LET_DEF,SEP_CLAUSES]
           |> RW [GSYM SPEC_MOVE_COND]
  in th end);

val (mc_compile_for_eval_spec,mc_compile_for_eval_def,mc_compile_for_eval_pre_def) = compile "x64" ``
  mc_compile_for_eval (x0:SExp,x1,x2:SExp,x3:SExp,x4:SExp,x5,xs,xs1,code) =
    (* exp to evaluate in x0 *)
    let x2 = x0 in
    (* push code ptr *)
    let x0 = Val (code_ptr code) in
    let xs = x0::xs in
    (* compile with no params *)
    let x0 = Sym "NIL"in
    let (x0,x1,x2,x3,x4,x5,xs,xs1,code) = mc_only_compile (x0,x1,x2,x3,x4,x5,xs,xs1,code) in
    let x0 = HD xs in
    let xs = TL xs in
    (* call generated code *)
    let x2 = x0 in
    let x0 = Sym "NIL"in
      (x0,x1,x2,x3,x4,x5,xs,xs1,code)``;

val mc_compile_for_eval_thm = store_thm("mc_compile_for_eval_thm",
  ``bc_inv bc ==>
    let bc2 = BC_ONLY_COMPILE ([],sexp2term body,bc) in
      mc_compile_for_eval_pre
        (body,x1,x2,x3,x4,
         bc_state_tree bc,xs,bc.consts,BC_CODE (bc.code,bc.code_end)) /\
      (mc_compile_for_eval
         (body,x1,x2,x3,x4,
          bc_state_tree bc,xs,bc.consts,BC_CODE (bc.code,bc.code_end)) =
       (Sym "NIL",Sym "NIL",Val bc.code_end,Sym "NIL",Sym "T",bc_state_tree bc2,
        xs,bc2.consts,BC_CODE (bc2.code,bc2.code_end))) /\
      bc_inv bc2``,
  SIMP_TAC std_ss [mc_compile_for_eval_def,mc_compile_for_eval_pre_def,
    LET_DEF,GSYM list2sexp_def] \\ STRIP_TAC
  \\ IMP_RES_TAC (Q.INST [`params`|->`Sym "NIL"`] mc_only_compile_thm
                  |> SIMP_RULE std_ss [sexp2list_def,MAP])
  \\ FULL_SIMP_TAC std_ss [MAP,HD,TL]
  \\ FULL_SIMP_TAC std_ss [list2sexp_def,NOT_CONS_NIL,code_ptr_def,HD,TL])
  |> SIMP_RULE std_ss [LET_DEF];

val X64_LISP_COMPILE_FOR_EVAL = save_thm("X64_LISP_COMPILE_FOR_EVAL",let
  val th = mc_compile_for_eval_spec
  val th = Q.INST [`x0`|->`body`,`x5`|->`bc_state_tree bc`,
                   `xs1`|->`bc.consts`,
                   `code`|->`BC_CODE (bc.code,bc.code_end)`] th
           |> SIMP_RULE std_ss [UNDISCH mc_compile_for_eval_thm,LET_DEF,SEP_CLAUSES]
           |> DISCH_ALL |> RW [GSYM SPEC_MOVE_COND]
  in th end);


(* reload all primitive ops with ddd as a variable *)

val _ = let
  val thms = DB.match [] ``SPEC X64_MODEL``
  val thms = filter (can (find_term (can (match_term ``zLISP``))) o car o concl)
                    (map (#1 o #2) thms)
  val _ = map (fn th => add_compiled [th] handle e => ()) thms
  in () end;


(*
(* btree lookup, i.e. const lookup *)

val (_,mc_btree_lookup_def,mc_btree_lookup_pre_def) = compile "x64" ``
  mc_btree_lookup (x0,x1) =
    if x0 = Val 0 then let x0 = CAR x1 in let x1 = Sym "NIL" in (x0,x1) else
    if x0 = Val 1 then let x0 = CAR x1 in let x1 = Sym "NIL" in (x0,x1) else
      let x1 = CDR x1 in
        if EVEN (getVal x0) then
          let x0 = Val (getVal x0 DIV 2) in
          let x1 = CAR x1 in
            mc_btree_lookup (x0,x1)
        else
          let x0 = Val (getVal x0 DIV 2) in
          let x1 = CDR x1 in
            mc_btree_lookup (x0,x1)``;

val mc_btree_lookup_thm = prove(
  ``!n xs. n < LENGTH xs ==>
      mc_btree_lookup_pre (Val (n+1),list2btree xs) /\
      (mc_btree_lookup (Val (n+1),list2btree xs) = (EL n xs,Sym "NIL"))``,
  completeInduct_on `n` \\ NTAC 2 STRIP_TAC
  \\ Cases_on `n = 0` \\ ASM_SIMP_TAC std_ss [Once mc_btree_lookup_def,Once mc_btree_lookup_pre_def,LET_DEF] THEN1
   (Cases_on `xs` \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ SIMP_TAC std_ss [list2btree_def,CAR_def,EL,HD,isDot_def])
  \\ `~(n + 1 < 2)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC (srw_ss()) [EVEN,GSYM ADD1,getVal_def,isVal_def]
  \\ Cases_on `n` \\ FULL_SIMP_TAC std_ss [EVEN]
  \\ SIMP_TAC std_ss [ADD1,GSYM ADD_ASSOC]
  \\ SIMP_TAC std_ss [(SIMP_RULE std_ss [] (Q.SPEC `2` ADD_DIV_ADD_DIV))
       |> RW1 [ADD_COMM] |> Q.SPEC `1` |> SIMP_RULE std_ss []]
  \\ SIMP_TAC std_ss [RW[ADD1]EL]
  \\ Cases_on `xs` \\ FULL_SIMP_TAC std_ss [LENGTH,TL]
  \\ SIMP_TAC std_ss [list2btree_def,CAR_def,EL,HD,CDR_def,isDot_def]
  \\ Cases_on `t = []` \\ FULL_SIMP_TAC std_ss [LENGTH,CDR_def,CAR_def,isDot_def]
  \\ `n' DIV 2 < SUC n'` by (ASM_SIMP_TAC std_ss [DIV_LT_X] \\ DECIDE_TAC)
  \\ IMP_RES_TAC DIV_LESS_LENGTH_SPLIT_LIST
  \\ Cases_on `EVEN n'` \\ FULL_SIMP_TAC std_ss []
  \\ RES_TAC \\ ASM_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ ASM_SIMP_TAC std_ss [Once EL_SPLIT_LIST] \\ METIS_TAC []);

val (mc_const_lookup_spec,mc_const_lookup_def,mc_const_lookup_pre_def) = compile "x64" ``
  mc_const_lookup (x0:SExp,x1:SExp,x5:SExp) =
    let x0 = LISP_ADD x0 (Val 1) in
    let x1 = CAR x5 in
    let x1 = CDR x1 in
    let (x0,x1) = mc_btree_lookup (x0,x1) in
      (x0,x1,x5)``

val mc_const_lookup_thm = prove(
  ``!n bc x1.
      n < LENGTH bc.consts ==>
      mc_const_lookup_pre (Val n,x1,bc_state_tree bc) /\
      (mc_const_lookup (Val n,x1,bc_state_tree bc) =
         (EL n bc.consts,Sym "NIL",bc_state_tree bc))``,
  ASM_SIMP_TAC std_ss [mc_const_lookup_def,mc_const_lookup_pre_def,LET_DEF,
     isVal_def,LISP_ADD_def,getVal_def,bc_state_tree_def,CAR_def,isDot_def]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC mc_btree_lookup_thm
  \\ ASM_SIMP_TAC std_ss [const_tree_def,isDot_def,CDR_def]);

val X64_BYTECODE_LOOKUP = save_thm("X64_BYTECODE_LOOKUP",
  mc_const_lookup_spec
  |> Q.INST [`x0`|->`Val n`,`x5`|->`bc_state_tree bc`]
  |> DISCH ``n < LENGTH bc.consts``
  |> SIMP_RULE std_ss [mc_const_lookup_thm,LET_DEF,SEP_CLAUSES]
  |> RW [GSYM SPEC_MOVE_COND]);
*)


(* implementation of iCALL_SYM (and iJUMP_SYM) *)

val (_,mc_fundef_lookup_def,mc_fundef_lookup_pre_def) = compile "x64" ``
  mc_fundef_lookup (x0,x1,x2,x3) =
    if ~(isDot x1) then (x0,x1,x2,x3) else
      let x0 = CAR x1 in
      let x1 = CDR x1 in
        if x0 = x2 then
          let x1 = CAR x1 in
          let x0 = CDR x1 in
          let x1 = CAR x1 in
            if x0 = x3 then (x0,x1,x2,x3) else
              let x1 = Sym "NIL" in
                (x0,x1,x2,x3)
        else
          let x1 = CDR x1 in
            mc_fundef_lookup (x0,x1,x2,x3)``

val (mc_fundef_lookup_full_spec,mc_fundef_lookup_full_def,mc_fundef_lookup_full_pre_def) = compile "x64" ``
  mc_fundef_lookup_full (x0,x1:SExp,x2,x3,x5,(xs:SExp list),io) =
    let x1 = CDR x5 in
    let x2 = x0 in
    let x3 = HD xs in
    let xs = TL xs in
    let (x0,x1,x2,x3) = mc_fundef_lookup (x0,x1,x2,x3) in
    let x0 = HD xs in
    let xs = TL xs in
    let x2 = x1 in
      if isVal x1 then (x0,x1,x2,x3,x5,xs,io) else
        let x0 = x2 in
        let io = IO_WRITE io (sexp2string x0) in
        let io = IO_WRITE io "\n" in
        let x0 = no_such_function x0 in
          (x0,x1,x2,x3,x5,xs,io)``

val mc_fundef_lookup_thm = prove(
  ``!xs y fc.
      (FUN_LOOKUP xs fc = SOME (i,m)) ==>
      ?y0.
        mc_fundef_lookup_pre (y,list2sexp (flat_alist xs),Sym fc,Val k) /\
        (mc_fundef_lookup (y,list2sexp (flat_alist xs),Sym fc,Val k) =
           (y0,if k = m then Val i else Sym "NIL",Sym fc,Val k))``,
  Induct \\ SIMP_TAC std_ss [flat_alist_def,list2sexp_def]
  \\ ONCE_REWRITE_TAC [mc_fundef_lookup_def,mc_fundef_lookup_pre_def]
  \\ SIMP_TAC std_ss [isDot_def,FUN_LOOKUP_def,lookup_result_def]
  \\ Cases_on `h` \\ Cases_on `r` \\ SIMP_TAC (srw_ss()) [isDot_def,FUN_LOOKUP_def,
       lookup_result_def,LET_DEF,flat_alist_def,list2sexp_def,CAR_def,CDR_def,
       markerTheory.Abbrev_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `q = fc` \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC []);

val mc_fundef_lookup_full_thm = prove(
  ``bc_inv bc /\ (FUN_LOOKUP bc.compiled fc = SOME (i,m)) ==>
    mc_fundef_lookup_full_pre (Sym fc,x1,x2,x3,bc_state_tree bc,Val m::x::xs,io) /\
    (mc_fundef_lookup_full (Sym fc,x1,x2,x3,bc_state_tree bc,Val m::x::xs,io) =
       (x,Val i,Val i,Val m,bc_state_tree bc,xs,io))``,
  SIMP_TAC std_ss [mc_fundef_lookup_full_def,mc_fundef_lookup_full_pre_def,LET_DEF,TL,HD]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC mc_fundef_lookup_thm
  \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [`Sym fc`,`m`])
  \\ FULL_SIMP_TAC std_ss [bc_state_tree_def,isDot_def,CDR_def,NOT_CONS_NIL,isVal_def]);

val X64_BYTECODE_CALL_SYM = save_thm("X64_BYTECODE_CALL_SYM",
  mc_fundef_lookup_full_spec
  |> Q.INST [`x0`|->`Sym fc`,`x5`|->`bc_state_tree bc`,`xs`|->`Val m::x::xs`]
  |> DISCH ``bc_inv bc /\ (FUN_LOOKUP bc.compiled fc = SOME (i,m))``
  |> SIMP_RULE std_ss [mc_fundef_lookup_full_thm]
  |> UNDISCH
  |> CONV_RULE (REWRITE_CONV [UNDISCH mc_fundef_lookup_full_thm])
  |> SIMP_RULE std_ss [LET_DEF]
  |> DISCH_ALL |> SIMP_RULE (std_ss++sep_cond_ss) [GSYM SPEC_MOVE_COND]
  |> (fn th => SPEC_COMPOSE_RULE [th,X64_LISP_JUMP_TO_CODE])
  |> SIMP_RULE std_ss [isVal_def,getVal_def,SEP_CLAUSES]);

val X64_BYTECODE_JUMP_SYM = save_thm("X64_BYTECODE_JUMP_SYM",
  mc_fundef_lookup_full_spec
  |> Q.INST [`x0`|->`Sym fc`,`x5`|->`bc_state_tree bc`,`xs`|->`Val m::x::xs`]
  |> DISCH ``bc_inv bc /\ (FUN_LOOKUP bc.compiled fc = SOME (i,m))``
  |> SIMP_RULE std_ss [mc_fundef_lookup_full_thm]
  |> UNDISCH
  |> CONV_RULE (REWRITE_CONV [UNDISCH mc_fundef_lookup_full_thm])
  |> SIMP_RULE std_ss [LET_DEF]
  |> DISCH_ALL |> SIMP_RULE (std_ss++sep_cond_ss) [GSYM SPEC_MOVE_COND]
  |> (fn th => SPEC_COMPOSE_RULE [th,X64_LISP_JUMP_TO_CODE_NO_RET])
  |> SIMP_RULE std_ss [isVal_def,getVal_def,SEP_CLAUSES]);

val _ = export_theory();
