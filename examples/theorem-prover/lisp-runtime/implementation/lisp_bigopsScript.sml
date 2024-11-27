open HolKernel Parse boolLib bossLib; val _ = new_theory "lisp_bigops";
val _ = ParseExtras.temp_loose_equality()
open lisp_codegenTheory lisp_initTheory lisp_symbolsTheory lisp_sexpTheory
open lisp_invTheory lisp_parseTheory lisp_opsTheory;

open wordsTheory arithmeticTheory wordsLib listTheory pred_setTheory pairTheory;
open combinTheory finite_mapTheory addressTheory helperLib;
open set_sepTheory bitTheory fcpTheory stringTheory;

open compilerLib decompilerLib codegenLib;

val _ = let
  val thms = DB.match [] ``SPEC X64_MODEL``
  val thms = filter (can (find_term (can (match_term ``zLISP``))) o car o concl)
                    (map (#1 o #2) thms)
  val _ = map (fn th => add_compiled [th] handle e => ()) thms
  in () end;

(* --- *)

infix \\
val op \\ = op THEN;
val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

(*
val _ = set_echo 3;
*)

(* sex2string *)

val (_,lisp_sexp2string_aux_extra_def,lisp_sexp2string_aux_extra_pre_def) = compile "x64" ``
  lisp_sexp2string_aux_extra (x0,x2,xs:SExp list,io) =
    if x2 = Sym "NIL" then (x0,x2,xs,io) else
      let x0 = Sym "T" in
      let xs = x0::xs in
      let io = IO_WRITE io "(" in
        (x0,x2,xs,io)``

val (_,lisp_sexp2string_aux_inner_def,lisp_sexp2string_aux_inner_pre_def) = compile "x64" ``
  lisp_sexp2string_aux_inner (x0,x1,x2,x3:SExp,x4:SExp,x5:SExp,xs:SExp list,io) =
    if isVal x0 then
      let (x0,x1,x2,x3,io) = (Sym "NIL",Sym "NIL",Sym "NIL",Sym "NIL", IO_WRITE io (num2str (getVal x0))) in
        (x0,x1,x2,x3,x4,x5,xs,io)
    else if isSym x0 then
      let (x0,x1,x2,x3,io) = (Sym "NIL",Sym "NIL",Sym "NIL",Sym "NIL", IO_WRITE io (sym2str (getSym x0))) in
        (x0,x1,x2,x3,x4,x5,xs,io)
    else
      let x1 = x0 in
      let x0 = LISP_TEST (isQuote x0) in
        if ~(x0 = Sym "NIL") then
          let io = IO_WRITE io "'" in
          let x0 = CDR x1 in
          let x0 = CAR x0 in
          let x2 = Sym "T" in
            lisp_sexp2string_aux_inner (x0,x1,x2,x3,x4,x5,xs,io)
        else
          let (x0,x2,xs,io) = lisp_sexp2string_aux_extra (x0,x2,xs,io) in
          let x0 = CDR x1 in
          let xs = x0::xs in
          let x0 = Val 0 in
          let xs = x0::xs in
          let x0 = CAR x1 in
          let x2 = Sym "T" in
            lisp_sexp2string_aux_inner (x0,x1,x2,x3,x4,x5,xs,io)``

val (_,lisp_sexp2string_aux_space_def,lisp_sexp2string_aux_space_pre_def) = compile "x64" ``
  lisp_sexp2string_aux_space (x0,io) =
    if ~(isDot x0) then let io = IO_WRITE io " . " in (x0,io) else
      let x0 = LISP_TEST (isQuote x0) in
        if ~(x0 = Sym "NIL") then
          let io = IO_WRITE io " . " in (x0,io)
        else
          let io = IO_WRITE io " " in (x0,io)``

val (_,lisp_sexp2string_aux_loop_def,lisp_sexp2string_aux_loop_pre_def) = compile "x64" ``
  lisp_sexp2string_aux_loop (x0,x1,x2,x3,x4,x5,xs,io) =
    if x3 = Sym "NIL" then
      let (x0,x1,x2,x3,x4,x5,xs,io) = lisp_sexp2string_aux_inner (x0,x1,x2,x3,x4,x5,xs,io) in
      let x3 = Sym "T" in
        lisp_sexp2string_aux_loop (x0,x1,x2,x3,x4,x5,xs,io)
    else
      let x0 = HD xs in
      let xs = TL xs in
        if x0 = Sym "NIL" then (x0,x1,x2,x3,x4,x5,xs,io) else
        if x0 = Sym "T" then
          let io = IO_WRITE io ")" in
            lisp_sexp2string_aux_loop (x0,x1,x2,x3,x4,x5,xs,io)
        else
          let x0 = HD xs in
          let xs = TL xs in
            if x0 = Sym "NIL" then
              lisp_sexp2string_aux_loop (x0,x1,x2,x3,x4,x5,xs,io)
            else
              let x1 = x0 in
              let (x0,io) = lisp_sexp2string_aux_space (x0,io) in
              let x3 = Sym "NIL" in
              let x2 = Sym "NIL" in
              let x0 = x1 in
                lisp_sexp2string_aux_loop (x0,x1,x2,x3,x4,x5,xs,io)``

val (lisp_sexp2string_spec,lisp_sexp2string_def,lisp_sexp2string_pre_def) = compile "x64" ``
  lisp_sexp2string (x0,x1,x2,x3,x4,x5,xs,io) =
    let xs = x0::xs in
    let xs = x1::xs in
    let xs = x2::xs in
    let xs = x3::xs in
    let x2 = Sym "T" in
    let x3 = Sym "NIL" in
    let xs = x3::xs in
    let (x0,x1,x2,x3,x4,x5,xs,io) = lisp_sexp2string_aux_loop (x0,x1,x2,x3,x4,x5,xs,io) in
    let x3 = HD xs in
    let xs = TL xs in
    let x2 = HD xs in
    let xs = TL xs in
    let x1 = HD xs in
    let xs = TL xs in
    let x0 = HD xs in
    let xs = TL xs in
      (x0,x1,x2,x3,x4,x5,xs,io)``

val T_NOT_NIL = CONJ (EVAL ``Sym "NIL" = Sym "T"``) (EVAL ``Sym "T" = Sym "NIL"``)

val LISP_TEST_EQ_NIL = prove(
  ``!b. (LISP_TEST b = Sym "NIL") = ~b``,
  Cases \\ EVAL_TAC);

val lisp_sexp2string_aux_loop_thm = prove(
  ``!x0 x1 xs io b.
      ?y0 y1 y2.
        (lisp_sexp2string_aux_loop (x0,x1,LISP_TEST b,Sym "NIL",x4,x5,xs,io) =
         lisp_sexp2string_aux_loop (y0,y1,y2,Sym "T",x4,x5,xs,IO_WRITE io (sexp2string_aux (x0,b)))) /\
        (lisp_sexp2string_aux_loop_pre (x0,x1,LISP_TEST b,Sym "NIL",x4,x5,xs,io) =
         lisp_sexp2string_aux_loop_pre (y0,y1,y2,Sym "T",x4,x5,xs,IO_WRITE io (sexp2string_aux (x0,b))))``,
  HO_MATCH_MP_TAC SExp_print_induct \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [Once lisp_sexp2string_aux_loop_def]
  \\ SIMP_TAC std_ss [Once lisp_sexp2string_aux_loop_pre_def]
  \\ ONCE_REWRITE_TAC [lisp_sexp2string_aux_inner_def]
  \\ SIMP_TAC std_ss [Once lisp_sexp2string_aux_inner_pre_def]
  \\ SIMP_TAC std_ss [LET_DEF]
  \\ REVERSE (Cases_on `x0`) \\ ASM_SIMP_TAC std_ss [isSym_def,isVal_def,LET_DEF]
  THEN1 (SIMP_TAC std_ss [isVal_def,isSym_def,LET_DEF,getSym_def,
          sexp2string_aux_def] \\ METIS_TAC [])
  THEN1 (SIMP_TAC std_ss [isVal_def,isSym_def,LET_DEF,getSym_def,getVal_def,
          sexp2string_aux_def] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [isDot_def,CAR_def,CDR_def]
  \\ Cases_on `isQuote (Dot S' S0)` THEN1
   (FULL_SIMP_TAC std_ss [LISP_TEST_def,EVAL ``Sym "T" = Sym "NIL"``]
    \\ Q.PAT_X_ASSUM `!x1.bbb` MP_TAC
    \\ SIMP_TAC std_ss [Once lisp_sexp2string_aux_loop_def]
    \\ SIMP_TAC std_ss [Once lisp_sexp2string_aux_loop_pre_def]
    \\ SIMP_TAC std_ss [LET_DEF]
    \\ STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`Dot S' S0`,`xs`,`IO_WRITE io "'"`,`T`])
    \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ Q.LIST_EXISTS_TAC [`y0`,`y1`,`y2`]
    \\ ONCE_REWRITE_TAC [sexp2string_aux_def]
    \\ ASM_SIMP_TAC std_ss [LIST_STRCAT_def,IO_WRITE_APPEND,APPEND,APPEND_NIL]
    \\ FULL_SIMP_TAC std_ss [isQuote_def,CDR_def,IO_WRITE_APPEND,APPEND])
  \\ ASM_SIMP_TAC std_ss [LISP_TEST_def]
  \\ REVERSE (Cases_on `b`) THEN1
   (FULL_SIMP_TAC std_ss [lisp_sexp2string_aux_extra_def]
    \\ Q.PAT_X_ASSUM `!x1.bbb` MP_TAC
    \\ Q.PAT_X_ASSUM `!x1.bbb` MP_TAC
    \\ SIMP_TAC std_ss [Once lisp_sexp2string_aux_loop_def]
    \\ SIMP_TAC std_ss [Once lisp_sexp2string_aux_loop_pre_def]
    \\ SIMP_TAC std_ss [LET_DEF]
    \\ STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`Dot S' S0`,`Val 0::S0::xs`,`io`,`T`])
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [LISP_TEST_def]
    \\ SIMP_TAC std_ss [Once lisp_sexp2string_aux_loop_def,LET_DEF,T_NOT_NIL]
    \\ SIMP_TAC std_ss [Once lisp_sexp2string_aux_loop_pre_def,LET_DEF,T_NOT_NIL]
    \\ SIMP_TAC std_ss [HD,TL,SExp_distinct]
    \\ Cases_on `S0 = Sym "NIL"` \\ ASM_SIMP_TAC std_ss [NOT_CONS_NIL]
    THEN1 (FULL_SIMP_TAC std_ss [sexp2string_aux_def,LET_DEF,
             LIST_STRCAT_def,APPEND,APPEND_NIL] \\ METIS_TAC [])
    \\ SIMP_TAC std_ss [lisp_sexp2string_aux_space_def,LET_DEF,IO_WRITE_APPEND]
    \\ REVERSE (Cases_on `isDot S0`) \\ ASM_SIMP_TAC std_ss [] THEN1
     (Q.PAT_X_ASSUM `!x1.bbb` (MP_TAC o Q.SPECL [`S0`,`xs`,`IO_WRITE io (STRCAT (sexp2string_aux (S',T)) " . ")`,`F`])
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [IO_WRITE_APPEND,NOT_CONS_NIL,
           sexp2string_aux_def,LET_DEF,LIST_STRCAT_def,APPEND,APPEND_NIL]
      \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND] \\ METIS_TAC [])
    \\ ASM_SIMP_TAC std_ss [LISP_TEST_EQ_NIL]
    \\ Cases_on `isQuote S0` \\ FULL_SIMP_TAC std_ss [LISP_TEST_def]
    THEN1
     (Q.PAT_X_ASSUM `!x1.bbb` (MP_TAC o Q.SPECL [`S0`,`xs`,`IO_WRITE io (STRCAT (sexp2string_aux (S',T)) " . ")`,`F`])
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [IO_WRITE_APPEND,NOT_CONS_NIL,
           sexp2string_aux_def,LET_DEF,LIST_STRCAT_def,APPEND,APPEND_NIL]
      \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND] \\ METIS_TAC [])
    THEN1
     (Q.PAT_X_ASSUM `!x1.bbb` (MP_TAC o Q.SPECL [`S0`,`xs`,`IO_WRITE io (STRCAT (sexp2string_aux (S',T)) " ")`,`F`])
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [IO_WRITE_APPEND,NOT_CONS_NIL,
           sexp2string_aux_def,LET_DEF,LIST_STRCAT_def,APPEND,APPEND_NIL]
      \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND] \\ METIS_TAC []))
  THEN1
   (FULL_SIMP_TAC std_ss [lisp_sexp2string_aux_extra_def,T_NOT_NIL]
    \\ Q.PAT_X_ASSUM `!x1.bbb` MP_TAC
    \\ Q.PAT_X_ASSUM `!x1.bbb` MP_TAC
    \\ SIMP_TAC std_ss [Once lisp_sexp2string_aux_loop_def]
    \\ SIMP_TAC std_ss [Once lisp_sexp2string_aux_loop_pre_def]
    \\ SIMP_TAC std_ss [LET_DEF]
    \\ STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`Dot S' S0`,`Val 0::S0::Sym"T"::xs`,`IO_WRITE io "("`,`T`])
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [LISP_TEST_def]
    \\ SIMP_TAC std_ss [Once lisp_sexp2string_aux_loop_def,LET_DEF,T_NOT_NIL]
    \\ SIMP_TAC std_ss [Once lisp_sexp2string_aux_loop_pre_def,LET_DEF,T_NOT_NIL]
    \\ SIMP_TAC std_ss [HD,TL,SExp_distinct]
    \\ Cases_on `S0 = Sym "NIL"` \\ ASM_SIMP_TAC std_ss []
    THEN1 (SIMP_TAC std_ss [Once lisp_sexp2string_aux_loop_def]
           \\ SIMP_TAC std_ss [Once lisp_sexp2string_aux_loop_pre_def]
           \\ FULL_SIMP_TAC std_ss [sexp2string_aux_def,LET_DEF,TL,NOT_CONS_NIL,
                LIST_STRCAT_def,APPEND,APPEND_NIL,T_NOT_NIL,HD,IO_WRITE_APPEND]
           \\ METIS_TAC [])
    \\ SIMP_TAC std_ss [lisp_sexp2string_aux_space_def,LET_DEF,IO_WRITE_APPEND]
    \\ REVERSE (Cases_on `isDot S0`) \\ ASM_SIMP_TAC std_ss [] THEN1
     (Q.PAT_X_ASSUM `!x1.bbb` (MP_TAC o Q.SPECL [`S0`,`Sym "T"::xs`,`IO_WRITE io (STRCAT "(" (STRCAT (sexp2string_aux (S',T)) " . "))`,`F`])
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
      \\ SIMP_TAC std_ss [Once lisp_sexp2string_aux_loop_def]
      \\ SIMP_TAC std_ss [Once lisp_sexp2string_aux_loop_pre_def]
      \\ FULL_SIMP_TAC std_ss [sexp2string_aux_def,LET_DEF,TL,NOT_CONS_NIL,
                LIST_STRCAT_def,APPEND,APPEND_NIL,T_NOT_NIL,HD,IO_WRITE_APPEND]
      \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
      \\ METIS_TAC [])
    \\ ASM_SIMP_TAC std_ss [LISP_TEST_EQ_NIL]
    \\ Cases_on `isQuote S0` \\ FULL_SIMP_TAC std_ss [LISP_TEST_def]
    THEN1
     (Q.PAT_X_ASSUM `!x1.bbb` (MP_TAC o Q.SPECL [`S0`,`Sym "T"::xs`,`IO_WRITE io (STRCAT "(" (STRCAT (sexp2string_aux (S',T)) " . "))`,`F`])
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
      \\ SIMP_TAC std_ss [Once lisp_sexp2string_aux_loop_def]
      \\ SIMP_TAC std_ss [Once lisp_sexp2string_aux_loop_pre_def]
      \\ FULL_SIMP_TAC std_ss [sexp2string_aux_def,LET_DEF,TL,NOT_CONS_NIL,
                LIST_STRCAT_def,APPEND,APPEND_NIL,T_NOT_NIL,HD,IO_WRITE_APPEND]
      \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
      \\ METIS_TAC [])
    THEN1
     (Q.PAT_X_ASSUM `!x1.bbb` (MP_TAC o Q.SPECL [`S0`,`Sym "T"::xs`,`IO_WRITE io (STRCAT "(" (STRCAT (sexp2string_aux (S',T)) " "))`,`F`])
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
      \\ SIMP_TAC std_ss [Once lisp_sexp2string_aux_loop_def]
      \\ SIMP_TAC std_ss [Once lisp_sexp2string_aux_loop_pre_def]
      \\ FULL_SIMP_TAC std_ss [sexp2string_aux_def,LET_DEF,TL,NOT_CONS_NIL,
                LIST_STRCAT_def,APPEND,APPEND_NIL,T_NOT_NIL,HD,IO_WRITE_APPEND]
      \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
      \\ METIS_TAC [])));

val lisp_sexp2string_thm = prove(
  ``!x0 x1 x2 x3 x4 x5 xs io.
      lisp_sexp2string_pre (x0,x1,x2,x3,x4,x5,xs,io) /\
      (lisp_sexp2string (x0,x1,x2,x3,x4,x5,xs,io) =
         (x0,x1,x2,x3,x4,x5,xs,IO_WRITE io (sexp2string x0)))``,
  SIMP_TAC std_ss [lisp_sexp2string_def,lisp_sexp2string_pre_def,LET_DEF]
  \\ NTAC 8 STRIP_TAC
  \\ STRIP_ASSUME_TAC (Q.SPECL [`x0`,`x1`,`Sym "NIL"::x3::x2::x1::x0::xs`,`io`,`T`] lisp_sexp2string_aux_loop_thm)
  \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC std_ss [LISP_TEST_def]
  \\ ONCE_REWRITE_TAC [lisp_sexp2string_aux_loop_def]
  \\ ASM_SIMP_TAC std_ss [HD,T_NOT_NIL,LET_DEF,TL,HD,sexp2string_def]
  \\ ONCE_REWRITE_TAC [lisp_sexp2string_aux_loop_pre_def]
  \\ ASM_SIMP_TAC std_ss [HD,T_NOT_NIL,LET_DEF,TL,HD,sexp2string_def]
  \\ ASM_SIMP_TAC std_ss [NOT_CONS_NIL]);



(* string2sexp

mem in x5
exp in x4
L_READ -- Sym "NIL"
L_COLLECT -- Sym "T"
L_RETURN -- Val 0

*)

val parse_task_def = Define `
  (parse_task L_READ = Sym "NIL") /\
  (parse_task (L_COLLECT x) = Sym "T") /\
  (parse_task (L_RETURN x) = Val 0)`;

val parse_task2_def = Define `
  (parse_task2 L_READ y = y) /\
  (parse_task2 (L_COLLECT x) y = x) /\
  (parse_task2 (L_RETURN x) y = x)`;

val parse_stack_def = Define `
  (parse_stack [] = [Sym "NIL"]) /\
  (parse_stack (L_CONS a::xs) = [Sym "CONS";a] ++ parse_stack xs) /\
  (parse_stack (L_STORE n::xs) = [Val n] ++ parse_stack xs) /\
  (parse_stack (L_STOP::xs) = [Sym "CAR"] ++ parse_stack xs) /\
  (parse_stack (L_DOT::xs) = [Sym "CDR"] ++ parse_stack xs) /\
  (parse_stack (L_QUOTE::xs) = [Sym "QUOTE"] ++ parse_stack xs)`;

val remove_parse_stack_thm = prove(
  ``!xs ys. (remove_parse_stack (parse_stack xs ++ ys) = ys)``,
  Induct \\ SIMP_TAC std_ss [remove_parse_stack_def,parse_stack_def,APPEND]
  \\ Cases \\ ASM_SIMP_TAC (srw_ss()) [remove_parse_stack_def,parse_stack_def,APPEND])

val (thm,lisp_token_def,lisp_token_pre_def) = compile "x64" ``
  lisp_token (io) =
    let (x0,x1,x2,x3,io) = (next_token1 (getINPUT io),next_token2 (getINPUT io),Sym "NIL", Sym "NIL",IO_INPUT_APPLY (SND o next_token) io) in
      (x0,x1,x2,x3,io)``

val (thm,lisp_syntaxerr_def,lisp_syntaxerr_pre_def) = compile "x64" ``
  lisp_syntaxerr (x0:SExp,xs) =
    let xs = remove_parse_stack xs in
    let x0 = Sym "NIL" in
      (x0,xs)``

val (thm,lisp_parse_lookup_def,lisp_parse_lookup_pre_def) = compile "x64" ``
  lisp_parse_lookup (x0,x2,x4) =
    if ~(isDot x4) then let x4 = Sym "NIL" in (x0,x2,x4) else
      let x2 = CAR x4 in
      let x4 = CDR x4 in
        if x0 = x2 then
          let x4 = CAR x4 in (x0,x2,x4)
        else
          let x4 = CDR x4 in lisp_parse_lookup (x0,x2,x4)``

val (_,lisp_parse_def,lisp_parse_pre_def) = compile "x64" ``
  lisp_parse (x0,x1,x2,x3,x4,x5,xs,io,xbp,amnt:num) =
    if x3 = Sym "NIL" then (* READ *)
      let (x0,x1,x2,x3,io) = lisp_token io in
        if x1 = Val 0 then
          let x3 = x1 in
          let x4 = x0 in
            lisp_parse (x0,x1,x2,x3,x4,x5,xs,io,xbp,amnt)
        else if x1 = Val 1 then
          if x0 = Val 0 then (* L_STOP *)
            let x3 = Sym "NIL" in
            let x0 = Sym "CAR" in
            let xs = x0::xs in
              lisp_parse (x0,x1,x2,x3,x4,x5,xs,io,xbp,amnt)
          else if x0 = Val 1 then (* L_DOT *)
            let x3 = Sym "NIL" in
            let x0 = Sym "CDR" in
            let xs = x0::xs in
              lisp_parse (x0,x1,x2,x3,x4,x5,xs,io,xbp,amnt)
          else if x0 = Val 3 then (* L_QUOTE *)
            let x3 = Sym "NIL" in
            let x0 = Sym "QUOTE" in
            let xs = x0::xs in
              lisp_parse (x0,x1,x2,x3,x4,x5,xs,io,xbp,amnt)
          else
            let x3 = Sym "T" in
            let x4 = Sym "NIL" in
              lisp_parse (x0,x1,x2,x3,x4,x5,xs,io,xbp,amnt)
        else if x1 = Val 3 then
          let x3 = Val 0 in
          let x1 = Val amnt in
            if getVal x0 < getVal x1 then
              let x1 = x0 in
              let x4 = EL (LENGTH xs + getVal x1 - xbp) xs in
                lisp_parse (x0,x1,x2,x3,x4,x5,xs,io,xbp,amnt)
            else
              let x4 = x5 in
              let (x0,x2,x4) = lisp_parse_lookup (x0,x2,x4) in
                lisp_parse (x0,x1,x2,x3,x4,x5,xs,io,xbp,amnt)
        else if x1 = Val 2 then
          let x3 = Sym "NIL" in
          let xs = x0::xs in
            lisp_parse (x0,x1,x2,x3,x4,x5,xs,io,xbp,amnt)
        else
          let (x0,xs) = lisp_syntaxerr (x0,xs) in
            (x0,x1,x2,x3,x4,x5,xs,io,xbp,amnt)
    else if x3 = Sym "T" then (* COLLECT *)
      let x0 = HD xs in
        if x0 = Sym "NIL" then
          let (x0,xs) = lisp_syntaxerr (x0,xs) in
            (x0,x1,x2,x3,x4,x5,xs,io,xbp,amnt)
        else
          let x0 = HD xs in
          let xs = TL xs in
            if x0 = Sym "CAR" then (* L_STOP *)
              let x3 = Val 0 in
                lisp_parse (x0,x1,x2,x3,x4,x5,xs,io,xbp,amnt)
            else if x0 = Sym "CONS" then (* L_CONS *)
              let x1 = HD xs in
              let xs = TL xs in
              let x1 = Dot x1 x4 in
              let x4 = x1 in
                lisp_parse (x0,x1,x2,x3,x4,x5,xs,io,xbp,amnt)
            else if x0 = Sym "CDR" then (* L_DOT *)
              let x4 = SAFE_CAR x4 in
              let x3 = Sym "T" in
                lisp_parse (x0,x1,x2,x3,x4,x5,xs,io,xbp,amnt)
            else
              let xs = x0::xs in
              let (x0,xs) = lisp_syntaxerr (x0,xs) in
                (x0,x1,x2,x3,x4,x5,xs,io,xbp,amnt)
    else (* RETURN *)
      let x0 = HD xs in
        if x0 = Sym "NIL" then
          let xs = TL xs in
          let x0 = x4 in
            (x0,x1,x2,x3,x4,x5,xs,io,xbp,amnt)
        else
          let x0 = HD xs in
            if x0 = Sym "QUOTE" then
              let xs = TL xs in
              let x1 = x4 in
              let x2 = Sym "NIL" in
              let x1 = Dot x1 x2 in
              let x0 = Dot x0 x1 in
              let x4 = x0 in
                lisp_parse (x0,x1,x2,x3,x4,x5,xs,io,xbp,amnt)
            else if isVal x0 then
              let xs = TL xs in
              let x1 = Val amnt in
                if getVal x0 < getVal x1 then
                  let x1 = x0 in
                  let x0 = x4 in
                  let xs = UPDATE_NTH (LENGTH xs + getVal x1 - xbp) x0 xs in
                    lisp_parse (x0,x1,x2,x3,x4,x5,xs,io,xbp,amnt)
                else
                  let x2 = x4 in
                  let x2 = Dot x2 x5 in
                  let x0 = Dot x0 x2 in
                  let x5 = x0 in
                    lisp_parse (x0,x1,x2,x3,x4,x5,xs,io,xbp,amnt)
            else
              let xs = x4::xs in
              let x0 = Sym "CONS" in
              let xs = x0::xs in
              let x3 = Sym "NIL" in
                lisp_parse (x0,x1,x2,x3,x4,x5,xs,io,xbp,amnt)``

val (_,lisp_pushes_def,lisp_pushes_pre_def) = compile "x64" ``
  lisp_pushes (x0:SExp,x1,xs) =
    if x1 = Val 0 then (x0,x1,xs) else
      let x1 = LISP_SUB x1 (Val 1) in
      let xs = x0::xs in
        lisp_pushes (x0,x1,xs)``

val (lisp_string2sexp_spec,lisp_string2sexp_def,lisp_string2sexp_pre_def) = compile "x64" ``
  lisp_string2sexp (x0,x1,x2,x3,x4,x5,xs,io,xbp:num,amnt) =
    let xs = x1::xs in
    let xs = x2::xs in
    let xs = x3::xs in
    let xs = x4::xs in
    let xs = x5::xs in
    let x3 = Sym "NIL" in
    let x5 = x3 in
    let x0 = x3 in
    let x1 = Val amnt in
    let (x0,x1,xs) = lisp_pushes (x0,x1,xs) in
    let xbp = LENGTH xs in
    let xs = x3::xs in
    let (x0,x1,x2,x3,x4,x5,xs,io,xbp,amnt) = lisp_parse (x0,x1,x2,x3,x4,x5,xs,io,xbp,amnt) in
    let x1 = Val amnt in
    let xs = DROP (getVal x1) xs in
    let x5 = HD xs in
    let xs = TL xs in
    let x4 = HD xs in
    let xs = TL xs in
    let x3 = HD xs in
    let xs = TL xs in
    let x2 = HD xs in
    let xs = TL xs in
    let x1 = HD xs in
    let xs = TL xs in
    let xbp = LENGTH xs in
      (x0,x1,x2,x3,x4,x5,xs,io,xbp,amnt)``

val lisp_mem_def = tDefine "lisp_mem" `
  lisp_mem x = if ~(isDot x) then (\x. Sym "NIL") else
                 (getVal (CAR x) =+ CAR (CDR x)) (lisp_mem (CDR (CDR x)))`
 (WF_REL_TAC `measure LSIZE`
  \\ SIMP_TAC std_ss [isDot_thm] \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [CDR_def,LSIZE_def] \\ Cases_on `b`
  \\ SIMP_TAC std_ss [CDR_def,LSIZE_def] \\ DECIDE_TAC)

val READ_L_STORE_NONE_IMP = prove(
  ``!h x. (READ_L_STORE h = SOME x) ==> (h = L_STORE x)``,
  Cases \\ SIMP_TAC (srw_ss()) [READ_L_STORE_def]);

val READ_L_CONS_NONE_IMP = prove(
  ``!h x. (READ_L_CONS h = SOME x) ==> (h = L_CONS x)``,
  Cases \\ SIMP_TAC (srw_ss()) [READ_L_CONS_def]);

val getINPUT_REPLACE_INPUT_IO = prove(
  ``!io x. getINPUT (REPLACE_INPUT_IO x io) = x``,
  Cases \\ EVAL_TAC \\ SIMP_TAC std_ss []);

val APPLY_REPLACE_INPUT_IO = prove(
  ``!io cs f. IO_INPUT_APPLY f (REPLACE_INPUT_IO cs io) =
              REPLACE_INPUT_IO (f cs) io``,
  Cases \\ SIMP_TAC std_ss [REPLACE_INPUT_IO_def,IO_INPUT_APPLY_def,getINPUT_def]);

val next_token_cases = prove(
  ``!cs. (next_token cs = ((z1,z2),cs3)) ==>
         ((z2 = Val 1) ==> (z1 = Val 0) \/ (z1 = Val 1) \/ (z1 = Val 2) \/ (z1 = Val 3)) /\
         ((z2 = Val 2) ==> isVal z1) /\
         ((z2 = Val 3) ==> isVal z1)``,
  HO_MATCH_MP_TAC next_token_ind \\ SIMP_TAC std_ss [next_token_def,LET_DEF] \\ STRIP_TAC
  THEN1 (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ NTAC 2 STRIP_TAC
  \\ `?xs1 xs2. read_while number_char cs "" = (xs1,xs2)` by METIS_TAC [PAIR]
  \\ `?ys1 ys2. str2sym (STRING c cs) = (ys1,ys2)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [] \\ Cases_on `c = #";"`
  \\ FULL_SIMP_TAC (srw_ss()) [EVAL ``space_char #";"``, EVAL ``number_char #";"``]
  \\ Cases_on `space_char c` \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [Once EQ_SYM_EQ] \\ SRW_TAC [] [isVal_def]);

val mem_list2sexp_def = Define `
  (mem_list2sexp [] = Sym "NIL") /\
  (mem_list2sexp ((n,x)::xs) = Dot (Val n) (Dot x (mem_list2sexp xs)))`;

val ok_mem_sexp_def = Define `
  ok_mem_sexp s = ?xs. s = mem_list2sexp xs`;

val EXISTS_IMP_RWT = METIS_PROVE [] ``((?x. P x) ==> Q) = !x. P x ==> Q``

val lisp_parse_lookup_thm = prove(
  ``!y mem x a.
      (lisp_mem y = mem) /\ ok_mem_sexp y ==>
      ?x2. lisp_parse_lookup_pre (Val a,x,y) /\
           (lisp_parse_lookup (Val a,x,y) = (Val a,x2,mem a))``,
  SIMP_TAC std_ss [ok_mem_sexp_def,EXISTS_IMP_RWT] \\ Induct_on `xs`
  \\ SIMP_TAC std_ss [mem_list2sexp_def] THEN1
   (ONCE_REWRITE_TAC [lisp_mem_def,lisp_parse_lookup_def,lisp_parse_lookup_pre_def]
    \\ SIMP_TAC std_ss [isDot_def,LET_DEF])
  \\ Cases_on `h` \\ SIMP_TAC std_ss [mem_list2sexp_def]
  \\ ONCE_REWRITE_TAC [lisp_mem_def,lisp_parse_lookup_def,lisp_parse_lookup_pre_def]
  \\ SIMP_TAC (srw_ss()) [isDot_def,LET_DEF,CAR_def,CDR_def,getVal_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `a = q`
  \\ ASM_SIMP_TAC std_ss [APPLY_UPDATE_THM,markerTheory.Abbrev_def]);

val lisp_parse_mem_inv_def = Define `
  lisp_parse_mem_inv x5 mem xbp amnt xs ys =
    (mem = \a. if a < amnt then EL a xs else lisp_mem x5 a) /\
    ok_mem_sexp x5 /\ (xbp = LENGTH (xs ++ ys)) /\
    (amnt = LENGTH xs)`;

val UPDATE_NTH_APPEND = prove(
  ``!xs ys n x.
       UPDATE_NTH n x (xs ++ ys) =
         if LENGTH xs <= n then xs ++ UPDATE_NTH (n - LENGTH xs) x ys
                          else UPDATE_NTH n x xs ++ ys``,
  Induct \\ SIMP_TAC std_ss [LENGTH,APPEND]
  \\ Cases_on `n` \\ ASM_SIMP_TAC std_ss [UPDATE_NTH_def,CONS_11,APPEND]
  \\ METIS_TAC []);

val LIST_UPDATE_NTH_def = Define `
  (LIST_UPDATE_NTH [] xs = xs) /\
  (LIST_UPDATE_NTH ((n,x)::ys) xs = LIST_UPDATE_NTH ys (UPDATE_NTH n x xs))`;

val lisp_parse_thm = prove(
  ``!cs s task mem.
      (\(cs,s,task,mem).
        !exp cs2 x0 x1 x2 x3 x4 x5 xs ys io xbp.
          lisp_parse_mem_inv x5 mem xbp amnt xs ys /\
          ((exp,cs2) = sexp_lex_parse (cs,s,task,mem)) ==>
          ?y0 y1 y2 y3 y4 y5 xs2.
             lisp_parse_pre (x0,x1,x2,parse_task task,parse_task2 task x4,x5,
                             parse_stack s ++ xs ++ ys,REPLACE_INPUT_IO cs io,xbp,amnt:num) /\
             (lisp_parse (x0,x1,x2,parse_task task,parse_task2 task x4,x5,
                          parse_stack s ++ xs ++ ys,REPLACE_INPUT_IO cs io,xbp,amnt) =
               (exp,y1,y2,y3,y4,y5,LIST_UPDATE_NTH xs2 xs ++ ys,REPLACE_INPUT_IO cs2 io,xbp,amnt))) (cs,s,task,mem)``,

  HO_MATCH_MP_TAC sexp_lex_parse_ind \\ SIMP_TAC std_ss []
  \\ REVERSE (REPEAT STRIP_TAC) \\ POP_ASSUM MP_TAC THEN1
   (SIMP_TAC std_ss [Once sexp_lex_parse_def,LET_DEF]
    \\ Cases_on `s` \\ SIMP_TAC std_ss [parse_stack_def,APPEND,NOT_CONS_NIL] THEN1
     (REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [parse_task_def,parse_task2_def]
      \\ ONCE_REWRITE_TAC [lisp_parse_def]
      \\ ONCE_REWRITE_TAC [lisp_parse_pre_def]
      \\ SIMP_TAC std_ss [LET_DEF,HD,SExp_distinct,TL,NOT_CONS_NIL]
      \\ Q.EXISTS_TAC `[]` \\ SIMP_TAC std_ss [LIST_UPDATE_NTH_def] \\ METIS_TAC [])
    \\ FULL_SIMP_TAC std_ss [HD,TL]
    \\ Cases_on `h = L_QUOTE` \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL] THEN1
     (FULL_SIMP_TAC std_ss [parse_task_def,parse_task2_def]
      \\ ONCE_REWRITE_TAC [lisp_parse_def,lisp_parse_pre_def]
      \\ SIMP_TAC std_ss [LET_DEF,HD,SExp_distinct,TL,parse_stack_def,APPEND]
      \\ SIMP_TAC (srw_ss()) [] \\ STRIP_TAC
      \\ Q.PAT_X_ASSUM `!exp.bbb` MATCH_MP_TAC
      \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC [])
    \\ Cases_on `READ_L_STORE h` THEN1
     (FULL_SIMP_TAC std_ss [NOT_CONS_NIL]
      \\ ONCE_REWRITE_TAC [lisp_parse_def,lisp_parse_pre_def]
      \\ FULL_SIMP_TAC std_ss [parse_task_def,parse_task2_def]
      \\ FULL_SIMP_TAC std_ss [LET_DEF,HD,SExp_distinct,TL,parse_stack_def,APPEND]
      \\ `~(HD (parse_stack (h::t) ++ xs ++ ys) = Sym "NIL") /\
          ~(HD (parse_stack (h::t) ++ xs ++ ys) = Sym "QUOTE") /\
          ~isVal (HD (parse_stack (h::t) ++ xs ++ ys)) /\
          ~(parse_stack (h::t) ++ xs ++ ys = [])` by
            (Cases_on `h` \\ FULL_SIMP_TAC (srw_ss())
                 [parse_stack_def,APPEND,isVal_def,READ_L_STORE_def])
      \\ ASM_SIMP_TAC std_ss [])
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ IMP_RES_TAC READ_L_STORE_NONE_IMP
    \\ FULL_SIMP_TAC (srw_ss()) [parse_stack_def]
    \\ FULL_SIMP_TAC std_ss [parse_task_def,parse_task2_def]
    \\ ONCE_REWRITE_TAC [lisp_parse_def,lisp_parse_pre_def]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,HD,SExp_distinct,TL,parse_stack_def,APPEND,isVal_def]
    \\ FULL_SIMP_TAC std_ss [getVal_def]
    \\ Cases_on `x < amnt` \\ ASM_SIMP_TAC std_ss [NOT_CONS_NIL] THEN1
     (`(amnt = LENGTH xs) /\
       (xbp = LENGTH (xs ++ ys))` by FULL_SIMP_TAC std_ss [lisp_parse_mem_inv_def]
      \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]
      \\ `LENGTH (parse_stack t) + LENGTH xs + LENGTH ys + x -
          (LENGTH xs + LENGTH ys) = LENGTH (parse_stack t) + x` by DECIDE_TAC
      \\ ASM_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
      \\ `~(LENGTH xs <= x) /\ x < LENGTH xs + LENGTH ys` by DECIDE_TAC
      \\ ASM_SIMP_TAC std_ss [UPDATE_NTH_APPEND]
      \\ ASM_SIMP_TAC std_ss [APPEND_ASSOC]
      \\ `lisp_parse_mem_inv x5 ((x =+ exp) mem) (LENGTH xs + LENGTH ys) amnt (UPDATE_NTH x exp xs) ys` by
       (FULL_SIMP_TAC std_ss [lisp_parse_mem_inv_def,LENGTH_APPEND,
          LENGTH_UPDATE_NTH,FUN_EQ_THM,APPLY_UPDATE_THM,EL_UPDATE_NTH]
        \\ METIS_TAC [])
      \\ `LENGTH xs = LENGTH (UPDATE_NTH x exp xs)` by SIMP_TAC std_ss [LENGTH_UPDATE_NTH]
      \\ POP_ASSUM (fn th => SIMP_TAC std_ss [th])
      \\ REPEAT STRIP_TAC
      \\ Q.PAT_X_ASSUM `!expp.bbb` (MP_TAC o Q.SPECL [`exp'`,`cs2`,`exp`,`Val x`,
                `x2`,`x5`,`UPDATE_NTH x exp xs`,`ys`,`io`,`LENGTH (xs:SExp list) + LENGTH (ys:SExp list)`])
      \\ ASM_SIMP_TAC std_ss [] \\ SIMP_TAC std_ss [LENGTH_UPDATE_NTH]
      \\ METIS_TAC [LIST_UPDATE_NTH_def])
    \\ REPEAT STRIP_TAC
    \\ `lisp_parse_mem_inv (Dot (Val x) (Dot exp x5)) ((x =+ exp) mem) xbp amnt xs ys` by
     (FULL_SIMP_TAC std_ss [lisp_parse_mem_inv_def]
      \\ FULL_SIMP_TAC std_ss [ok_mem_sexp_def]
      \\ REVERSE (REPEAT STRIP_TAC)
      THEN1 (Q.EXISTS_TAC `(x,exp)::xs'` \\ FULL_SIMP_TAC std_ss [mem_list2sexp_def])
      \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM]
      \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC std_ss [Once lisp_mem_def]
      \\ FULL_SIMP_TAC std_ss [CAR_def,CDR_def,getVal_def,APPLY_UPDATE_THM,isDot_def]
      \\ METIS_TAC [])
    \\ RES_TAC \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MP_TAC
    \\ ASM_SIMP_TAC std_ss [])
  THEN1
   (SIMP_TAC std_ss [Once sexp_lex_parse_def,LET_DEF]
    \\ Cases_on `s` \\ SIMP_TAC std_ss [parse_stack_def,APPEND,NOT_CONS_NIL] THEN1
     (REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [parse_task_def,parse_task2_def]
      \\ ONCE_REWRITE_TAC [lisp_parse_def]
      \\ ONCE_REWRITE_TAC [lisp_parse_pre_def]
      \\ SIMP_TAC (srw_ss()) [LET_DEF,HD,SExp_distinct,TL,NOT_CONS_NIL]
      \\ `remove_parse_stack (parse_stack [] ++ xs ++ ys) = xs ++ ys` by
            FULL_SIMP_TAC std_ss [remove_parse_stack_thm,GSYM APPEND_ASSOC]
      \\ FULL_SIMP_TAC std_ss [parse_stack_def,APPEND,LET_DEF,lisp_syntaxerr_def]
      \\ Q.EXISTS_TAC `[]` \\ SIMP_TAC std_ss [LIST_UPDATE_NTH_def] \\ METIS_TAC [])
    \\ FULL_SIMP_TAC std_ss [HD,TL]
    \\ Cases_on `h = L_STOP` \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL] THEN1
     (FULL_SIMP_TAC std_ss [parse_task_def,parse_task2_def]
      \\ ONCE_REWRITE_TAC [lisp_parse_def,lisp_parse_pre_def]
      \\ SIMP_TAC std_ss [LET_DEF,HD,SExp_distinct,TL,parse_stack_def,APPEND]
      \\ SIMP_TAC (srw_ss()) [] \\ STRIP_TAC
      \\ Q.PAT_X_ASSUM `!exp.bbb` MATCH_MP_TAC \\ ASM_SIMP_TAC std_ss [])
    \\ REVERSE (Cases_on `READ_L_CONS h`) THEN1
     (IMP_RES_TAC READ_L_CONS_NONE_IMP
      \\ FULL_SIMP_TAC (srw_ss()) [parse_stack_def]
      \\ FULL_SIMP_TAC std_ss [parse_task_def,parse_task2_def]
      \\ ONCE_REWRITE_TAC [lisp_parse_def,lisp_parse_pre_def]
      \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF,HD,SExp_distinct,TL,
           parse_stack_def,APPEND,isVal_def])
    \\ Cases_on `h = L_DOT` \\ ASM_SIMP_TAC std_ss [] THEN1
     (FULL_SIMP_TAC (srw_ss()) [parse_stack_def]
      \\ FULL_SIMP_TAC std_ss [parse_task_def,parse_task2_def]
      \\ ONCE_REWRITE_TAC [lisp_parse_def,lisp_parse_pre_def]
      \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF,HD,SExp_distinct,TL,
           parse_stack_def,APPEND,isVal_def,SAFE_CAR_def])
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [parse_task2_def]
    \\ ONCE_REWRITE_TAC [lisp_parse_def]
    \\ ONCE_REWRITE_TAC [lisp_parse_pre_def]
    \\ `~(HD (parse_stack (h::t) ++ xs ++ ys) = Sym "NIL") /\
        ~(HD (parse_stack (h::t) ++ xs ++ ys) = Sym "CONS") /\
        ~(HD (parse_stack (h::t) ++ xs ++ ys) = Sym "CAR") /\
        ~(HD (parse_stack (h::t) ++ xs ++ ys) = Sym "CDR") /\
        ~(parse_stack (h::t) = [])` by
      (Cases_on `h` \\ FULL_SIMP_TAC (srw_ss()) [HD,
         parse_stack_def,APPEND,isVal_def,READ_L_CONS_def])
    \\ ASM_SIMP_TAC (srw_ss()) [LET_DEF,HD,SExp_distinct,TL,
         NOT_CONS_NIL,parse_task_def,lisp_syntaxerr_def]
    \\ `HD (parse_stack (h::t) ++ xs ++ ys)::TL (parse_stack (h::t) ++ xs ++ ys) =
        parse_stack (h::t) ++ xs ++ ys` by
      (Cases_on `parse_stack (h::t)` \\ FULL_SIMP_TAC std_ss [HD,TL,APPEND])
    \\ ASM_SIMP_TAC std_ss [remove_parse_stack_thm,GSYM APPEND_ASSOC]
    \\ Q.EXISTS_TAC `[]` \\ ASM_SIMP_TAC std_ss [LIST_UPDATE_NTH_def])
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [parse_task_def]
  \\ ONCE_REWRITE_TAC [lisp_parse_def]
  \\ ONCE_REWRITE_TAC [lisp_parse_pre_def]
  \\ ASM_SIMP_TAC (srw_ss()) [LET_DEF,HD,SExp_distinct,TL,
         NOT_CONS_NIL,parse_task_def,lisp_syntaxerr_def,lisp_token_def]
  \\ ASM_SIMP_TAC std_ss [getINPUT_REPLACE_INPUT_IO,next_token1_def,next_token2_def]
  \\ `?cs3 z1 z2. next_token cs = ((z1,z2),cs3)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss []
  \\ `~(parse_stack s = [])` by
   (Cases_on `s` \\ SIMP_TAC std_ss [parse_stack_def,NOT_CONS_NIL]
    \\ Cases_on `h` \\ SIMP_TAC std_ss [parse_stack_def,NOT_CONS_NIL,APPEND])
  \\ Cases_on `z2 = Val 0` \\ FULL_SIMP_TAC (srw_ss()) [parse_task2_def]
  THEN1
   (Q.PAT_X_ASSUM `(exp,cs2) = xxx` MP_TAC \\ ONCE_REWRITE_TAC [sexp_lex_parse_def]
    \\ FULL_SIMP_TAC (srw_ss()) [APPLY_REPLACE_INPUT_IO,LET_DEF] \\ METIS_TAC [])
  \\ Cases_on `z2 = Val 1` \\ FULL_SIMP_TAC (srw_ss()) [parse_task2_def] THEN1
   (Cases_on `z1 = Val 0` \\ FULL_SIMP_TAC (srw_ss()) [parse_task2_def,
      parse_stack_def,APPLY_REPLACE_INPUT_IO] THEN1
      (Q.PAT_X_ASSUM `(exp,cs2) = xxx` MP_TAC \\ ONCE_REWRITE_TAC [sexp_lex_parse_def]
       \\ FULL_SIMP_TAC (srw_ss()) [APPLY_REPLACE_INPUT_IO,LET_DEF] \\ METIS_TAC [])
    \\ Cases_on `z1 = Val 1` \\ FULL_SIMP_TAC (srw_ss()) [parse_task2_def,
      parse_stack_def,APPLY_REPLACE_INPUT_IO] THEN1
      (Q.PAT_X_ASSUM `(exp,cs2) = xxx` MP_TAC \\ ONCE_REWRITE_TAC [sexp_lex_parse_def]
       \\ FULL_SIMP_TAC (srw_ss()) [APPLY_REPLACE_INPUT_IO,LET_DEF] \\ METIS_TAC [])
    \\ Cases_on `z1 = Val 3` \\ FULL_SIMP_TAC (srw_ss()) [parse_task2_def,
      parse_stack_def,APPLY_REPLACE_INPUT_IO] THEN1
      (Q.PAT_X_ASSUM `(exp,cs2) = xxx` MP_TAC \\ ONCE_REWRITE_TAC [sexp_lex_parse_def]
       \\ FULL_SIMP_TAC (srw_ss()) [APPLY_REPLACE_INPUT_IO,LET_DEF] \\ METIS_TAC [])
    \\ `z1 = Val 2` by METIS_TAC [next_token_cases]
    \\ FULL_SIMP_TAC (srw_ss()) [parse_task2_def,
         parse_stack_def,APPLY_REPLACE_INPUT_IO]
    \\ Q.PAT_X_ASSUM `(exp,cs2) = xxx` MP_TAC \\ ONCE_REWRITE_TAC [sexp_lex_parse_def]
    \\ FULL_SIMP_TAC (srw_ss()) [APPLY_REPLACE_INPUT_IO,LET_DEF] \\ METIS_TAC [])
  \\ Cases_on `z2 = Val 2` \\ FULL_SIMP_TAC (srw_ss()) [parse_task2_def] THEN1
   (Q.PAT_X_ASSUM `(exp,cs2) = xxx` MP_TAC \\ ONCE_REWRITE_TAC [sexp_lex_parse_def]
    \\ FULL_SIMP_TAC (srw_ss()) [APPLY_REPLACE_INPUT_IO,LET_DEF]
    \\ `isVal z1` by METIS_TAC [next_token_cases]
    \\ FULL_SIMP_TAC (srw_ss()) [isVal_thm,getVal_def]
    \\ FULL_SIMP_TAC (srw_ss()) [parse_task2_def,
          parse_stack_def,APPLY_REPLACE_INPUT_IO,getVal_def] \\ METIS_TAC [])
  \\ Cases_on `z2 = Val 3` \\ FULL_SIMP_TAC (srw_ss()) [parse_task2_def] THEN1
   (Q.PAT_X_ASSUM `(exp,cs2) = xxx` MP_TAC \\ ONCE_REWRITE_TAC [sexp_lex_parse_def]
    \\ FULL_SIMP_TAC (srw_ss()) [APPLY_REPLACE_INPUT_IO,LET_DEF]
    \\ `isVal z1` by METIS_TAC [next_token_cases]
    \\ FULL_SIMP_TAC (srw_ss()) [isVal_thm,getVal_def]
    \\ FULL_SIMP_TAC (srw_ss()) [isVal_thm,getVal_def]
    \\ Cases_on `a < amnt` \\ ASM_SIMP_TAC std_ss [] THEN1
     (`(amnt = LENGTH xs) /\
       (xbp = LENGTH (xs ++ ys))` by FULL_SIMP_TAC std_ss [lisp_parse_mem_inv_def]
      \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]
      \\ `LENGTH (parse_stack s) + LENGTH xs + LENGTH ys + a -
          (LENGTH xs + LENGTH ys) = LENGTH (parse_stack s) + a` by DECIDE_TAC
      \\ ASM_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
      \\ `LENGTH (parse_stack s) <= LENGTH (parse_stack s) + a` by DECIDE_TAC
      \\ ASM_SIMP_TAC std_ss [rich_listTheory.EL_APPEND2,rich_listTheory.EL_APPEND1]
      \\ `EL a xs = mem a` by FULL_SIMP_TAC std_ss [lisp_parse_mem_inv_def]
      \\ `a < LENGTH xs + LENGTH ys` by DECIDE_TAC
      \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC])
    \\ `ok_mem_sexp x5` by FULL_SIMP_TAC std_ss [lisp_parse_mem_inv_def]
    \\ IMP_RES_TAC (SIMP_RULE std_ss [] lisp_parse_lookup_thm)
    \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [`Sym "NIL"`,`a`])
    \\ ASM_SIMP_TAC std_ss []
    \\ `lisp_mem x5 a = mem a` by
          (FULL_SIMP_TAC std_ss [lisp_parse_mem_inv_def] \\ METIS_TAC [])
    \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [])
  \\ Q.PAT_X_ASSUM `(exp,cs2) = xxx` MP_TAC \\ ONCE_REWRITE_TAC [sexp_lex_parse_def]
  \\ FULL_SIMP_TAC (srw_ss()) [APPLY_REPLACE_INPUT_IO,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [remove_parse_stack_thm,GSYM APPEND_ASSOC]
  \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `[]`
  \\ ASM_SIMP_TAC std_ss [LIST_UPDATE_NTH_def] \\ METIS_TAC [])
  |> SIMP_RULE std_ss [];

val lisp_pushes_thm = prove(
  ``!n x xs. lisp_pushes_pre (x,Val n,xs) /\
      (lisp_pushes (x,Val n,xs) = (x,Val 0,GENLIST (\a.x) n ++ xs))``,
  Induct \\ ONCE_REWRITE_TAC [lisp_pushes_def,lisp_pushes_pre_def]
  \\ ASM_SIMP_TAC (srw_ss()) [GENLIST,APPEND,LET_DEF,LISP_SUB_def,getVal_def,isVal_def]);

val read_sexp_def = Define `
  read_sexp io = FST (sexp_parse_stream (getINPUT io))`;

val next_sexp_def = Define `
  next_sexp io = IO_INPUT_APPLY (SND o sexp_parse_stream) io`;

val LENGTH_LIST_UPDATE_NTH = prove(
  ``!xs ys. LENGTH (LIST_UPDATE_NTH xs ys) = LENGTH ys``,
  Induct \\ SIMP_TAC std_ss [LIST_UPDATE_NTH_def]
  \\ Cases \\ ASM_SIMP_TAC std_ss [LIST_UPDATE_NTH_def,LENGTH_UPDATE_NTH]);

val lisp_string2sexp_thm = prove(
  ``!x0 x1 x2 x3 x4 x5 xs io.
      lisp_string2sexp_pre (x0,x1,x2,x3,x4,x5,xs,io,xbp,amnt) /\
      (lisp_string2sexp (x0,x1,x2,x3,x4,x5,xs,io,xbp,amnt) =
         (read_sexp io,x1,x2,x3,x4,x5,xs,next_sexp io,LENGTH xs,amnt))``,
  SIMP_TAC std_ss [lisp_string2sexp_def,lisp_string2sexp_pre_def,LET_DEF]
  \\ NTAC 7 STRIP_TAC \\ ASM_SIMP_TAC std_ss [lisp_pushes_thm]
  \\ `?exp cs2. ((exp,cs2) = sexp_lex_parse (getINPUT io,[],L_READ,lisp_mem (Sym "NIL")))` by METIS_TAC [PAIR]
  \\ MP_TAC (Q.SPECL [`getINPUT io`,`[]`,`L_READ`,`\x.Sym "NIL"`,`exp`,`cs2`,`Sym "NIL"`,`Val 0`,`x2`,`x4`,`Sym "NIL"`,`GENLIST (\a. Sym "NIL") amnt`,`x5::x4::x3::x2::x1::xs`,`io`,`LENGTH
        (GENLIST (\a. Sym "NIL") amnt ++
         x5::x4::x3::x2::x1::xs)`] lisp_parse_thm)
  \\ ASM_SIMP_TAC std_ss [parse_stack_def,APPEND]
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (SIMP_TAC std_ss [lisp_parse_mem_inv_def,LENGTH_GENLIST]
    \\ ONCE_REWRITE_TAC [lisp_mem_def] \\ SIMP_TAC std_ss [isDot_def]
    \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [EL_GENLIST]
    \\ SIMP_TAC std_ss [ok_mem_sexp_def] \\ Q.EXISTS_TAC `[]` \\ EVAL_TAC)
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [parse_task_def,parse_task2_def]
  \\ FULL_SIMP_TAC std_ss [IO_INPUT_LEMMA,NOT_CONS_NIL,CONS_11,TL,HD,getVal_def]
  \\ Q.ABBREV_TAC `zs = (DROP amnt (LIST_UPDATE_NTH xs2
                        (GENLIST (\a. Sym "NIL") amnt) ++ x5::x4::x3::x2::x1::xs))`
  \\ `zs = x5::x4::x3::x2::x1::xs` by
   (`amnt = LENGTH (LIST_UPDATE_NTH xs2 (GENLIST (\a. Sym "NIL") amnt))` by
              ASM_SIMP_TAC std_ss [LENGTH_LIST_UPDATE_NTH,LENGTH_GENLIST]
    \\ Q.UNABBREV_TAC `zs` \\ POP_ASSUM (fn th => SIMP_TAC std_ss [Once th])
    \\ SIMP_TAC std_ss [rich_listTheory.BUTFIRSTN_LENGTH_APPEND])
  \\ ASM_SIMP_TAC std_ss [TL,HD,NOT_CONS_NIL,isVal_def]
  \\ ASM_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH_LIST_UPDATE_NTH,LENGTH_GENLIST]
  \\ Q.PAT_X_ASSUM `(exp,cs2) = xxx` (MP_TAC o GSYM)
  \\ ASM_SIMP_TAC std_ss [read_sexp_def,next_sexp_def,sexp_parse_stream_def]
  \\ Cases_on `io` \\ FULL_SIMP_TAC std_ss [IO_INPUT_APPLY_def,getINPUT_def,
       REPLACE_INPUT_IO_def,sexp_parse_stream_def]
  \\ ONCE_REWRITE_TAC [lisp_mem_def] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [isDot_def]);


fun abbrev_code (th,jump,def_name) = let
  val INSERT_UNION_INSERT = prove(
    ``x INSERT (y UNION (z INSERT t)) = x INSERT z INSERT (y UNION t)``,
    SIMP_TAC std_ss [EXTENSION,IN_INSERT,IN_UNION] \\ METIS_TAC []);
  fun mk_tuple [] = fail()
    | mk_tuple [x] = x
    | mk_tuple (x::xs) = pairSyntax.mk_pair(x,mk_tuple xs)
  val th = th
           |> SIMP_RULE std_ss [lisp_string2sexp_thm,LET_DEF,SEP_CLAUSES]
           |> SIMP_RULE std_ss [INSERT_UNION_INSERT,INSERT_UNION_EQ,UNION_EMPTY,
                                GSYM UNION_ASSOC,UNION_IDEMPOT]
  val th = Q.INST [`qs`|->`q::qs`] th
  val th = SPEC_COMPOSE_RULE [th,X64_LISP_RET]
  val (_,_,c,_) = dest_spec (concl th)
  val input = mk_tuple (free_vars c)
  val ty = type_of (pairSyntax.mk_pabs(input,c))
  val name = mk_var(def_name,ty)
  val def = Define [ANTIQUOTE (mk_eq(mk_comb(name,input),c))]
  val th = RW [GSYM def] th
  val th = SPEC_COMPOSE_RULE [jump,th]
  in th end;


val X64_LISP_PARSE_SEXP = save_thm("X64_LISP_PARSE_SEXP",let
  val th = lisp_string2sexp_spec
  val jump = X64_LISP_CALL_EL3
  val def_name = "abbrev_code_for_parse"
  val th = abbrev_code (th,jump,def_name)
  val _ = add_compiled [th]
  in th end);

val X64_LISP_PRINT_SEXP = save_thm("X64_LISP_PRINT_SEXP",let
  val th = SIMP_RULE std_ss [lisp_sexp2string_thm,LET_DEF,SEP_CLAUSES] lisp_sexp2string_spec
  val jump = X64_LISP_CALL_EL7
  val def_name = "abbrev_code_for_print"
  val th = abbrev_code (th,jump,def_name)
  val _ = add_compiled [th]
  in th end);


val _ = export_theory();
