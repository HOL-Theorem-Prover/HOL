
open HolKernel boolLib bossLib Parse;
open opmonTheory listTheory stringTheory bit_listTheory;

val _ = new_theory "decoder";


(* -- define tokenise - a function which splits a string at white space and comma -- *)

val STR_SPLIT_AUX_def = Define `
  (STR_SPLIT_AUX c [] curr = [IMPLODE (REVERSE curr)]) /\
  (STR_SPLIT_AUX c (x::xs) curr =
    if MEM x c then IMPLODE (REVERSE curr) :: STR_SPLIT_AUX c xs []
               else STR_SPLIT_AUX c xs (x::curr))`;

val STR_SPLIT_def = Define `
  STR_SPLIT c s = STR_SPLIT_AUX c (EXPLODE s) []`;

val tokenise_def = Define `
  tokenise s = FILTER (\x. ~(x = "")) (STR_SPLIT [#" ";#","] s)`;

(* EVAL ``tokenise "testing: A, B, C"`` gives ``["testing:"; "A"; "B"; "C"]`` *)


(* -- syntax matcher -- *)

val match_init_def = Define `
  match_init = (\w:bool list. SOME ((\x:string.[]:bool list),w))`;

val match_def = Define `
  match step s = option_do (MAP step s)`;

val match_list_def = Define `
  match_list step pre res list =
    match_init >>
    option_try (MAP (\(x,y). match step (pre x) >> (res y)) list)`;

val match_list_raw_def = Define `
  match_list_raw g step pre res list =
    (\w:bool list. SOME (g,w)) >>
    option_try (MAP (\(x,y). match step (pre x) >> (res y)) list)`;


(* -- operations over bit lists -- *)

val hex2bits_def = Define `
  hex2bits = FOLDR $++ [] o MAP (\x. n2bits (4 * STRLEN x) (hex2num x)) o tokenise`;

val assign_def = Define `
  assign name x (g:string->bool list, bits:bool list) = SOME ((name =+ x) g,bits)`;

val assign_drop_def = Define `
  assign_drop name i (g:string->bool list, bits:bool list) =
    if LENGTH bits < i then NONE else SOME ((name =+ TAKE i bits) g, DROP i bits)`;

val drop_eq_def = Define `
  drop_eq v (g:string->bool list, bits:bool list) =
    let i = LENGTH v in
      if LENGTH bits < i \/ ~(v = TAKE i bits) then NONE else SOME (g, DROP i bits)`;

val assert_def = Define `
  assert p (g:string->bool list, bits:bool list) =
    if p g then SOME (g,bits) else NONE`;

val DT_def = Define `
  (DT (g,[]) = NONE) /\
  (DT (g,F::b) = NONE) /\
  (DT (g,T::b) = SOME (g,b))`;

val DF_def = Define `
  (DF (g,[]) = NONE) /\
  (DF (g,F::b) = SOME (g,b)) /\
  (DF (g,T::b) = NONE)`;


(* -- simplifying rules -- *)

val drop_eq_thm = store_thm("drop_eq_thm",
  ``!xs. (drop_eq (T::xs) = DT >> drop_eq xs) /\
         (drop_eq (F::xs) = DF >> drop_eq xs) /\
         (drop_eq [] = SOME)``,
  REPEAT STRIP_TAC
  THEN SIMP_TAC bool_ss [FUN_EQ_THM] THEN Cases_on `x` THEN Cases_on `r`
  THEN SIMP_TAC std_ss [drop_eq_def,DT_def,DF_def,LET_DEF,LENGTH,option_then_def,DROP_0,TAKE_0]
  THEN Cases_on `h` THEN SIMP_TAC std_ss [drop_eq_def,DT_def,DF_def,
    LET_DEF,LENGTH,option_then_def,rich_listTheory.BUTFIRSTN,rich_listTheory.FIRSTN,CONS_11]);

val assert_option_then_lemma = prove(
  ``!p b. (assert (\g. T) >> p = p) /\
          (assert b >> DF = DF >> assert b) /\
          (assert b >> DT = DT >> assert b)``,
  REPEAT STRIP_TAC
  THEN SRW_TAC [] [option_then_def,assert_def,FUN_EQ_THM,LET_DEF,pairTheory.FORALL_PROD]
  THEN Cases_on `p_2` THEN SRW_TAC [] [DF_def,DT_def]
  THEN Cases_on `h` THEN FULL_SIMP_TAC std_ss [DF_def,DT_def,assert_def]);

val assert_option_then_thm = store_thm("assert_option_then_thm",
  ``!p q b. (assert (\g. T) >> p = p) /\
            (q >> assert (\g. T) >> p = q >> p) /\
            (assert b >> DF = DF >> assert b) /\
            (assert b >> DT = DT >> assert b) /\
            (p >> assert b >> DF = p >> DF >> assert b) /\
            (p >> assert b >> DT = p >> DT >> assert b)``,
  METIS_TAC [assert_option_then_lemma,option_then_assoc]);


(* -- for fast evaluation -- *)

Theorem DT_DF_then_orelse[compute]:
  ((DT >> p) (g,[]) = NONE) /\ ((DF >> p) (g,[]) = NONE) /\
  ((DT >> p) (g,F::b) = NONE) /\ ((DF >> p) (g,T::b) = NONE) /\
  ((DF >> p) (g,F::b) = p (g,b)) /\ ((DT >> p) (g,T::b) = p (g,b)) /\
  (((DT >> f) ++ p) (g,[]) = p (g,[])) /\ (((DF >> f) ++ p) (g,[]) = p (g,[])) /\
  (((DT >> f1) ++ (DF >> f2)) (g,F::b) = f2 (g,b)) /\
  (((DF >> f2) ++ (DT >> f1)) (g,F::b) = f2 (g,b)) /\
  (((DT >> f1) ++ (DF >> f2)) (g,T::b) = f1 (g,b)) /\
  (((DF >> f2) ++ (DT >> f1)) (g,T::b) = f1 (g,b)) /\
  (((DT >> f) ++ p) (g,F::b) = p (g,F::b)) /\
  (((DF >> f) ++ p) (g,T::b) = p (g,T::b))
Proof
  SIMP_TAC std_ss [DF_def,DT_def,option_then_def,option_orelse_def,LET_DEF] >>
  METIS_TAC []
QED

val DT_over_DF_lemma = prove(
  ``((DT >> x) ++ ((DF >> y) ++ (DT >> z)) = (DT >> (x ++ z)) ++ (DF >> y)) /\
    ((DF >> x) ++ ((DT >> y) ++ (DF >> z)) = (DF >> (x ++ z)) ++ (DT >> y))``,
  REPEAT STRIP_TAC THEN (REWRITE_TAC [FUN_EQ_THM] THEN Cases THEN Cases_on `r`
  THEN1 SIMP_TAC std_ss [DF_def,DT_def,option_then_def,option_orelse_def,LET_DEF]
  THEN Cases_on `h`
  THEN SIMP_TAC std_ss [DF_def,DT_def,option_then_def,option_orelse_def,LET_DEF]
  THEN METIS_TAC []));

val DT_over_DF = store_thm("DT_over_DF",
  ``((DT >> x) ++ ((DF >> y) ++ ((DT >> z) ++ g)) = (DT >> (x ++ z)) ++ ((DF >> y) ++ g)) /\
    ((DF >> x) ++ ((DT >> y) ++ ((DF >> z) ++ g)) = (DF >> (x ++ z)) ++ ((DT >> y) ++ g)) /\
    ((DT >> x) ++ ((DF >> y) ++ (DT >> z)) = (DT >> (x ++ z)) ++ (DF >> y)) /\
    ((DF >> x) ++ ((DT >> y) ++ (DF >> z)) = (DF >> (x ++ z)) ++ (DT >> y))``,
  REWRITE_TAC [GSYM option_orelse_assoc,
    REWRITE_RULE [GSYM option_orelse_assoc] DT_over_DF_lemma]);

val DTF_def = Define `
  (DTF p q (g,[])= NONE) /\
  (DTF p q (g,F::b) = q (g,b)) /\
  (DTF p q (g,T::b) = p (g,b))`;

val DTF_THM = store_thm("DTF_THM",
  ``!x y. ((DF >> p) ++ (DT >> q) = DTF q p) /\ ((DT >> q) ++ (DF >> p) = DTF q p)``,
  REPEAT STRIP_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN Cases THEN Cases_on `r`
  THEN SIMP_TAC bool_ss [DTF_def,DF_def,DT_def,option_then_def,option_orelse_def,LET_DEF]
  THEN Cases_on `h`
  THEN SIMP_TAC std_ss [DTF_def,DF_def,DT_def,option_then_def,option_orelse_def,LET_DEF]
  THEN METIS_TAC []);

val _ = export_theory ();
