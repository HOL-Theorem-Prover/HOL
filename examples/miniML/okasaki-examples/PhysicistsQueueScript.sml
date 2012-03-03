
open HolKernel Parse boolLib bossLib; val _ = new_theory "PhysicistsQueue";

open listTheory arithmeticTheory;

(* implementation *)

val _ = Hol_datatype `queue = QUEUE of 'a list => num => 'a list => num => 'a list`;

val empty_def = Define `empty = QUEUE [] 0 [] 0 []`;

val is_empty_def = Define `
  is_empty (QUEUE _ lenf _ _ _) = (lenf = 0)`;

val checkw_def = Define `
  (checkw (QUEUE [] lenf f lenr r) = QUEUE f lenf f lenr r) /\
  (checkw q = q)`;

val check_def = Define `
  check (QUEUE w lenf f lenr r) =
    if lenr <= lenf
      then checkw (QUEUE w lenf f lenr r)
      else checkw (QUEUE f (lenf + lenr) (f ++ REVERSE r) 0 [])`;

val snoc_def = Define `
  snoc (QUEUE w lenf f lenr r) x =
    check (QUEUE w lenf f (lenr+1) (x::r))`;

val head_def = Define `
  head (QUEUE (x::xs) lenf f lenr r) = x`;

val tail_def = Define `
  tail (QUEUE (x::xs) lenf f lenr r) = check (QUEUE xs (lenf-1) (TL f) lenr r)`;

(* verification proof *)

val queue_inv_def = Define `
  queue_inv q (QUEUE w lenf f lenr r) =
    (q = f ++ REVERSE r) /\ (lenr = LENGTH r) /\ (lenf = LENGTH f) /\
    lenr <= lenf /\ ((w = []) ==> (q = [])) /\ isPREFIX w f`;

val empty_thm = prove(
  ``!xs. queue_inv xs empty = (xs = [])``,
  EVAL_TAC THEN SIMP_TAC std_ss []);

val is_empty_thm = prove(
  ``!q xs. queue_inv xs q ==> (is_empty q = (xs = []))``,
  Cases THEN Cases_on `l` THEN EVAL_TAC THEN SRW_TAC [] []
  THEN Cases_on `l0` THEN FULL_SIMP_TAC (srw_ss()) [APPEND_eq_NIL,LENGTH_NIL]);

val isPREFIX_APPEND = prove(
  ``!xs ys. isPREFIX xs (xs ++ ys)``,
  Induct THEN FULL_SIMP_TAC (srw_ss()) [isPREFIX]);

val isPREFIX_REFL = prove(
  ``!xs ys. isPREFIX xs xs``,
  Induct THEN FULL_SIMP_TAC (srw_ss()) [isPREFIX]);

val snoc_thm = prove(
  ``!q xs x. queue_inv xs q ==> queue_inv (xs ++ [x]) (snoc q x)``,
  Cases THEN Cases_on `l` THEN EVAL_TAC THEN SRW_TAC [] [] THEN EVAL_TAC
  THEN FULL_SIMP_TAC (srw_ss()) [APPEND_eq_NIL,LENGTH_NIL]
  THEN Cases_on `l0` THEN EVAL_TAC THEN FULL_SIMP_TAC (srw_ss()) []
  THEN FULL_SIMP_TAC std_ss [isPREFIX_APPEND,GSYM APPEND_ASSOC]
  THEN DECIDE_TAC);

val head_thm = prove(
  ``!q x xs. queue_inv (x::xs) q ==> (head q = x)``,
  Cases THEN Cases_on `l` THEN EVAL_TAC THEN SRW_TAC [] []
  THEN Cases_on `l0` THEN FULL_SIMP_TAC (srw_ss()) [REVERSE_DEF,LENGTH_NIL]);

val tail_thm = prove(
  ``!q x xs. queue_inv (x::xs) q ==> queue_inv xs (tail q)``,
  Cases THEN Cases_on `l` THEN EVAL_TAC THEN SRW_TAC [] []
  THEN Cases_on `l0` THEN TRY (Cases_on `t`) THEN EVAL_TAC
  THEN FULL_SIMP_TAC (srw_ss()) [REVERSE_DEF,LENGTH_NIL,isPREFIX_REFL]
  THEN Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL]
  THEN EVAL_TAC THEN FULL_SIMP_TAC (srw_ss()) [REVERSE_DEF,LENGTH_NIL,
          isPREFIX_REFL,isPREFIX_APPEND] THEN DECIDE_TAC);

val _ = export_theory();
