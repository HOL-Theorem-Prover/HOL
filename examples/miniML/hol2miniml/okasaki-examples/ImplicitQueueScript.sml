
open HolKernel Parse boolLib bossLib; val _ = new_theory "ImplicitQueue";

open listTheory arithmeticTheory;
open ml_translatorLib;

(* Okasaki page 174 *)

(* implementation *)

val _ = Hol_datatype `times = Once of 'a | Twice of times => times`;
val _ = Hol_datatype `digit = Zero | One of 'a times | Two of 'a times => 'a times`;
val _ = Hol_datatype `queue = Shallow of 'a digit
                            | Deep of 'a digit => queue => 'a digit`;

val empty_def = mlDefine `
  empty = Shallow Zero`;

val is_empty_def = mlDefine `
  (is_empty (Shallow Zero) = T) /\
  (is_empty _ = F)`;

val snoc_def = mlDefine `
  (snoc (Shallow Zero) y = Shallow (One y)) /\
  (snoc (Shallow (One x)) y = Deep (Two x y) empty Zero) /\
  (snoc (Deep f m Zero) y = Deep f m (One y)) /\
  (snoc (Deep f m (One x)) y = Deep f (snoc m (Twice x y)) Zero)`

val head_def = mlDefine `
  (head (Shallow (One x)) = x) /\
  (head (Deep (One x) m r) = x) /\
  (head (Deep (Two x y) m r) = x)`;

val tail_def = mlDefine `
  (tail (Shallow (One x)) = empty) /\
  (tail (Deep (Two x y) m r) = Deep (One y) m r) /\
  (tail (Deep (One x) q r) =
     if is_empty q then Shallow r else
       case head q of Twice y z => Deep (Two y z) (tail q) r)`

(*
(* verification *)

val exps_def = Define `
  (exps (Once x) = [x]) /\
  (exps (Twice t1 t2) = exps t1 ++ exps t2)`;

val digits_def = Define `
  (digits Zero = []) /\
  (digits (One x) = exps x) /\
  (digits (Two x y) = exps x ++ exps y)`;

val flatten_def = Define `
  (flatten (Shallow x) = digits x) /\
  (flatten (Deep d1 t d2) = digits d1 ++ flatten t ++ digits d2)`;

val only_digits_def = Define `
  (only_digits Zero = []) /\
  (only_digits (One x) = [x]) /\
  (only_digits (Two x y) = [x;y])`;

val depth_def = Define `
  (depth n m (Once x) = (m = n)) /\
  (depth n m (Twice t1 t2) = depth (n+1) m t1 /\ depth (n+1) m t2)`;

val ddepth_def = Define `
  ddepth n d = EVERY (\d. depth 0 n d) (only_digits d)`;

val two_def = Define `
  (two (Two _ _) = T) /\ (two _ = F)`;

val queue_ok_def = Define `
  (queue_ok n (Shallow x) = ~two x /\ ddepth n x) /\
  (queue_ok n (Deep x1 t x2) =
     ~(x1 = Zero) /\ queue_ok (n+1) t /\ ~two x2 /\ ddepth n x1 /\ ddepth n x2)`;

val queue_inv_def = Define `
  queue_inv q t = queue_ok 0 t /\ (q = flatten t)`;

val empty_thm = prove(
  ``queue_inv [] empty``,
  EVAL_TAC);

val exps_NOT_NIL = prove(
  ``!e. ~(exps e = [])``,
  Induct THEN EVAL_TAC THEN FULL_SIMP_TAC std_ss [APPEND_eq_NIL]);

val is_empty_thm = prove(
  ``!xs q. queue_inv xs q ==> (is_empty q = (xs = []))``,
  Cases THEN Cases THEN EVAL_TAC
  THEN1 (Cases_on `d` THEN EVAL_TAC THEN SIMP_TAC std_ss [exps_NOT_NIL])
  THEN1 (Cases_on `d0` THEN EVAL_TAC THEN ONCE_REWRITE_TAC [EQ_SYM_EQ]
         THEN SIMP_TAC std_ss [exps_NOT_NIL,APPEND_eq_NIL])
  THEN Cases_on `d` THEN EVAL_TAC);

val qdepth_def = Define `
  (qdepth (Shallow _) = 0) /\
  (qdepth (Deep _ t _) = SUC (qdepth t))`;

val snoc_thm = prove(
  ``!q xs x. queue_inv xs q ==> queue_inv (xs ++ [x]) (snoc q (Once x))``,
  STRIP_TAC THEN SIMP_TAC std_ss [queue_inv_def] THEN Q.SPEC_TAC (`0`,`n`)
  THEN Induct_on `qdepth q` THEN STRIP_TAC THEN STRIP_TAC

snoc_def

queue_ok_def

  Cases_on `q` THEN EVAL_TAC
  THEN Cases_on `d` THEN EVAL_TAC THEN FULL_SIMP_TAC (srw_ss()) []


val depth_LESS_EQ = prove(
  ``!e m n. depth m n e ==> m <= n``,
  Induct THEN EVAL_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN DECIDE_TAC);

val depth_00 = prove(
  ``!e. depth 0 0 e ==> ?x. e = Once x``,
  Cases THEN SIMP_TAC (srw_ss()) [depth_def] THEN REPEAT STRIP_TAC
  THEN METIS_TAC [depth_LESS_EQ,EVAL ``1 <= 0:num``]);

val head_thm = prove(
  ``!q x xs. queue_inv (x::xs) q ==> (head q = Once x)``,
  Cases THEN TRY (Cases_on `d`) THEN TRY (Cases_on `d0`)
  THEN EVAL_TAC THEN SIMP_TAC (srw_ss()) []
  THEN REPEAT STRIP_TAC THEN IMP_RES_TAC depth_00
  THEN FULL_SIMP_TAC (srw_ss()) [exps_def])

val tail_thm = prove(
  ``!q x xs. queue_inv (x::xs) q ==> queue_inv xs (tail q)``,
  Cases THEN1 (Cases_on `d` THEN EVAL_TAC THEN SIMP_TAC (srw_ss()) []
    THEN REPEAT STRIP_TAC THEN IMP_RES_TAC depth_00
    THEN FULL_SIMP_TAC (srw_ss()) [exps_def])
  THEN REVERSE (Cases_on `d0`) THEN EVAL_TAC THEN SIMP_TAC (srw_ss()) []
  THEN1 (REPEAT STRIP_TAC THEN IMP_RES_TAC depth_00
         THEN FULL_SIMP_TAC (srw_ss()) [exps_def])
  THEN Cases_on `is_empty q'` THEN FULL_SIMP_TAC (srw_ss()) []
  THEN1
   (Cases_on `q'` THEN FULL_SIMP_TAC std_ss [is_empty_def]
    THEN Cases_on `d'` THEN FULL_SIMP_TAC std_ss [is_empty_def]
    THEN EVAL_TAC THEN FULL_SIMP_TAC std_ss [is_empty_def]
    THEN REPEAT STRIP_TAC THEN IMP_RES_TAC depth_00
    THEN FULL_SIMP_TAC (srw_ss()) [exps_def])

*)

val _ = export_theory();
