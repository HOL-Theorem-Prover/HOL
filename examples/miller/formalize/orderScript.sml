(* non-interactive mode
*)
open HolKernel Parse boolLib;
val _ = new_theory "order";
val _ = ParseExtras.temp_loose_equality()

(* interactive mode
val () = loadPath := union ["..", "../finished"] (!loadPath);
val () = app load
  ["bossLib",
   "pred_setTheory",
   "realLib",
   "pairTheory",
   "combinTheory",
   "res_quanLib",
   "dividesTheory",
   "primeTheory",
   "gcdTheory",
   "prob_extraTools",
   "millerTools"];
val () = show_assums := true;
*)

open bossLib listTheory subtypeTools res_quanTools res_quanTheory
     pred_setTheory extra_pred_setTheory listContext relationTheory
     ho_proverTools subtypeTheory hurdUtils;

(* ------------------------------------------------------------------------- *)
(* Tools.                                                                    *)
(* ------------------------------------------------------------------------- *)

val S_TAC = rpt (POP_ASSUM MP_TAC) >> rpt RESQ_STRIP_TAC;

val (R_TAC, AR_TAC, R_TAC', AR_TAC') = SIMPLIFY_TACS list_c;

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                             *)
(* ------------------------------------------------------------------------- *)

val reflexive_def = Define `reflexive f = !x. f x x`;

val antisym_def = Define `antisym f = !x y. f x y /\ f y x ==> (x = y)`;

val total_def = Define `total f = !x y. f x y \/ f y x`;

val preorder_def = Define `preorder f = reflexive f /\ transitive f`;

val partialorder_def = Define `partialorder f = preorder f /\ antisym f`;

val totalorder_def = Define `totalorder f = partialorder f /\ total f`;

val sorted_def = Define
  `(sorted f [] = T) /\
   (sorted f [h] = T) /\
   (sorted f (h1 :: h2 :: t) = f h1 h2 /\ sorted f (h2 :: t))`;

val insert_def = Define
  `(insert f a [] = [a]) /\
   (insert f a (h :: t) = if f a h then a :: h :: t else h :: insert f a t)`;

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

val INSERT_SORTED = store_thm
  ("INSERT_SORTED",
   ``!f a l. totalorder f ==> (sorted f (insert f a l) = sorted f l)``,
   S_TAC
   >> AR_TAC [totalorder_def, partialorder_def, preorder_def,
              reflexive_def, transitive_def, total_def]
   >> Cases_on `sorted f l` THENL
   [R_TAC []
    >> Cases_on `l` >- R_TAC [sorted_def, insert_def]
    >> R_TAC [insert_def]
    >> POP_ASSUM MP_TAC
    >> Q.SPEC_TAC (`h`, `x`)
    >> Induct_on `t`
    >- (S_TAC
        >> Cases_on `f a x`
        >> AR_TAC [sorted_def, insert_def]
        >> ho_PROVE_TAC [])
    >> S_TAC
    >> Cases_on `f a x` >- AR_TAC [sorted_def]
    >> Q.PAT_X_ASSUM `!x. P x ==> Q x` (MP_TAC o Q.SPEC `h`)
    >> Q.PAT_X_ASSUM `sorted f (x::h::t)` MP_TAC
    >> R_TAC [sorted_def, insert_def]
    >> Cases_on `f a h`
    >> R_TAC [sorted_def]
    >> ho_PROVE_TAC [],
    R_TAC []
    >> Cases_on `l` >- AR_TAC [sorted_def, insert_def]
    >> POP_ASSUM MP_TAC
    >> Q.SPEC_TAC (`h`, `x`)
    >> Induct_on `t` >- R_TAC [sorted_def]
    >> S_TAC
    >> Q.PAT_X_ASSUM `!x. P x ==> Q x` (MP_TAC o Q.SPEC `h`)
    >> NTAC 2 (POP_ASSUM MP_TAC)
    >> R_TAC [sorted_def, insert_def]
    >> Cases_on `f a x`
    >> Cases_on `f a h`
    >> R_TAC [sorted_def]
    >> ho_PROVE_TAC []]);

(* non-interactive mode
*)
val _ = export_theory ();
