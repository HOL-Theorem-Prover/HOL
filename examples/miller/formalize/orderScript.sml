(* non-interactive mode
*)
Theory order
Ancestors
  list res_quan pred_set extra_pred_set relation subtype
Libs
  subtypeTools res_quanTools listContext ho_proverTools hurdUtils

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

(* ------------------------------------------------------------------------- *)
(* Tools.                                                                    *)
(* ------------------------------------------------------------------------- *)

val S_TAC = rpt (POP_ASSUM MP_TAC) >> rpt RESQ_STRIP_TAC;

val (R_TAC, AR_TAC, R_TAC', AR_TAC') = SIMPLIFY_TACS list_c;

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                             *)
(* ------------------------------------------------------------------------- *)

Definition reflexive_def:   reflexive f = !x. f x x
End

Definition antisym_def:   antisym f = !x y. f x y /\ f y x ==> (x = y)
End

Definition total_def:   total f = !x y. f x y \/ f y x
End

Definition preorder_def:   preorder f = reflexive f /\ transitive f
End

Definition partialorder_def:   partialorder f = preorder f /\ antisym f
End

Definition totalorder_def:   totalorder f = partialorder f /\ total f
End

Definition sorted_def:
   (sorted f [] = T) /\
   (sorted f [h] = T) /\
   (sorted f (h1 :: h2 :: t) = f h1 h2 /\ sorted f (h2 :: t))
End

Definition insert_def:
   (insert f a [] = [a]) /\
   (insert f a (h :: t) = if f a h then a :: h :: t else h :: insert f a t)
End

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

Theorem INSERT_SORTED:
     !f a l. totalorder f ==> (sorted f (insert f a l) = sorted f l)
Proof
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
    >> ho_PROVE_TAC []]
QED

(* non-interactive mode
*)
