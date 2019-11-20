open HolKernel Parse boolLib bossLib;

open transferTheory finite_mapTheory pred_setTheory

val _ = new_theory "fsets";

Type fset = “:'a |-> unit”

Overload fIN = “\e (fs:'a fset). e IN FDOM fs”

Overload fUNION = “FUNION : 'a fset -> 'a fset -> 'a fset”

Overload fINSERT = “λe fs. fs |+ (e,())”

Definition FSET_def:
  FSET AB fs s <=> !a b. AB a b ==> (fIN a fs <=> b IN s)
End

Theorem fIN_IN:
  (AB ===> FSET AB ===> (=)) fIN (IN)
Proof
  simp[FUN_REL_def, FSET_def]
QED

Theorem fEMPTY_EMPTY:
  FSET AB FEMPTY EMPTY
Proof
  simp[FSET_def]
QED

Theorem fUNION_UNION:
  (FSET AB ===> FSET AB ===> FSET AB) fUNION (UNION)
Proof
  simp[FUN_REL_def, FSET_def] >> metis_tac[]
QED

Theorem fINSERT_INSERT:
  bi_unique AB ==>
  (AB ===> FSET AB ===> FSET AB) fINSERT (INSERT)
Proof
  simp[FUN_REL_def, FSET_def, bi_unique_def, left_unique_def,
       right_unique_def] >> metis_tac[]
QED

Overload fDELETE = “fdomsub : 'a fset -> 'a -> 'a fset”
Theorem fDELETE_DELETE:
  bi_unique AB ==>
  (FSET AB ===> AB ===> FSET AB) fDELETE (DELETE)
Proof
  simp[FUN_REL_def, FSET_def, bi_unique_def, left_unique_def,
       right_unique_def] >> metis_tac[]
QED

Overload toSet = “FDOM : 'a fset -> 'a set”
Theorem toSet_I:
  (FSET (=) ===> (=)) toSet I
Proof
  simp[FUN_REL_def, FSET_def, pred_setTheory.EXTENSION]
QED

Theorem bi_unique_FSET[simp]:
  bi_unique AB ∧ bitotal AB ==> bi_unique (FSET AB)
Proof
  simp[bi_unique_def, FSET_def, left_unique_def, right_unique_def,
       bitotal_def, total_def, surj_def, pred_setTheory.EXTENSION, fmap_EXT] >>
  metis_tac[]
QED

(*
Theorem FSET_ALT:
  FSET AB fs s <=> s = { b | ?a. AB a b /\ fIN a fs }
Proof
  simp[FSET_def, pred_setTheory.EXTENSION] >> eq_tac >> rw[]
*)

Theorem KT_FINITE:
  surj AB /\ right_unique AB ==> (FSET AB ===> (=)) (K T) FINITE
Proof
  rw[FUN_REL_def, FSET_def, right_unique_def, total_def, surj_def] >>
  fs[SKOLEM_THM] >>
  ‘b = { e | fIN (f e) a }’
    by simp[pred_setTheory.EXTENSION] >>
  qabbrev_tac ‘a0 = { f e | e | fIN (f e) a /\ e IN b }’ >>
  ‘a0 SUBSET FDOM a’ by simp[SUBSET_DEF, Abbr‘a0’, PULL_EXISTS] >>
  ‘FINITE a0’ by metis_tac[SUBSET_FINITE, FDOM_FINITE] >>
  ‘a0 = IMAGE f b’ by simp[Abbr‘a0’, EXTENSION] >>
  ‘!e1 e2. f e1 = f e2 <=> e1 = e2’ by metis_tac[] >>
  metis_tac[INJECTIVE_IMAGE_FINITE]
QED


val _ = export_theory();
