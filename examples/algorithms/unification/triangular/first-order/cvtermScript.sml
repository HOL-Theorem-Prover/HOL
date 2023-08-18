open HolKernel Parse boolLib bossLib;
open termTheory
open cvTheory
open transferTheory
open transferLib
open cvxferTheory

val _ = new_theory "cvterm";

Overload cp[local] = “cv$Pair”
Overload cn[local] = “cv$Num”

(* encode unification terms as cv-values *)
Definition t2c_def:
  t2c cf (term$Var n) = cp (cn 0) (cn n) ∧
  t2c cf (term$Pair t1 t2) = cp (cn 1) (cp (t2c cf t1) (t2c cf t2)) ∧
  t2c cf (term$Const c) = cp (cn 2) (cf c)
End

Definition TmC_def:
  (TmC AC (term$Var n) c ⇔ c = cp (cn 0) (cn n)) ∧
  (TmC AC (term$Pair t1 t2) c ⇔ ∃c1 c2. c = cp (cn 1) (cp c1 c2) ∧
                                        TmC AC t1 c1 ∧ TmC AC t2 c2) ∧
  (TmC AC (term$Const ct) c ⇔ ∃c0. c = cp (cn 2) c0 ∧ AC ct c0)
End

Theorem TmVar_C[transfer_rule]:
  (NC |==> TmC AC) term$Var (cp (cn 0))
Proof
  simp[FUN_REL_def, TmC_def, NC_def]
QED

Theorem TmPair_C[transfer_rule]:
  (TmC AC |==> TmC AC |==> TmC AC) term$Pair (λc1 c2. cp (cn 1) (cp c1 c2))
Proof
  simp[FUN_REL_def, TmC_def]
QED

Theorem TmConst_C[transfer_rule]:
  (AC |==> TmC AC) term$Const (cp (cn 2))
Proof
  simp[FUN_REL_def, TmC_def]
QED


val _ = export_theory();
