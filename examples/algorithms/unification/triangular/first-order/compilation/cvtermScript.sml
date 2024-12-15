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

Definition TmC_def[simp]:
  (TmC AC (term$Var n) c ⇔ c = cp (cn 0) (cn n)) ∧
  (TmC AC (term$Pair t1 t2) c ⇔ ∃c1 c2. c = cp (cn 1) (cp c1 c2) ∧
                                        TmC AC t1 c1 ∧ TmC AC t2 c2) ∧
  (TmC AC (term$Const ct) c ⇔ ∃c0. c = cp (cn 2) c0 ∧ AC ct c0)
End

Theorem TmC_RIGHT_THM[simp]:
  (TmC AC t (cp (cn 0) (cn n)) ⇔ t = Var n) ∧
  (TmC AC t (cp (cn 1) (cp c1 c2)) ⇔
     ∃t1 t2. t = Pair t1 t2 ∧ TmC AC t1 c1 ∧ TmC AC t2 c2) ∧
  (TmC AC t (cp (cn 2) c) ⇔ ∃a. AC a c ∧ t = Const a)
Proof
  simp[EQ_IMP_THM, PULL_EXISTS] >> rpt conj_tac >>
  Cases_on ‘t’ >> simp[]
QED

Theorem TmVar_C[transfer_rule]:
  (NC |==> TmC AC) term$Var (cp (cn 0))
Proof
  simp[FUN_REL_def, NC_def]
QED

Theorem TmPair_C[transfer_rule]:
  (TmC AC |==> TmC AC |==> TmC AC) term$Pair (λc1 c2. cp (cn 1) (cp c1 c2))
Proof
  simp[FUN_REL_def]
QED

Theorem TmConst_C[transfer_rule]:
  (AC |==> TmC AC) term$Const (cp (cn 2))
Proof
  simp[FUN_REL_def]
QED

Theorem total_TmC[transfer_simp]:
  total AC ⇒ total (TmC AC)
Proof
  simp[total_def] >> strip_tac >> Induct >> gvs[] >> metis_tac[]
QED

Theorem left_unique_TmC[transfer_simp]:
  left_unique AC ⇒ left_unique (TmC AC)
Proof
  simp[left_unique_def] >> strip_tac >> Induct >> gvs[PULL_EXISTS] >>
  metis_tac[]
QED

Theorem right_unique_TmC[transfer_simp]:
  right_unique AC ⇒ right_unique (TmC AC)
Proof
  simp[right_unique_def] >> strip_tac >> Induct >> gvs[PULL_EXISTS] >>
  metis_tac[]
QED

Inductive is_cvterm:
[~var:]
  is_cvterm Cs (cp (cn 0) (cn n))
[~pair:]
  is_cvterm Cs c1 ∧ is_cvterm Cs c2 ⇒
  is_cvterm Cs (cp (cn 1) (cp c1 c2))
[~const:]
  c ∈ Cs ⇒ is_cvterm Cs (cp (cn 2) c)
End

Theorem RRANGE_TmC[transfer_simp]:
  RRANGE (TmC AC) = is_cvterm (RRANGE AC)
Proof
  simp[relationTheory.RRANGE, FUN_EQ_THM, EQ_IMP_THM, FORALL_AND_THM,
       PULL_EXISTS] >> conj_tac >~
  [‘TmC _ _ _ ⇒ _’]
  >- (rpt gen_tac >> rename [‘TmC AC t c’] >> qid_spec_tac ‘c’ >>
      Induct_on ‘t’ >> simp[is_cvterm_rules, PULL_EXISTS] >>
      rw[] >> irule is_cvterm_const >>
      simp[IN_DEF, relationTheory.RRANGE, SF SFY_ss]) >>
  Induct_on ‘is_cvterm’ >> simp[IN_DEF, relationTheory.RRANGE] >>
  metis_tac[]
QED

val _ = export_theory();
