open HolKernel Parse boolLib bossLib;

open pairTheory pred_setTheory
open modalBasicsTheory

val _ = new_theory "tableauBasics";

Overload gsize = “λl. SUM (MAP nnfform_size l)”
Overload form_size = “nnfform_size”

Definition is_literal_def[simp]:
  (is_literal (Var _) ⇔ T) ∧ (is_literal (NVar _) ⇔ T) ∧ (is_literal _ ⇔ F)
End

Definition is_conj_def[simp]:
  is_conj (Conj _ _ ) = T ∧
  is_conj _ = F
End

Definition is_disj_def[simp]:
  is_disj (Disj f1 f2) = T ∧
  is_disj _ = F
End

Definition is_dia_def[simp]:
  is_dia (Dia _) = T ∧
  is_dia _ = F
End

Definition dest_dia_def[simp]:
  dest_dia (Dia f) = f
End

Definition is_box_def[simp]:
  is_box (Box _) = T ∧
  is_box _ = F
End

Definition contradiction_def[simp]:
  (contradiction [] ⇔ NONE) ∧
  (contradiction (Var n :: rest) ⇔
     if MEM (NVar n) rest then SOME n
     else contradiction rest) ∧
  (contradiction (NVar n :: rest) ⇔
     if MEM (Var n) rest then SOME n else  contradiction rest) ∧
  (contradiction (_ :: rest) ⇔ contradiction rest)
End

Theorem contradiction_EQ_NONE:
  ∀Γ. contradiction Γ = NONE ⇔ ∀n. MEM (Var n) Γ ⇒ ¬MEM (NVar n) Γ
Proof
  Induct >> simp[] >> Cases >> simp[AllCaseEqs()] >> metis_tac[]
QED

Theorem contradiction_EQ_SOME:
  (contradiction Γ = SOME i) ⇒ MEM (Var i) Γ ∧ MEM (NVar i) Γ
Proof
  Induct_on ‘Γ’ >> simp[] >> Cases >> simp[AllCaseEqs()] >> metis_tac[]
QED


Definition conjsplit_def[simp]:
  (conjsplit (Conj f1 f2 :: rest) = SOME (f1 :: f2 :: rest)) ∧
  (conjsplit (f :: rest) = OPTION_MAP (CONS f) (conjsplit rest)) ∧
  (conjsplit [] = NONE)
End

Theorem conjsplit_EQ_NONE:
  ∀Γ. conjsplit Γ = NONE ⇔ ∀f1 f2. ¬(MEM (Conj f1 f2) Γ)
Proof
  Induct >> simp[] >> Cases >> simp[] >> metis_tac[]
QED

Theorem MEM_conjsplit:
  ∀Γ₀ Γ ϕ. conjsplit Γ₀ = SOME Γ ∧ MEM ϕ Γ₀ ⇒
            (∃ϕ₁ ϕ₂. ϕ = Conj ϕ₁ ϕ₂ ∧ MEM ϕ₁ Γ ∧ MEM ϕ₂ Γ) ∨
            MEM ϕ Γ
Proof
  Induct >> simp[] >> Cases >> simp[PULL_EXISTS] >> metis_tac[]
QED

Theorem conjsplit_MEM2:
  ∀Γ₀ Γ ϕ. conjsplit Γ₀ = SOME Γ ∧ MEM ϕ Γ ⇒
           MEM ϕ Γ₀ ∨ (∃ϕ'. MEM (Conj ϕ ϕ') Γ₀) ∨
           (∃ϕ'. MEM (Conj ϕ' ϕ) Γ₀)
Proof
  Induct >> simp[] >> Cases >> csimp[PULL_EXISTS] >> metis_tac[]
QED

Theorem conjsplit_size:
  ∀Γ fs. conjsplit Γ = SOME fs ⇒ gsize fs < gsize Γ
Proof
  Induct >> simp[conjsplit_def] >> Cases >>
  simp[conjsplit_def, FORALL_PROD, PULL_EXISTS]
QED

Definition disjsplit_def[simp]:
  disjsplit (Disj f1 f2 :: rest) = SOME (f1::rest, f2::rest) ∧
  disjsplit (f :: rest) = OPTION_MAP (CONS f ## CONS f) (disjsplit rest) ∧
  disjsplit [] = NONE
End

Theorem disjsplit_size:
  ∀Γ fs1 fs2. disjsplit Γ = SOME (fs1, fs2) ⇒
                  SUM (MAP form_size fs1) < SUM (MAP form_size Γ) ∧
                  SUM (MAP form_size fs2) < SUM (MAP form_size Γ)
Proof
  Induct_on ‘Γ’ >> simp[disjsplit_def] >> Cases >>
  simp[disjsplit_def, FORALL_PROD, PULL_EXISTS]
QED

Theorem disjsplit_EQ_NONE:
  ∀Γ. disjsplit Γ = NONE ⇔ ∀f1 f2. ¬(MEM (Disj f1 f2) Γ)
Proof
  Induct >> simp[] >> Cases >> simp[] >> metis_tac[]
QED

Theorem MEM_disjsplit:
  ∀Γ Γ1 Γ2 ϕ.
    disjsplit Γ = SOME (Γ1, Γ2) ∧ MEM ϕ Γ ⇒
      (∃ϕ₁ ϕ₂. ϕ = Disj ϕ₁ ϕ₂ ∧ MEM ϕ₁ Γ1 ∧ MEM ϕ₂ Γ2) ∨
      MEM ϕ Γ1 ∧ MEM ϕ Γ2
Proof
  Induct >> dsimp[] >> conj_tac >> Cases >> simp[EXISTS_PROD, PULL_EXISTS] >>
  metis_tac[]
QED

Theorem disjsplit_MEM2:
  ∀Γ Γ1 Γ2 f1 f2.
     MEM f1 Γ1 ∧ MEM f2 Γ2 ∧ disjsplit Γ = SOME (Γ1,Γ2) ⇒
     MEM f1 Γ ∨ MEM f2 Γ ∨ MEM (Disj f1 f2) Γ
Proof
  Induct >> simp[] >> Cases >> simp[PULL_EXISTS, EXISTS_PROD] >> metis_tac[]
QED



Definition unbox_def[simp]:
  unbox (Box f :: rest) = f :: unbox rest ∧
  unbox (f :: rest) = unbox rest ∧
  unbox [] = []
End

Theorem MEM_unbox:
  MEM ϕ (unbox Γ) ⇔ MEM (Box ϕ) Γ
Proof
  Induct_on ‘Γ’ >> simp[] >> Cases >> simp[] >> metis_tac[]
QED

Theorem unbox_APPEND:
  unbox (Γ ++ Δ) = unbox Γ ++ unbox Δ
Proof
  Induct_on ‘Γ’ >> simp[] >> Cases >> simp[]
QED


Definition undia_def[simp]:
  undia (Dia f :: rest) = f :: undia rest ∧
  undia (f :: rest) = undia rest ∧
  undia [] = []
End

Theorem MEM_undia:
  MEM ϕ (undia Γ) ⇔ MEM (Dia ϕ) Γ
Proof
  Induct_on ‘Γ’ >> simp[] >> Cases >> simp[]
QED

Definition unvar_def[simp]:
  unvar (Var n :: rest) = n :: unvar rest ∧
  unvar (f :: rest) = unvar rest ∧
  unvar [] = []
End

Theorem MEM_unvar[simp]:
  MEM n (unvar Γ) ⇔ MEM (Var n) Γ
Proof
  Induct_on ‘Γ’ >> simp[] >> Cases >> simp[]
QED

(* a standard tree model where the numbers at each node correspond to the
   variables true at that world *)
Datatype: tmodel = Nd (num list) (tmodel list)
End

Theorem tmodel_size_def[simp,allow_rebind] = definition "tmodel_size_def"

Theorem MEM_tmodel_size:
  MEM t ts ⇒ tmodel_size t < tmodel1_size ts
Proof
  Induct_on ‘ts’ >> rw[] >> res_tac >> simp[]
QED

Theorem tmodel_ind:
  ∀P. (∀vs ts. (∀t. MEM t ts ⇒ P t) ⇒ P (Nd vs ts)) ⇒
      (∀t. P t)
Proof
  rpt strip_tac >>
  completeInduct_on ‘tmodel_size t’ >> Cases >>
  rw[] >> fs[PULL_FORALL] >> last_x_assum irule >> rpt strip_tac >>
  first_x_assum irule >> drule MEM_tmodel_size >> simp[]
QED

val _ = TypeBase.update_induction tmodel_ind

(* standard one-step in a tree relation *)
Definition tree_rel_def:
  tree_rel t1 t2 ⇔ ∃vs ts. t1 = Nd vs ts ∧ MEM t2 ts
End

Theorem tree_rel_size_bounds:
  tree_rel t1 t2 ⇒ tmodel_size t2 ≤ tmodel_size t1
Proof
  simp[tree_rel_def, PULL_EXISTS] >> rw[] >>
  drule MEM_tmodel_size >> simp[]
QED

Definition subtree_def:
  subtree t1 t2 ⇔ tree_rel^* t2 t1
End

Theorem forces_grows_backward:
  ∀w. forces M1 w f ∧ M2.valt = M1.valt ∧ M2.frame.rel = M1.frame.rel ∧
      M1.frame.world ⊆ M2.frame.world ∧ w ∈ M1.frame.world ∧
      (∀w1 w2. M1.frame.rel w1 w2 ∧ w1 ∈ M1.frame.world ⇒ w2 ∈ M1.frame.world) ⇒
      forces M2 w f
Proof
  Induct_on ‘f’ >> simp[]
  >- metis_tac[SUBSET_DEF]
  >- metis_tac[SUBSET_DEF]
  >- metis_tac[]
  >- metis_tac[]
  >- (rw[] >> fs[] >> metis_tac[SUBSET_DEF])
  >- (rw[] >> fs[] >> metis_tac[SUBSET_DEF])
QED

Overload scmap = “list$OPT_MMAP”
Theorem scmap_MEM:
  ∀l0 l e f. scmap f l0 = SOME l ∧ MEM e l ⇒ ∃e0. MEM e0 l0 ∧ f e0 = SOME e
Proof
  Induct >> dsimp[AllCaseEqs()]
QED

Theorem scmap_MEM2:
  ∀l0 l e0 f. scmap f l0 = SOME l ∧ MEM e0 l0 ⇒ ∃e. MEM e l ∧ f e0 = SOME e
Proof
  Induct >> dsimp[AllCaseEqs()]
QED

Theorem scmap_EQ_NONE[simp]:
  ∀l f. scmap f l = NONE ⇔ ∃e. MEM e l ∧ f e = NONE
Proof
  Induct >> dsimp[AllCaseEqs()] >> metis_tac[TypeBase.nchotomy_of “:α option”]
QED



val _ = export_theory();
