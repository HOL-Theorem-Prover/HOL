open HolKernel boolLib Parse bossLib

open vbgsetTheory vbgnatsTheory
open lcsymtacs
open boolSimps

val _ = new_theory "ordinal"

val poc_def = Define`
  poc A R ⇔
    (∀x. x ∈ A ⇒ R x x) ∧
    (∀x y z. x ∈ A ∧ y ∈ A ∧ z ∈ A ∧ R x y ∧ R y z ⇒ R x z) ∧
    (∀x y. x ∈ A ∧ y ∈ A ∧ R x y ∧ R y x ⇒ (x = y))
`;

val chain_def = Define`
  chain A R C ⇔ C ⊆ A ∧ ∀x y. x ∈ C ∧ y ∈ C ⇒ R x y ∨ R y x
`

val totalR_def = Define`
  totalR A R ⇔ poc A R ∧ ∀x y. x ∈ A ∧ y ∈ A ⇒ R x y ∨ R y x
`;

val iseg_def = Define`
  iseg A R x = SPEC0 (λy. y ∈ A ∧ R y x ∧ x ≠ y ∧ x ∈ A)
`;

val iseg_SUBSET = store_thm(
  "iseg_SUBSET",
  ``∀x y. x ∈ A ∧ y ∈ A ∧ totalR A R ∧ R x y ⇒ iseg A R x ⊆ iseg A R y``,
  rpt strip_tac >>
  `poc A R` by fs[totalR_def] >>
  `∀x y z. x ∈ A ∧ y ∈ A ∧ z ∈ A ∧ R x y ∧ R y z ⇒ R x z` by fs[poc_def] >>
  rw[iseg_def, SUBSET_def, SPEC0] >- metis_tac [] >>
  `R u y` by metis_tac [] >>
  strip_tac >> srw_tac [][] >>
  `∀x y. x ∈ A ∧ y ∈ A ∧ R x y ∧ R y x ⇒ (x = y)` by fs[poc_def] >>
  metis_tac[]);

val woclass_def = Define`
  woclass A R ⇔
     totalR A R ∧
     ∀B. B ⊆ A ∧ B ≠ {} ⇒ ∃e. e ∈ B ∧ ∀d. d ∈ B ⇒ R e d
`;

val Nats_SETs = prove(``n ∈ Nats ⇒ SET n``, metis_tac [SET_def])
val _ = augment_srw_ss [rewrites [Nats_SETs]]

val Nats_wo = store_thm(
  "Nats_wo",
  ``woclass Nats (λx y. x ≤ y)``,
  rw[woclass_def, totalR_def, poc_def, LE_ANTISYM]
    >- metis_tac [LE_TRANS]
    >- metis_tac [LE_TOTAL] >>
  `∃e. e ∈ B` by (fs[EXTENSION] >> metis_tac[]) >>
  metis_tac [Nats_least_element]);

val _ = export_theory()


