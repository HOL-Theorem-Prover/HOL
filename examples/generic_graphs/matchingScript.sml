open HolKernel Parse boolLib bossLib;
open fsgraphTheory pred_setTheory arithmeticTheory listTheory genericGraphTheory;
open realTheory;
val _ = new_theory "matching";


Definition matching_def:
  matching (G: fsgraph) M ⇔ (M ⊆ fsgedges G) ∧ (∀e1 e2. e1 ∈ M ∧ e2 ∈ M ∧ e1 ≠ e2 ⇒ DISJOINT e1 e2)
End

Definition matching_of_def:
  matching_of (G: fsgraph) M U
              ⇔ matching G M ∧ U ⊆ nodes G ∧ (∀u. u ∈ U ⇒ (∃e. e ∈ M ∧ u ∈ e))
End

Definition unmatched_def:
  unmatched G M v ⇔ matching G M ∧ ∀e. e ∈ M ⇒ v ∉ e
End

Definition vertex_cover_def:
  vertex_cover G U ⇔ U ⊆ nodes G ∧ ∀e. e ∈ fsgedges G ⇒ ∃v. v ∈ U ∧ v ∈ e
End

(* Obsolete
Definition bipartite_graph_def:
  bipartite (G: fsgraph) ⇔ ∃V1 V2.
  V1 ⊆ nodes G ∧ V2 ⊆ nodes G ∧ V1 ∪ V2 = nodes G ∧ V1 ∩ V2 = ∅ ∧
  ∀e. e ∈ fsgedges G ⇒ ∃v1 v2. v1 ∈ e ∧ v2 ∈ e ∧ v1 ≠ v2 ∧ v1 ∈ V1 ∧ v2 ∈ V2
End
 *)


Definition alternating_path_def:
  alternating_path G M P ⇔ matching G M ∧ path G P ∧
                           unmatched G M (HD P) ∧
                           ∀(n: num). SUC n < LENGTH P ⇒ (ODD n ⇔ {EL n P; EL (SUC n) P} ∈ M)
End

Definition augmenting_path_def:
  augmenting_path G M P ⇔ alternating_path G M P ∧ unmatched G M (LAST P)
End

Theorem adjacent_reversible[simp]: (* TODO: chuck this elsewhere *)
  ∀l a b. adjacent (REVERSE l) a b ⇔ adjacent l b a
Proof
  ‘∀l a b. adjacent l b a ⇒ adjacent (REVERSE l) a b’ suffices_by METIS_TAC [REVERSE_REVERSE]
  >> Induct_on ‘list$adjacent’ >> rw []
    >- (simp[GSYM APPEND_ASSOC, Excl "APPEND_ASSOC"] >> simp [adjacent_append2]) >> cheat
QED


  
Theorem walk_reversible[simp]:
  ∀(G: fsgraph) P. walk G (REVERSE P) ⇔ walk G P
Proof
  rw [walk_def] >> METIS_TAC [adjacent_SYM]
QED

Theorem path_reversible[simp]:
  ∀G P. path G (REVERSE P) ⇔ path G P
Proof
  rw [path_def]
QED

  
Theorem augmenting_path_reversible:
  ∀G M P. matching G M ⇒ augmenting_path G M P ⇒ augmenting_path G M (REVERSE P)
Proof
  rw [augmenting_path_def, alternating_path_def, unmatched_def]
QED


Theorem finite_matching:
  ∀G M. matching G M ⇒ FINITE M
Proof
  rw[matching_def] >> irule SUBSET_FINITE_I >> Q.EXISTS_TAC ‘fsgedges G’ >> rw[]
QED

  (* FINITE_is_measure_maximal
Theorem max_measure_exists:
  ∀A m. FINITE A ∧ A ≠ ∅ ⇒ ∃a. a ∈ A ∧ ∀b. b ∈ A ⇒ m b ≤ m a
Proof
  Induct_on ‘FINITE’ >> rw[]
QED
*)

(* Q.SPECL [‘matching G’, ‘CARD’] *)
Theorem maximal_matching_exists:
  ∀(G: fsgraph). ∃M. matching G M ∧ ∀N. matching G N ⇒ CARD N ≤ CARD M
Proof                           (* TODO *)
  GEN_TAC >> Q.SPEC_THEN ‘{M | matching G M}’ MP_TAC FINITE_is_measure_maximal >> impl_tac
  >-                            (* TODO *)
QED

(* Berge's Theorem: https://en.wikipedia.org/wiki/Berge's_theorem *)
Theorem maximal_matching_no_aug:
  ∀G M. matching G M ⇒ (MAX_SET (IMAGE CARD (matching G)) = CARD M) ⇔ (∀P. path G P ⇒ ¬augmenting_path G M P)
Proof                           (* TODO *)

QED


(* Konig 1931, page 37*)
Theorem konig_matching_thm:
  ∀G. MAX_SET (IMAGE CARD (matching G)) = MIN_SET (IMAGE CARD (vertex_cover G))
Proof                           (* TODO *)

QED






    



val _ = export_theory();

