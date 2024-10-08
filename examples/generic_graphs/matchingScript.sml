open HolKernel Parse boolLib bossLib;
open fsgraphTheory pred_setTheory arithmeticTheory listTheory genericGraphTheory;
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


(* Theorem augmenting_path_reversible: *)
(*   ∀G M P. matching G M ⇒ augmenting_path G M P ⇒ augmenting_path G M (REVERSE P) *)
(* Proof *)
(*   rw [augmenting_path_def, alternating_path_def, unmatched_def] *)
(* QED *)


Theorem finite_matching:
  ∀G M. matching G M ⇒ FINITE M
Proof
  rw[matching_def] >> irule SUBSET_FINITE_I >> Q.EXISTS_TAC ‘fsgedges G’ >> rw[]
QED

Theorem finite_num_matching:
  ∀(G: fsgraph). FINITE {M | matching G M}
Proof
  (* M ⊆ E ⇒ M ∈ P(E); [IN_POW (<--)]
     ∀M. (matching G M ⇒ M ⊆ E) ⇒ {M | matching G M} ⊆ P(E) [new lemma∃]
     E is finite ⇒ P(E) is finite [FINITE_POW (<--)]
     P(E) is finite ∧ {M | matching G M} ⊆ P(E) ⇒ {M | matching G M} is finite [SUBSET_FINITE_I]
   *)
  (* pred_setTheory *)
  rw[]
  >> irule SUBSET_FINITE_I
  >> Q.EXISTS_TAC ‘POW (fsgedges G)’
  >> rw [SUBSET_DEF, IN_POW]
  >> gvs [matching_def, SUBSET_DEF]
QED

Theorem finite_num_matching':
  ∀(G: fsgraph). FINITE (matching G)
Proof
  GEN_TAC >> sg ‘matching G = {M | matching G M}’
  >- rw[EXTENSION, IN_APP]
  >> pop_assum (fn t => ONCE_REWRITE_TAC [t])
  >> rw [finite_num_matching]
QED

  (* FINITE_is_measure_maximal
Theorem max_measure_exists:
  ∀A m. FINITE A ∧ A ≠ ∅ ⇒ ∃a. a ∈ A ∧ ∀b. b ∈ A ⇒ m b ≤ m a
Proof
  Induct_on ‘FINITE’ >> rw[]
QED
*)

Theorem matching_exists:
  ∃x. matching G x
Proof
  Q.EXISTS_TAC ‘∅’ >> simp [matching_def]
QED

(* Q.SPECL [‘matching G’, ‘CARD’] *)
Theorem maximal_matching_exists:
  ∀(G: fsgraph). ∃M. matching G M ∧ ∀N. matching G N ⇒ CARD N ≤ CARD M
Proof
  GEN_TAC >> Q.SPECL_THEN [‘CARD’, ‘{M | matching G M}’] MP_TAC (GEN_ALL FINITE_is_measure_maximal)
  >> simp[is_measure_maximal_def, finite_num_matching]
  >> disch_then irule           (* discharge the matched assumption that matches irule? *)
  >> rw[EXTENSION] >> rw [matching_exists]
QED

(* Theorem maximal_matching_exists_alt: *)
(*   ∀(G: fsgraph). ∃M. matching G M ∧ CARD M = MAX_SET (IMAGE CARD (matching G)) *)
(* Proof *)
(*   GEN_TAC *)
(*   >> Q.SPECL_THEN [‘G’] MP_TAC maximal_matching_exists *)
(*   >> rw [] *)
(*   >> Q.EXISTS_TAC ‘M’ *)
(*   >> Q.SPEC_THEN ‘G’ MP_TAC finite_num_matching >> rw [] *)
(*   >> MP_TAC *)
(*   >> Q.SPEC_THEN ‘IMAGE CARD (matching G)’ MP_TAC in_max_set >> STRIP_TAC *)
(*   >> gvs [IMAGE_IN, CARD_IMAGE_INJ] >> simp [] *)
(*   >> rw [] *)
(* QED *)

(* Berge's Theorem: https://en.wikipedia.org/wiki/Berge's_theorem *)
(* Theorem maximal_matching_no_aug: *)
(*   ∀G M. matching G M ⇒ (MAX_SET (IMAGE CARD (matching G)) = CARD M) ⇔ (∀P. path G P ⇒ ¬augmenting_path G M P) *)
(* Proof                           (* TODO *) *)

(* QED *)




(* Konig 1931, page 37*)
Theorem konig_matching_thm:
  ∀G. bipartite G ⇒ MAX_SET (IMAGE CARD (matching G)) = MIN_SET (IMAGE CARD (vertex_cover G))
Proof                           (* TODO *)
  (*  *)
  rw [bipartite_alt]
  >> Q.SPEC_THEN ‘G’ MP_TAC maximal_matching_exists
  >> STRIP_TAC
  >> gvs [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]
  >> rename [‘_ = {Aend _; Bend _}’] (* This is to easily define f as well as find two ends in a bipartition. *)
  >> Q.ABBREV_TAC ‘f = \e. if ∃p. alternating_path G M p ∧ LAST p = Bend e then Bend e else Aend e’
  >> Q.ABBREV_TAC ‘U = IMAGE f M’
  (* >> Q.ABBREV_TAC ‘isMaxMatching = \m. matching G m ∧ (CARD m = MAX_SET (IMAGE CARD (matching G)))’ *)
  >> sg ‘MAX_SET (IMAGE CARD (matching G)) = CARD M’
  >- (Q.SPECL_THEN [‘IMAGE CARD (matching G)’] MP_TAC MAX_SET_TEST_IFF
      >> impl_tac
      >- (CONJ_TAC
          >- (irule IMAGE_FINITE
              >> rw [finite_num_matching'])
          >- (rw [EXTENSION]
              >> rw [matching_exists, IN_APP]))
      >> DISCH_THEN (MP_TAC o Q.SPEC ‘CARD (M: (unit + num -> bool) -> bool)’)
      >> impl_tac
      >- (rw []
          >> Q.EXISTS_TAC ‘M’
          >> rw [IN_APP])
      >- (
         (* pop_assum (fn t => rw [t]) *)
       sg ‘CARD M = CARD U’
       >- (Q.SPECL_THEN [‘f’,‘M’] MP_TAC CARD_IMAGE_INJ
           >> Q.SPECL_THEN [‘G’,‘M’] MP_TAC finite_matching
           >> rw []
           >> pop_assum (irule o GSYM)
           >> (rw[Abbr ‘f’] >> CCONTR_TAC) (* So that all 4 subgoals are contradiction *)
           (*
            Below is tediously repetitive - subgoals only differ in assumption "u = v"
            where u ∈ {Aend x; Bend x;} and v ∈ {Aend y; Bend y};
           *)
           >- (
            ‘x ∈ fsgedges G ∧ y ∈ fsgedges G’ by METIS_TAC [matching_def, SUBSET_DEF]
            >> ‘DISJOINT x y’ by METIS_TAC [matching_def] >> pop_assum MP_TAC
            >> rw [DISJOINT_DEF, INTER_DEF, GSYM MEMBER_NOT_EMPTY]
            >> Q.EXISTS_TAC ‘Bend x’
            >> METIS_TAC [COMPONENT, genericGraphTheory.INSERT2_lemma]
            )
           >- (
            ‘x ∈ fsgedges G ∧ y ∈ fsgedges G’ by METIS_TAC [matching_def, SUBSET_DEF]
            >> ‘DISJOINT x y’ by METIS_TAC [matching_def] >> pop_assum MP_TAC
            >> rw [DISJOINT_DEF, INTER_DEF, GSYM MEMBER_NOT_EMPTY]
            >> Q.EXISTS_TAC ‘Aend x’
            >> METIS_TAC [COMPONENT, genericGraphTheory.INSERT2_lemma]
            )
           >- (
            ‘x ∈ fsgedges G ∧ y ∈ fsgedges G’ by METIS_TAC [matching_def, SUBSET_DEF]
            >> ‘DISJOINT x y’ by METIS_TAC [matching_def] >> pop_assum MP_TAC
            >> rw [DISJOINT_DEF, INTER_DEF, GSYM MEMBER_NOT_EMPTY]
            >> Q.EXISTS_TAC ‘Bend x’
            >> METIS_TAC [COMPONENT, genericGraphTheory.INSERT2_lemma]
            )
           >- (
            ‘x ∈ fsgedges G ∧ y ∈ fsgedges G’ by METIS_TAC [matching_def, SUBSET_DEF]
            >> ‘DISJOINT x y’ by METIS_TAC [matching_def] >> pop_assum MP_TAC
            >> rw [DISJOINT_DEF, INTER_DEF, GSYM MEMBER_NOT_EMPTY]
            >> Q.EXISTS_TAC ‘Aend x’
            >> METIS_TAC [COMPONENT, genericGraphTheory.INSERT2_lemma]
            )
          )
       >> rw [IN_DEF]
       >> METIS_TAC [maximal_matching_exists]
       )
     )
  >> pop_assum (fn t => REWRITE_TAC [t])
  >>
     (* Todo *)
QED






    



val _ = export_theory();

