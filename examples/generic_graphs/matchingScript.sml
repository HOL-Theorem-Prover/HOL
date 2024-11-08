open HolKernel Parse boolLib bossLib;
open fsgraphTheory pred_setTheory arithmeticTheory listTheory genericGraphTheory;
open rich_listTheory;
val _ = new_theory "matching";

Overload V[local] = “nodes (G :fsgraph)”
Overload E[local] = “fsgedges (G :fsgraph)”

Definition matching_def:
  matching (G: fsgraph) M ⇔ (M ⊆ fsgedges G) ∧ (∀e1 e2. e1 ∈ M ∧ e2 ∈ M ∧ e1 ≠ e2 ⇒ DISJOINT e1 e2)
End

Theorem matching_def':
  matching (G: fsgraph) M ⇔ (M ⊆ fsgedges G) ∧ (∀e1 e2. e1 ∈ M ∧ e2 ∈ M ⇒ e1 ≠ e2 ⇒ DISJOINT e1 e2)
Proof
  METIS_TAC [matching_def]
QED

Definition matched_def:
  matched G M v ⇔ matching G M ⇒ ∃e. e ∈ M ∧ v ∈ e
End

Definition unmatched_def:
  unmatched G M v ⇔ matching G M ∧ ∀e. e ∈ M ⇒ v ∉ e
End

Theorem matched_def_eq:
  ∀G M v. unmatched G M v ⇔ ~matched G M v
Proof
  rw [matched_def, unmatched_def] >> METIS_TAC []
QED

Definition matching_of_nodes_def:
  matching_of_nodes (G: fsgraph) M U
  ⇔ ∀v. v ∈ U ⇒ matched G M v
End


(* Definition vertex_cover_def: *)
(*   vertex_cover G U ⇔ U ⊆ nodes G ∧ ∀e. e ∈ fsgedges G ⇒ ∃v. v ∈ U ∧ v ∈ e *)
(* End *)

Definition gen_vertex_cover_def:
  gen_vertex_cover ns es U ⇔ U ⊆ ns ∧ ∀e. e ∈ es ⇒ ∃v. v ∈ U ∧ v ∈ e
End

Theorem gen_vertex_cover_subset:
  ∀ns es1 es2 U. gen_vertex_cover ns es1 U ∧ es2 ⊆ es1 ⇒ gen_vertex_cover ns es2 U
Proof
  METIS_TAC [gen_vertex_cover_def, SUBSET_DEF]
QED

    
Overload vertex_cover = “\(G: fsgraph) U. gen_vertex_cover V E U”


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
  ∀(G: fsgraph) P. path G (REVERSE P) ⇔ path G P
Proof
  rw [path_def]
QED

Theorem adj_list_take_lemma:
  ∀(ls: 'a list) x y n. adjacent (TAKE n ls) x y ⇒ 1 < n ⇒ adjacent ls x y
Proof
  rw [adjacent_iff]
  >> Q.ABBREV_TAC ‘ls_n = TAKE n ls’
  >> Cases_on ‘LENGTH ls ≤ n’
  >- gvs [TAKE_LENGTH_TOO_LONG]

  >> ‘ls_n ≠ []’ by METIS_TAC [adjacent_thm]
  >> qsuff_tac ‘ls ≠ []’
  >- (rw []
      >> ‘∃z1 z2 zs. ls = z1::zs ∨ ls = z1::z2::zs’ by METIS_TAC [LIST_NOT_NIL]
      >- (rw [] >> irule (cj 2 adjacent_rules)

       )
      >- (

       )
     )
QED

Theorem alternating_path_prefix:
  ∀(G: fsgraph) M P n. alternating_path G M P ⇒ 0 < n ⇒ alternating_path G M (TAKE n P)
Proof
  rw [alternating_path_def]     (* 3 *)
  >- (rw [path_def, walk_def]   (* 4 *)
      >- METIS_TAC [path_def, walk_def]
      >- METIS_TAC [MEM_TAKE, path_def, walk_def]
      >-

  )
QED


(* Theorem augmenting_path_reversible: *)
(*   ∀G M P. matching G M ⇒ augmenting_path G M P ⇒ augmenting_path G M (REVERSE P) *)
(* Proof *)

(* QED *)


Theorem matching_exists:
  ∃x. matching G x
Proof
  Q.EXISTS_TAC ‘∅’ >> simp [matching_def]
QED


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

(* Definition max_matching_def: *)
(*   max_matching (G: fsgraph) M ⇔ matching G M ∧ ∀N. matching G N ⇒ CARD N ≤ CARD M *)
(* End *)

(* Theorem max_matching_def_image_card: *)
(*   max_matching G M ⇔ matching G M ∧ CARD M = MAX_SET (IMAGE CARD (matching G)) *)
(* Proof *)
(*   qsuff_tac ‘CARD M = MAX_SET (IMAGE CARD (matching G)) ⇔ ∀N. matching G N ⇒ CARD N ≤ CARD M’ *)
(*   >- rw [max_matching_def] *)
(*   >> Q.SPECL_THEN [‘N’, ‘matching G’] (fn t => rw [t]) (GSYM IN_APP) *)
(*   >> Q.SPECL_THEN [‘IMAGE CARD (matching G)’] MP_TAC MAX_SET_TEST_IFF *)
(*   >>   *)
(* QED *)

(* Q.SPECL [‘matching G’, ‘CARD’] *)
Theorem maximal_matching_exists:
  ∀(G: fsgraph). ∃M. matching G M ∧ ∀N. matching G N ⇒ CARD N ≤ CARD M
Proof
  GEN_TAC
  >> Q.SPECL_THEN [‘CARD’, ‘{M | matching G M}’] MP_TAC (GEN_ALL FINITE_is_measure_maximal)
  >> simp[is_measure_maximal_def, finite_num_matching]
  >> disch_then irule
  >> rw[EXTENSION] >> rw [matching_exists]
QED

(* M (* maximal matching  *) *)
(* Theorem maximal_matching_aug_path: *)
(*   ∀(G: fsgraph) M. matching G M ⇒ (CARD M = MAX_SET (IMAGE CARD (matching G)) ⇔ ∀p. ~augmenting_path G M p) *)
(* Proof *)
(*   rw [matching_def, augmenting_path_def, alternating_path_def] *)
(*   >> MATCH_MP_TAC [MAX_SET_TEST_IFF] *)
(* QED *)


Theorem vertex_cover_exists:
  ∃U. vertex_cover (G: fsgraph) U
Proof
  Q.EXISTS_TAC ‘V’ >> rw [gen_vertex_cover_def] \\
  Q.SPEC_THEN ‘G’ MP_TAC (alledges_valid) >> rw [] \\
  Q.EXISTS_TAC ‘a’ >> rw [COMPONENT]
QED


Theorem finite_num_vertex_cover:
  ∀(G: fsgraph). FINITE {U | vertex_cover G U}
Proof
  rw []
  >> irule SUBSET_FINITE_I
  >> Q.EXISTS_TAC ‘POW V’
  >> rw [SUBSET_DEF, IN_POW]
  >> gvs [gen_vertex_cover_def, SUBSET_DEF]
QED

Theorem finite_num_vertex_cover':
  ∀(G: fsgraph). FINITE (vertex_cover G)
Proof
  ‘∀(G: fsgraph). vertex_cover G = {U | vertex_cover G U}’ by rw [GSPEC_ETA]
  >> rw [finite_num_vertex_cover]
QED

Theorem minimal_vertex_cover_exists:
  ∀(G: fsgraph). ∃U. vertex_cover G U ∧ ∀E. vertex_cover G E ⇒ CARD U ≤ CARD E
Proof                           (* TODO *)
  (* By finite_num_vertex_cover, (vertex_cover G) attains a minimum;
  However the lemma is missing unlike the maximum.
  I could define a strictly decreasing map to define another measure.
  IF m: 'a -> num is a measure on set X, then m' = (max_set(image m X) - m) is also one.
  wherever m'(x) attains a maximum is where m(x) sttains a minimum.
   *)
  cheat
QED

(* Lemma: if U covers a matching M, then |M| ≤ |U|. *)
Theorem vertex_cover_matching_card:
  gen_vertex_cover V M U ∧ matching G M ⇒ CARD M ≤ CARD U
Proof
  STRIP_TAC >> irule INJ_CARD >> CONJ_TAC
  >- (irule SUBSET_FINITE >> Q.EXISTS_TAC ‘V’
      >> gvs [gen_vertex_cover_def]
     )
  >> Q.EXISTS_TAC ‘\e. @x. x ∈ e ∧ x ∈ U’
  >> rw [INJ_DEF]
  >- (SELECT_ELIM_TAC
      >> simp []
      >> gvs [gen_vertex_cover_def]
      >> simp []
      >> METIS_TAC []
     )
  >- (gvs [matching_def']
      >> pop_assum MP_TAC >> rpt SELECT_ELIM_TAC >> rw []
      >- METIS_TAC [gen_vertex_cover_def]
      >- METIS_TAC [gen_vertex_cover_def]
      >- (‘x ∈ e ∩ e'’ by rw [INTER_DEF]
          >> Cases_on ‘DISJOINT e e'’
          >- METIS_TAC [NOT_IN_EMPTY, DISJOINT_DEF]
          >- (gvs [DISJOINT_DEF, matching_def'] >> METIS_TAC [matching_def'])
       )
      )
QED



Theorem matching_insert:
  matching G (e INSERT M) ⇔ matching G M ∧ (DISJOINT e (BIGUNION M) ∨ e ∈ M) ∧ e ∈ E
Proof
  Cases_on ‘e ∈ M’
  >- (simp [ABSORPTION_RWT]
      >> simp [matching_def]
      >> ASM_SET_TAC []
     )
  >> rw [EQ_IMP_THM]  (* 4 *)
  >- gvs [matching_def]
  >- (gvs [matching_def]
      >> Q.PAT_X_ASSUM ‘∀e1 e2. _’ (fn t => Q.SPECL_THEN [‘e’, ‘s'’] MP_TAC t)
      >> rw [] >> pop_assum irule
      >> ASM_SET_TAC []
     )
  >- gvs [matching_def]
  >> gvs [matching_def]
  >> rpt GEN_TAC
  >> Cases_on ‘e1 = e2’         (* 2 *)
  >- rw []
  >> Cases_on ‘e1 ∈ M ∧ e2 ∈ M’ (* 2 *)
  >- rw []
  >> gvs []                     (* 2 *)
  >- (rw [] >> simp [])
  >> rw [Once DISJOINT_SYM]
  >> Q.PAT_X_ASSUM ‘∀s. s ∈ M ⇒ _’ (fn t => Q.SPEC_THEN ‘e1’ irule t)
  >> rw []
QED




Theorem DISJOINT_elem_lemma:
  DISJOINT A B ⇔ ∀x y. (x ∈ A ∧ y ∈ B) ⇒ x ≠ y
Proof
  ASM_SET_TAC []
QED

Theorem DISJOINT_pair_elem_lemma2:
  DISJOINT {a; b} {c; d} ⇔ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d
Proof
  ASM_SET_TAC []
QED

Theorem LAST_EL_LENGTH_lemma:
  ∀n ls. LENGTH ls = SUC n ⇒ LAST ls = EL n ls
Proof
  rw [] >> sg ‘ls ≠ []’
  >- METIS_TAC [SUC_NOT_ZERO, LENGTH_NIL]
  >> Q.ABBREV_TAC ‘sl = REVERSE ls’
  >> sg ‘sl ≠ []’
  >- (‘∃x xs. ls = x::xs’ by METIS_TAC [LIST_NOT_NIL] >> rw [Abbr ‘sl’, REVERSE_DEF]
     )
  >> ‘∃y ys. sl = y::ys’ by METIS_TAC [LIST_NOT_NIL]
  >> rw []
  >> ONCE_REWRITE_TAC [GSYM REVERSE_REVERSE]
  >> FIRST_ASSUM (fn t => ONCE_REWRITE_TAC [t])
  >> rw [LAST_REVERSE]
  >> sg ‘LENGTH ys = n’
  >- (‘LENGTH (y::ys) = SUC n’ by METIS_TAC [LENGTH_REVERSE]
      >> ‘ys = DROP 1 (y::ys)’ by rw [DROP_1]
      >> pop_assum (fn t => ONCE_REWRITE_TAC [t])
      >> rw [LENGTH_DROP]
     )
  >> Q.SPECL_THEN [‘0’, ‘n’, ‘(REVERSE ys ++ [y])’] MP_TAC (GSYM EL_DROP) >> rw []
  >> ‘LENGTH ys = LENGTH $ REVERSE ys’ by rw [LENGTH_REVERSE]
  >> pop_assum (fn t => ONCE_REWRITE_TAC [t])
  >> rw [DROP_LENGTH_APPEND]
QED

(* flips an implication into contrapositive form *)
val contrapos_tac = rw [Once MONO_NOT_EQ];

fun my_tac t =
 ‘x ∈ fsgedges G ∧ y ∈ fsgedges G’ by METIS_TAC [matching_def, SUBSET_DEF]
       >> ‘DISJOINT x y’ by METIS_TAC [matching_def] >> pop_assum MP_TAC
       >> rw [DISJOINT_DEF, INTER_DEF, GSYM MEMBER_NOT_EMPTY]
       >> Q.EXISTS_TAC t
       >> METIS_TAC [COMPONENT, genericGraphTheory.INSERT2_lemma];



(* Konig 1931, page 37*)
Theorem max_matching_min_cover_card_eq:
  ∀G. bipartite G ⇒ MAX_SET (IMAGE CARD (matching G)) = MIN_SET (IMAGE CARD (vertex_cover G))
Proof                           (* TODO *)
  (*  *)
  rw [bipartite_alt]
  >> Q.SPEC_THEN ‘G’ MP_TAC maximal_matching_exists
  >> STRIP_TAC
  >> gvs [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]
  >> rename [‘_ = {Aend _; Bend _}’] (* This is to easily define f as well as find two ends in a bipartition. *)
  >> Q.ABBREV_TAC ‘f = \e. if ∃p. alternating_path G M p ∧ HD p ∈ A ∧ LAST p = Bend e then Bend e else Aend e’
  >> Q.ABBREV_TAC ‘U = IMAGE f M’
  >> sg ‘CARD M = CARD U’       (* I probably need this outside the subgoal *)
  >- (Q.SPECL_THEN [‘f’,‘M’] MP_TAC CARD_IMAGE_INJ
      >> Q.SPECL_THEN [‘G’,‘M’] MP_TAC finite_matching
      >> rw []
      >> pop_assum (irule o GSYM)
      >> (rw[Abbr ‘f’] >> CCONTR_TAC) (* So that all 4 subgoals are contradiction *)
      (*
            Below is tediously repetitive - subgoals only differ in assumption "u = v"
            where u ∈ {Aend x; Bend x;} and v ∈ {Aend y; Bend y};
      *)
      >- (my_tac ‘Bend x’)
      >- (my_tac ‘Aend x’)
      >- (my_tac ‘Bend x’)
      >- (my_tac ‘Aend x’)
     )
  >> sg ‘MAX_SET (IMAGE CARD (matching G)) = CARD M’
  >- (Q.SPEC_THEN ‘IMAGE CARD (matching G)’ MP_TAC MAX_SET_TEST_IFF
      >> impl_tac
      >- (CONJ_TAC
          >- (irule IMAGE_FINITE
              >> rw [finite_num_matching'])
          >- (rw [EXTENSION]
              >> rw [matching_exists, IN_APP]))
      >> DISCH_THEN (MP_TAC o Q.SPEC ‘CARD (M: (unit + num -> bool) -> bool)’)
      >> impl_tac
      >- (
       rw []
       >> Q.EXISTS_TAC ‘M’
       >> rw [IN_APP]
       )
      >- (rw [IN_DEF] >> METIS_TAC [maximal_matching_exists])
     )
  (* Proof CARD U = MIN_SET (...)
     by >= ∧ <= *)
  >> pop_assum SUBST1_TAC
  >> qsuff_tac ‘vertex_cover G U’
  >- (STRIP_TAC
      >> irule MIN_SET_TEST >> simp [PULL_EXISTS]
      >> Q.EXISTS_TAC ‘U’ >> simp []
      >> simp [EXTENSION, PULL_EXISTS]
      >> Q.EXISTS_TAC ‘U’ >> simp []
      >> CCONTR_TAC >> gvs [NOT_LE]
      >> rename [‘CARD U' < CARD U’]
      >> ‘gen_vertex_cover V M U'’ by METIS_TAC [gen_vertex_cover_subset, matching_def]
      >> ‘CARD M ≤ CARD U'’ by METIS_TAC [vertex_cover_matching_card]
      >> rw [LET_TRANS]
     )
  >> rw [gen_vertex_cover_def]
  (* RTP: U ⊆ V *)
  >- (‘M ⊆ E’ by gvs [matching_def]
      >> pop_assum MP_TAC
      >> rw [Abbr ‘U’, SUBSET_DEF]
      >> rw [Abbr ‘f’]
      >- METIS_TAC [Q.SPEC ‘G’ fsgraph_valid]
      >- METIS_TAC [Q.SPEC ‘G’ fsgraph_valid]
     )
  (* RTP: ∃v. v ∈ U ∧ v ∈ e *)
  >> qsuff_tac ‘Aend e ∉ U ⇒ Bend e ∈ U’
  >- METIS_TAC [COMPONENT, INSERT2_lemma]
  >> DISCH_TAC
  >> sg ‘∀e. e ∈ E ⇒ Aend e ≠ Bend e’
  >- (rpt STRIP_TAC >> ASM_SET_TAC [])
  >> Cases_on ‘unmatched G M (Aend e)’
  >- (Cases_on ‘unmatched G M (Bend e)’
      >- (sg ‘matching G (e INSERT M)’
          >- (rw [matching_insert]
              >> gvs [unmatched_def]
              >> DISJ1_TAC >> rpt STRIP_TAC
              >> ‘e = {Aend e; Bend e}’ by METIS_TAC []
              >> pop_assum SUBST1_TAC
              >> simp [DISJOINT_DEF]
             )
          >> sg ‘e ∉ M’
          >- (gvs [unmatched_def]
              >> STRIP_TAC
              >> FIRST_X_ASSUM drule
              >> METIS_TAC [COMPONENT]
             )
          >> Q.PAT_X_ASSUM ‘∀N. matching G N ⇒ _’ drule
          >> ‘FINITE M’ by METIS_TAC [finite_matching]
          >> simp []
         )
      >- (simp [Abbr ‘f’, Abbr ‘U’, AllCaseEqs ()] >> simp [EXISTS_OR_THM]
          >> gvs [AllCaseEqs (), FORALL_AND_THM]
          >> pop_assum MP_TAC >> rw [unmatched_def]
          >> qexists_tac ‘e'’ >> rw []
          >> DISJ1_TAC
          >> sg ‘Bend e' = Bend e’
          >- (‘e' ∈ E’ by ASM_SET_TAC [matching_def]
              >> LAST_ASSUM drule
              >> STRIP_TAC
              >> ‘Bend e = Aend e' ∨ Bend e = Bend e'’ by ASM_SET_TAC []
              >- METIS_TAC [DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY]
              >> rw []
             )
          >> rw []
          >> qexists_tac ‘[Aend e; Bend e]’ >> rw []
          >> rw [alternating_path_def]
          >- (rw [path_def, walk_def]
              >- ASM_SET_TAC []
              >- ASM_SET_TAC []
              >> gvs [adjacent_iff, adjacent_fsg]
              >> METIS_TAC []
             )
          >- (‘n = 0’ by simp []
              >> gvs [unmatched_def]
              >> STRIP_TAC
              >> FIRST_X_ASSUM drule
              >> simp []
             )

         )
     )
  >> gvs [unmatched_def]
  >> ‘e' ∈ E’ by ASM_SET_TAC [matching_def]
  >> ‘Aend e = Aend e'’ by ASM_SET_TAC []
  >> ‘Bend e' ∈ U’ by ASM_SET_TAC []
  >> Cases_on ‘e = e'’
  >- rw []
  >> sg ‘e ∉ M’
  >- (
     gvs [matching_def]
     >> ‘e' ∈ E’ by ASM_SET_TAC [matching_def]
     >> Q.PAT_X_ASSUM ‘∀e1 e2. _’ MP_TAC
     >> rw [Once MONO_NOT_EQ]
     >> Q.EXISTS_TAC ‘e’ >> Q.EXISTS_TAC ‘e'’
     >> ASM_SET_TAC []
  )
  >> sg ‘∃p. alternating_path G M p ∧ HD p ∈ A ∧ LAST p = Bend e'’
  >- (gvs [Abbr ‘U’, Abbr ‘f’]
      >> ‘e' = e''’ by ASM_SET_TAC [matching_def, DISJOINT_DEF]
      >> rw []
      >> pop_assum MP_TAC >> rw [Once MONO_NOT_EQ] >> rw []
      >> METIS_TAC []
     )
  >> Q.ABBREV_TAC ‘b = Bend e’
  >> Cases_on ‘matched G M b’
  >- (gvs [matched_def]
      >> gvs [Abbr ‘f’, Abbr ‘U’]
      >> ‘e''' = e'’ by ASM_SET_TAC [matching_def] >> rw []
      >> ‘LAST p = Bend e'’ by ASM_SET_TAC [] >> rw []
      >> ‘p ≠ []’ by METIS_TAC [alternating_path_def, path_def, walk_def]
      >> qexists_tac ‘e''’ >> rw [] (* 2 *)
      >- ASM_SET_TAC [matching_def]
      >> pop_assum MP_TAC >> rw [Once MONO_NOT_EQ]
      >> Q.ABBREV_TAC ‘a = Aend e’
      >> Q.ABBREV_TAC ‘b' = Bend e'’
      >> Cases_on ‘MEM b p’
      >- (Q.ABBREV_TAC ‘pb = TAKE (INDEX_OF b) p’




       )
      >> Q.ABBREV_TAC ‘pb'ab = p ++ [a] ++ [b]’
      >> qexists_tac ‘pb'ab’ >> rpt (reverse CONJ_TAC)
      >- (sg ‘LAST pb'ab = b’
          >- METIS_TAC [LAST_CONS, Abbr ‘pb'ab’, LAST_APPEND_NOT_NIL]
          >> pop_assum (fn t => ONCE_REWRITE_TAC [t])
          >> ASM_SET_TAC [matching_def]
         )
      >- (qsuff_tac ‘HD pb'ab = HD p’
          >- rw []
          >> ‘∃x xs. p = x::xs’ by METIS_TAC [LIST_NOT_NIL]
          >> rw [Abbr ‘pb'ab’]
         )
      >> rw [alternating_path_def]
      >- (rw [path_def]         (* 2 *)
          >- (rw [walk_def]
              >- rw [Abbr ‘pb'ab’]

           )
         )
     )


QED




   qsuff_tac ‘∃p. alternating_path G M p ∧ LAST p = Bend e’


  >- (rw []
      >> Cases_on ‘e ∈ M’
      >- (simp [Abbr ‘f’, Abbr ‘U’]
          >> qexists_tac ‘e’
          >> rw []
          >> pop_assum MP_TAC
          >> rw [Once MONO_NOT_EQ] (* contrapositive *)
          >> qexists_tac ‘p’
          >> rw []
         )
      (* Idea for case e ∈ E \ M: need to show ∃e2. e2 ∈ M ∧ Bend e2 = b.
         Obviously e ≠ ∅;
         Suppose no e' ∈ M satisfies Bend e' = b, it suffies to show
         the contradiction that N = {e} ∪ M is a matching.
         Why: If N is a matching, it is bigger than M.
         How: N is a matching because e is disjoint with all e' ∈ M.
       *)
      (* >> simp [Abbr ‘U’] *)
      >> CCONTR_TAC
      >> gvs []
      >> qsuff_tac ‘matching G (e INSERT M)’ (* 2 *)
      >- (STRIP_TAC
          >> FIRST_X_ASSUM drule
          >> simp [NOT_LE]
          >> Q.PAT_X_ASSUM ‘CARD _ = CARD _’ (simp o single o SYM)
          >> ‘FINITE M’ suffices_by simp []
          >> irule finite_matching
          >> qexists_tac ‘G’ >> rw []
         )
      >> rw [matching_insert]
      >> rename [‘Bend e1 ∉ U’, ‘e2 ∈ M’]
      >> ‘e2 ∈ E’ by ASM_SET_TAC [matching_def]
      >> Q.PAT_ASSUM ‘∀e. e ∈ E ⇒ _’ (Q.SPEC_THEN ‘e1’ MP_TAC)
      >> Q.PAT_X_ASSUM ‘∀e. e ∈ E ⇒ _’ (Q.SPEC_THEN ‘e2’ MP_TAC)
      >> rw [] >> gvs [Abbr ‘U’]


      >> rw [DISJOINT_elem_lemma2]


      >> ‘∀x. x ∈ M ⇒ Aend e1 ≠ f x ∧ Bend e1 ≠ f x’ by METIS_TAC []
      >> pop_assum (fn t => Q.SPEC_THEN ‘e2’ MP_TAC t) >> rw []
      >> simp [DISJOINT_elem_lemma]
      >> ‘∀y. y ∈ e2 ⇒ y ∉ e1’ suffices_by ASM_SET_TAC []
      >> rw []
      >> Cases_on ‘y = f e2’    (* 2 *)
      >- ASM_SET_TAC []
      >> rw []



      (* >> ‘y = Aend e2 ∨ y = Bend e2’ by ASM_SET_TAC [matching_def] *)
      (* >- (gvs [] >>  *)
      (*    ) *)
      (* >> CCONTR_TAC >> disch_t >> rw [Abbr ‘f’] (* 2 *) *)
      (* >- (qsuff_tac ‘Aend e ≠ Aend s'’ *)
      (*     >- (rw [] *)
      (*         >>  *)

      (*      ) *)
      (*    ) *)
      (*     >> ... *)




      >> qexists_tac ‘s'’ >> rw []
      >> Q.PAT_X_ASSUM ‘∀x. Aend e = _ ⇒ _’ MP_TAC >> b
     )


  (* RTP: ∃p. alternating_path G M p ∧ LAST p = Bend e *)
  >- (Cases_on ‘unmatched G M (Aend e)’
      >- (gvs [unmatched_def]
          >> qexists_tac ‘[Aend e; Bend e]’
          >> rw [alternating_path_def] (* 3 *)
          >- (rw [path_def, walk_def]
              (* Here we go again. TODO: Add Aend e ∈ V universally *)
              >- METIS_TAC [Q.SPEC ‘G’ fsgraph_valid]
              >- METIS_TAC [Q.SPEC ‘G’ fsgraph_valid]
              >- (rw [adjacent_fsg]
                  >> gvs [adjacent_iff]
                  >> METIS_TAC []
                 )
              >- (CCONTR_TAC >> METIS_TAC [DISJOINT_DEF, NOT_IN_EMPTY, IN_INTER])
             )
          >- rw [unmatched_def]
          >> ‘n = 0’ by simp []
          >> rw []
          >> STRIP_TAC
          >> FIRST_X_ASSUM drule
          >> simp []
          >> cheat
         )
      >> gvs [unmatched_def]
      >> rename1 ‘ab' ∈ M’
     )
)

)


  (* >> Q.ABBREV_TAC ‘mincard_vcover = MIN_SET (IMAGE CARD (vertex_cover G))’ *)
  (* >> rw [EQ_LESS_EQ] *)
  (* >- (sg ‘∀E. E ⊂ U ⇒ ~vertex_cover G E’ *)
  (*     >- (GEN_TAC *)
  (*         >> rw [PSUBSET_MEMBER] *)
  (*         >> rw [Abbr ‘mincard_vcover’, vertex_cover_def, PSUBSET_DEF, SUBSET_DEF, DIFF_DEF] *)
  (*         >> DISJ2_TAC *)
  (*         >> ‘∃e. e ∈ M ∧ ∀v. v ∈ e ⇒ v ∉ E’ suffices_by METIS_TAC [matching_def, SUBSET_DEF] *)
  (*         >> *)

          (* >> Q.EXISTS_TAC ‘@x. x ∈ M ∧ Aend x ∉ E ∧ Bend x ∉ E’ *)
          (* >> rw [matching_def] *)
          (* >- (rw [SELECT_THM] *)
          (*     >> ‘x ∈ M ∧ matching G M ⇒ x ∈ fsgedges G’ by METIS_TAC [matching_def, SUBSET_DEF] *)
          (*     >> pop_assum MP_TAC *)
          (*     >> simp [GSYM RES_SELECT_THM] *)
          (*     >> METIS_TAC [SELECT_THM, SELECT_AX] *)
          (*     ) *)
     (* Todo *)
QED





    



val _ = export_theory();

