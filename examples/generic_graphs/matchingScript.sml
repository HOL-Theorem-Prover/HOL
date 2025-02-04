open HolKernel Parse boolLib bossLib;
open fsgraphTheory pred_setTheory arithmeticTheory listTheory genericGraphTheory;
open rich_listTheory;
open hurdUtils;
open tautLib;
val _ = new_theory "matching";

open realTheory;
open prim_recTheory;

Overload V[local] = “nodes (G :fsgraph)”;
Overload E[local] = “fsgedges (G :fsgraph)”;


(* Bipartite graph identities *)

Theorem gen_bipartite_sym:
  ∀(G: fsgraph). gen_bipartite G A B ⇔ gen_bipartite G B A
Proof
  ASM_SET_TAC [gen_bipartite_def]
QED

Theorem bipartite_gen_bipartite:
  ∀G. bipartite G ⇔ ∃A B. gen_bipartite G A B
Proof
  rw [gen_bipartite_def, bipartite_def]
QED

(* List lemmas *)


(* fsg lemma *)
Theorem alledges_valid_alt:
  ∀(G: fsgraph) n1 n2. {n1; n2} ∈ E ⇒ n1 ∈ V ∧ n2 ∈ V ∧ n1 ≠ n2
Proof
  NTAC 4 STRIP_TAC >> drule alledges_valid >> ASM_SET_TAC []
QED



(* Subgraph. should be in fsgraphtheory. *)

Overload V'[local] = “nodes (G' :fsgraph)”;
Overload E'[local] = “fsgedges (G' :fsgraph)”;
Overload V''[local] = “nodes (G'' :fsgraph)”;
Overload E''[local] = “fsgedges (G'' :fsgraph)”;

Definition subgraph_def:
  subgraph (G': fsgraph) (G: fsgraph) <=> V' SUBSET V /\ E' SUBSET E
End

Overload SUBSET = “subgraph”

Definition span_subgraph_def:
  span_subgraph (G': fsgraph) (G: fsgraph) ⇔ G' ⊆ G ∧ V' = V
End

Theorem subgraph_id:
  ∀(G: fsgraph). G ⊆ G
Proof
  simp [subgraph_def]
QED

Theorem subgraph_exists:
  ∀(G: fsgraph). ∃G'. G' ⊆ G
Proof
  rw [] >> qexists_tac ‘G’ >> rw [subgraph_id]
QED

(* Factors *)
Definition regular_def:
  regular k (G: fsgraph) ⇔ ∀v. v ∈ V ⇒ degree G v = k
End

Definition factor_def:
  factor k (G': fsgraph) (G: fsgraph) ⇔ span_subgraph G' G ∧ regular k G'
End

(* Definition prefs_def: *)
(*   prefs (G: fsgraph) = {f | } *)
(* End *)

(* Matching *)

Definition matching_def:
  matching (G: fsgraph) M <=> (M SUBSET E) /\ (!e1 e2. e1 IN M /\ e2 IN M /\ e1 <> e2 ==> DISJOINT e1 e2)
End

(* TODO: obsolete. *)
Theorem matching_def':
  matching (G: fsgraph) M <=> (M SUBSET E) /\ (!e1 e2. e1 IN M /\ e2 IN M ==> e1 <> e2 ==> DISJOINT e1 e2)
Proof
  METIS_TAC [matching_def]
QED

Theorem matching_as_subgraph:
  ∀G M. matching G M ⇒ ∃G'. G' ⊆ G ∧ V' = V ∧ E' = M
Proof
  rw [matching_def, subgraph_def]
  >> ‘∃G'. nodes G' = V ∧ fsgedges G' = M’ suffices_by ASM_SET_TAC []
  >> Q.EXISTS_TAC ‘fsgAddEdges M $ fsgAddNodes V emptyG’
  >> rw [fsgedges_fsgAddEdges]
  >> rw [EXTENSION] >> reverse iff_tac
  >- (rw []
      >> ‘x ∈ E’ by ASM_SET_TAC []
      >> drule alledges_valid >> rw []
      >> qexistsl_tac [‘a’, ‘b’] >> ASM_SET_TAC []
     )
  >> rw []
  >> ‘x = {m; n}’ by ASM_SET_TAC [] >> gvs []
QED

Definition matched:
  matched (G: fsgraph) M v ⇔ matching G M ⇒ v ∈ BIGUNION M
End

Theorem matched_def:
  ∀G M v. matched G M v <=> matching G M ==> (?e. e IN M /\ v IN e)
Proof
  rw [matched, BIGUNION] >> METIS_TAC []
QED

Definition unmatched:
  unmatched G M v ⇔ ~matched G M v
End

(* shit mountain *)
val matched_def_eq = unmatched;

Theorem unmatched_def:
  ∀G M v. unmatched G M v <=> matching G M /\ !e. e IN M ==> v NOTIN e
Proof
  rw [unmatched, matched_def] >> METIS_TAC []
QED


(* Theorem matched_def_eq: *)
(*   !G M v. unmatched G M v <=> ~matched G M v *)
(* Proof *)
(*   rw [matched_def, unmatched_def] >> METIS_TAC [] *)
(* QED *)


Definition matched_set_def:
  matched_set (G: fsgraph) M U <=> !v. v IN U ==> matched G M v
End

Theorem matched_set_subset:
  ∀G M U S. matched_set G M U ∧ S ⊆ U ⇒ matched_set G M S
Proof
  ASM_SET_TAC [matched_set_def]
QED

Theorem matched_set_f:
  ∀G M U. matching G M ∧ U ⊆ V ∧ matched_set G M U ⇒ (∃f. INJ f U V)
Proof
  rw [matched_set_def, matched] >> gvs []
  >> drule_then mp_tac matching_as_subgraph >> rpt STRIP_TAC (*  *)
  >> Q.ABBREV_TAC ‘f = \v. if ∃e. e ∈ M ∧ v ∈ e then @v'. {v; v'} ∈ M else v’
  >> qexists_tac ‘f’ >> rw [INJ_DEF]
  >- (rw [Abbr ‘f’]
      >- (rw [IN_APP]
          >> irule SELECT_ELIM_THM
          >> ‘∀x. E' x ⇔ x ∈ E'’ by rw [IN_APP] >> POP_ORW
          >> ‘∀x. V x ⇔ x ∈ V’ by rw [IN_APP] >> POP_ORW
          >> rw []
          >- (drule alledges_valid >> rw [] >> ASM_SET_TAC [])
          >> drule alledges_valid >> rw []
          >> Cases_on ‘x = a’
          >- (POP_ORW >> qexists_tac ‘b’ >> rw [])
          >> ‘x = b’ by ASM_SET_TAC []
          >> POP_ORW >> qexists_tac ‘a’
          >> ‘{b; a} = {a; b}’ by ASM_SET_TAC []
          >> POP_ORW >> rw []
         )
      >> gvs [GSYM IMP_DISJ_THM]
      >> first_x_assum drule >> rw []
      >> first_x_assum drule >> rw []
     )
  >> gvs [Abbr ‘f’, matching_def]
  >> qabbrev_tac ‘v = @v'. {x; v'} ∈ E'’
  >> sg ‘v ∈ V’
  >- (‘∃s. x ∈ s ∧ s ∈ E'’ by ASM_SET_TAC []
      >> sg ‘v ∈ s’
      >- (drule alledges_valid >> STRIP_TAC >> gvs []
          >- (DISJ2_TAC
              >> gvs [Abbr ‘v’]
              >> qabbrev_tac ‘P = λx. (x = b)’
              >> qabbrev_tac ‘Q = λy. {a; y} ∈ E'’
              >> rw []
              >> irule SELECT_ELIM_THM
              >> rw [Abbr ‘P’, Abbr ‘Q’]
              >- (‘{a; b} = {a; x}’ suffices_by SET_TAC []
                  >> CCONTR_TAC
                  >> qpat_x_assum ‘∀e1 e2. _’ drule_all
                  >> rw []
                 )
              >> qexists_tac ‘b’ >> rw []
             )
          >> DISJ1_TAC
          >> gvs [Abbr ‘v’]
          >> qabbrev_tac ‘P = λx. (x = a)’
          >> qabbrev_tac ‘Q = λy. {b; y} ∈ E'’
          >> rw []
          >> irule SELECT_ELIM_THM
          >> rw [Abbr ‘P’, Abbr ‘Q’]
          >- (‘{a; b} = {b; x}’ suffices_by SET_TAC []
              >> CCONTR_TAC
              >> qpat_x_assum ‘∀e1 e2. _’ drule_all
              >> rw []
             )
          >> qexists_tac ‘a’
          >> ‘{b; a} = {a; b}’ by SET_TAC []
          >> POP_ORW >> rw []
         )
      >> cheat
     )
  (* TODO: below *)
  (* >> ‘{x; v} = {y; v}’ suffices_by ASM_SET_TAC [] *)
  >> cheat
  (* >> Cases_on ‘∃e. e ∈ E' ∧ x ∈ e’ (* 2 *) *)
  (* >- (Cases_on ‘∃e. e ∈ E' ∧ y ∈ e’ (* 2 *) *)
  (*     >- (gs [] *)
  (*         >> sg ‘{y; v} = e'’ *)
  (*         >- (‘{y; v} ∈ E'’ by ASM_SET_TAC [] *)
  (*            ) *)
  (*        ) *)
  (*    ) *)
QED

Theorem gen_matching_exists:
  !(G: fsgraph). ?x. matching G x
Proof
  GEN_TAC >> Q.EXISTS_TAC ‘ {} ’ >> simp [matching_def]
QED

Theorem matching_exists:
  ?x. matching G x
Proof
  rw [gen_matching_exists]
QED


Theorem matching_not_empty:
  matching G <> {}
Proof
  ASSUME_TAC matching_exists >> ASM_SET_TAC [NOT_IN_EMPTY]
QED


Theorem finite_matching:
  !G M. matching G M ==> FINITE M
Proof
  rw[matching_def] >> irule SUBSET_FINITE_I >> Q.EXISTS_TAC ‘fsgedges G’ >> rw[]
QED


Theorem finite_num_matching:
  !(G: fsgraph). FINITE {M | matching G M}
Proof
  (* M SUBSET E ==> M IN P(E); [IN_POW (<--)]
     !M. (matching G M ==> M SUBSET E) ==> {M | matching G M} SUBSET P(E) [new lemma?]
     E is finite ==> P(E) is finite [FINITE_POW (<--)]
     P(E) is finite /\ {M | matching G M} SUBSET P(E) ==> {M | matching G M} is finite [SUBSET_FINITE_I]
   *)
  (* pred_setTheory *)
  rw []
  >> irule SUBSET_FINITE_I
  >> Q.EXISTS_TAC ‘POW (fsgedges G)’
  >> rw [SUBSET_DEF, IN_POW]
  >> gvs [matching_def, SUBSET_DEF]
QED


Theorem finite_num_matching':
  !(G: fsgraph). FINITE (matching G)
Proof
  GEN_TAC \\
  ‘matching G = {M | matching G M}’ by rw[EXTENSION, IN_APP]
  >> pop_assum (fn t => rw [Once t])
  >> rw [finite_num_matching]
QED


Theorem matching_2times_vertex:
  ∀(G: fsgraph) M. matching G M ⇒ CARD $ BIGUNION M = CARD M * 2
Proof
  rpt STRIP_TAC
  >> irule CARD_BIGUNION_SAME_SIZED_SETS
  >> rw [finite_matching, matching_def]
  >- gvs [matching_def]
  >- (gvs [matching_def, SUBSET_DEF]
      >> LAST_ASSUM drule >> disch_tac
      >> drule alledges_valid >> disch_tac >> gs []
     )
  >- (gvs [matching_def, SUBSET_DEF]
      >> LAST_ASSUM drule >> disch_tac
      >> drule alledges_valid >> disch_tac >> gs []
     )
  >> drule finite_matching >> rw []
QED


(* Neighbour *)

Definition neighbour_def:
  neighbour (G: fsgraph) v = {v' | v' IN V /\ v' <> v /\ ?e. e IN E /\ v IN e /\ v' IN e}
End

Theorem neighbour_def_adj:
  ∀G v. neighbour G v = {v' | v' ∈ V ∧ adjacent (G: fsgraph) v v'}
Proof
  rw [neighbour_def, adjacent_fsg, EXTENSION] >> cheat
QED

Theorem neighbour_degree_eq:
  ∀G v. CARD (neighbour G v) = degree G v
Proof
  cheat                         (* TODO *)
QED
Theorem neighbour_bipartite:
  ∀G A B v. gen_bipartite G A B ∧ v ∈ V ∧ v ∈ A ⇒ neighbour G v ⊆ B
Proof
  rw [gen_bipartite_def, neighbour_def_adj, SUBSET_DEF] >> rpt STRIP_TAC >> gs [adjacent_fsg]
  >> first_x_assum drule >> ASM_SET_TAC []
QED

Theorem neighbour_FINITE:
  ∀(G: fsgraph) v. v ∈ V ⇒ FINITE $ neighbour G v
Proof
  rw []
  >> ‘neighbour G v ⊆ V’ by rw [neighbour_def, GSPEC_AND]
  >> ‘FINITE V’ by ASM_SET_TAC [GEN_ALL FINITE_nodes]
  >> irule SUBSET_FINITE_I >> qexists_tac ‘V’ >> rw []
QED

Theorem neighbour_subgraph_SUBSET:
  ∀G G'. subgraph G' G ==> !v. v IN V' ==> (neighbour G' v) ⊆ (neighbour G v)
Proof
  rw [subgraph_def]
  >> ASM_SET_TAC [neighbour_def]
QED

Theorem neighbour_subgraph_CARD:
  ∀G G'. subgraph G' G ==> !v. v IN V' ==> CARD (neighbour G' v) <= CARD (neighbour G v)
Proof
  rw [] >> drule_all neighbour_subgraph_SUBSET >> rw []
  >> irule CARD_SUBSET >> rw []
  >> irule neighbour_FINITE >> ASM_SET_TAC [subgraph_def]
QED

Definition neighbour_set:
  neighbour_set G U = BIGUNION $ IMAGE (neighbour G) U
End

Overload N = “neighbour_set G”;
Overload N' = “neighbour_set G'”

Theorem neighbour_set_def:
  ∀G U. U SUBSET V ==> N U = {v' | v' IN V /\ ?v. v IN U /\ v' <> v /\ ?e. e IN E /\ v IN e /\ v' IN e}
Proof
  rw [neighbour_set, BIGUNION, IMAGE_DEF, neighbour_def, EXTENSION]
  >> EQ_TAC
  >- (rw []
      >- gvs []
      >> Q.PAT_X_ASSUM ‘!x. _’ (fn t => gvs [t])
      >> Q.EXISTS_TAC ‘x'’ >> rw []
      >> Q.EXISTS_TAC ‘e’ >> rw []
     )
  >> rw []
  >> Q.EXISTS_TAC ‘neighbour G v’ >> reverse $ rw [neighbour_def]
  >- (Q.EXISTS_TAC ‘e’ >> rw [])
  >> Q.EXISTS_TAC ‘v’ >> rw []
QED

Theorem neighbour_set_alt:
  ∀G U. U SUBSET V ==> N U = {v' | v' IN V /\ ?e v. v IN U /\ v' <> v /\ e IN E /\ v IN e /\ v' IN e}
Proof
  rw [neighbour_set_def, EXTENSION] >> EQ_TAC
  >- METIS_TAC []
  >> METIS_TAC []
QED

Theorem neighbour_set_def_adj:
  ∀G U. U ⊆ V ⇒ N U = {v' | v' ∈ V ∧ ∃v. v ∈ U ∧ adjacent (G: fsgraph) v v'}
Proof
  rw [adjacent_fsg, neighbour_set_def, EXTENSION] >> EQ_TAC
  >- (rw []
      >> drule alledges_valid >> rw []
      >> qexists_tac ‘v’ >> rw []
      >> ‘v = a ∨ v = b’ by ASM_SET_TAC []
      >- ASM_SET_TAC []
      >> ‘{x; v} ∈ E’ by ASM_SET_TAC []
      >> ‘{v; x} = {x; v}’ suffices_by (rw [] >> POP_ORW >> rw [])
      >> rw [EXTENSION] >> TAUT_TAC
     )
  >> rw [] >> qexists_tac ‘v’ >> rw []
  >- (drule alledges_valid >> disch_tac >> gvs [INSERT2_lemma]
     )
  >> qexists_tac ‘{v; x}’ >> rw []
QED

Theorem neighbour_set_FINITE:
  ∀(G: fsgraph) U. U ⊆ V ⇒ FINITE (N U)
Proof
  reverse $ rw [neighbour_set]
  >- (irule neighbour_FINITE >> ASM_SET_TAC [])
  >> irule IMAGE_FINITE
  >> irule SUBSET_FINITE_I
  >> qexists_tac ‘V’ >> simp []
QED

Theorem neighbour_set_subgraph_CARD:
  ∀(G: fsgraph) (G': fsgraph). subgraph G' G ==> ∀vs. vs ⊆ V' ⇒ CARD (N' vs) <= CARD (N vs)
Proof
  rw [] >> drule neighbour_subgraph_CARD >> rw []
  >> Cases_on ‘V' = EMPTY’
  >- (rw [neighbour_set] >> gvs [neighbour_def])
  >> Cases_on ‘vs = EMPTY’
  >- (rw [neighbour_set] >> gvs [neighbour_def])
  >> ‘∃v. v ∈ vs’ by ASM_SET_TAC []
  >> ‘v ∈ V'’ by ASM_SET_TAC []
  >> first_assum drule >> disch_tac
  >> rw [neighbour_set]
  >> irule CARD_SUBSET >> rpt STRIP_TAC
  >- (reverse $ rw [FINITE_BIGUNION_EQ]
      >- (irule neighbour_FINITE >> gvs [subgraph_def] >> ASM_SET_TAC [])
      >- (irule IMAGE_FINITE >> ‘FINITE V'’ by gvs [GEN_ALL FINITE_nodes]
          >> irule SUBSET_FINITE_I >> qexists_tac ‘V'’ >> rw []
         )
     )
  >> rw [BIGUNION_SUBSET] >> irule $ GEN_ALL SUBSET_BIGUNION_SUBSET_I
  >> qexists_tac ‘neighbour G x’ >> rw []
  >> irule neighbour_subgraph_SUBSET >> ASM_SET_TAC []
QED

(* Theorem neighbour_set_matched_set_card: *)
(*   ∀G M U. bipartite G ∧ U ⊆ V ∧ matching G M ∧ matched_set G M U ⇒ CARD U ≤ CARD (N U) *)
(* Proof *)
(*   rw [matched_set_def, bipartite_alt] *)
(*   >> Cases_on ‘U = ∅’ *)
(*   >- simp [] *)
(*   >> ‘∃v. v ∈ U’ by ASM_SET_TAC [] *)
(*   >> LAST_ASSUM drule >> disch_tac *)
(*   >> drule matching_as_subgraph >> rpt strip_tac *)
(*   >> qsuff_tac ‘CARD U ≤ CARD (N' U)’ *)
(*   >- (‘CARD (N' U) ≤ CARD (N U)’ suffices_by simp [] *)
(*       >> irule neighbour_set_subgraph_CARD >> gvs [] *)
(*      ) *)
(*   >> irule INJ_CARD >> rw [neighbour_set_FINITE] *)
(*   >> Q.ABBREV_TAC ‘n = λv. CHOICE $ neighbour G' v’ *)
(*   >> qexists_tac ‘n’ *)
(*   >> rw [INJ_DEF, neighbour_set_def, Abbr ‘n’] *)
(*   >- (rw [CHOICE_DEF] *)
(*      ) *)
(* QED *)


(* Vertex cover *)

Definition gen_vertex_cover_def:
  gen_vertex_cover ns es U <=> U SUBSET ns /\ !e. e IN es ==> ?v. v IN U /\ v IN e
End

(* Overload vertex_cover = “\(G: fsgraph) U. gen_vertex_cover V E U” *)
Overload vertex_cover = “\(G: fsgraph). gen_vertex_cover V E”


Theorem gen_vertex_cover_subset:
  !ns es1 es2 U. gen_vertex_cover ns es1 U /\ es2 SUBSET es1 ==> gen_vertex_cover ns es2 U
Proof
  METIS_TAC [gen_vertex_cover_def, SUBSET_DEF]
QED


Theorem vertex_cover_exists:
  ?U. vertex_cover (G: fsgraph) U
Proof
  Q.EXISTS_TAC ‘V’ >> rw [gen_vertex_cover_def] \\
  Q.SPEC_THEN ‘G’ MP_TAC (alledges_valid) >> rw [] \\
  Q.EXISTS_TAC ‘a’ >> rw [COMPONENT]
QED


Theorem finite_num_vertex_cover:
  !(G: fsgraph). FINITE {U | vertex_cover G U}
Proof
  rw []
  >> irule SUBSET_FINITE_I
  >> Q.EXISTS_TAC ‘POW V’
  >> rw [SUBSET_DEF, IN_POW]
  >> gvs [gen_vertex_cover_def, SUBSET_DEF]
QED

Theorem finite_num_vertex_cover':
  !(G: fsgraph). FINITE (vertex_cover G)
Proof
  ‘!(G: fsgraph). vertex_cover G = {U | vertex_cover G U}’ by rw [EXTENSION, IN_APP]
  >> POP_ORW >> rw [finite_num_vertex_cover]
QED


(* Alternating & Augmenting Path *)
Definition alternating_path_def:
  alternating_path G M P <=> matching G M /\ path G P /\
                           unmatched G M (HD P) /\
                           !(n: num). SUC n < LENGTH P ==> (ODD n <=> {EL n P; EL (SUC n) P} IN M)
End


Definition augmenting_path_def:
  augmenting_path G M P <=> alternating_path G M P /\ unmatched G M (LAST P)
End


Theorem adjacent_reversible[simp]: (* TODO: chuck this elsewhere *)
  !l a b. adjacent (REVERSE l) a b <=> adjacent l b a
Proof
  ‘!l a b. adjacent l b a ==> adjacent (REVERSE l) a b’ suffices_by METIS_TAC [REVERSE_REVERSE]
  >> Induct_on ‘list$adjacent’ >> ONCE_REWRITE_TAC [CONS_APPEND]
  >> rw [adjacent_append2]
QED

Theorem adjacent_fsg_reversible[simp]:
  !(G: fsgraph) a b. adjacent G a b <=> adjacent G b a
Proof
  rw [adjacent_fsg]
  >> ‘{a; b} = {b; a}’ by rw [INSERT2_lemma]
  >> pop_assum (fn t => rw [Once t])
QED

(* tautLib *)
Definition XOR:                 (* boolTheory may need this, could not find *)
  $XOR = (\t1 t2. (t1 ∧ ~t2) ∨ (~t1 ∧ t2))
End

(* Definition path_xor: *)
(*   path_xor (G: fsgraph) es p = {e | XOR (e IN es) (?v1 v2. adjacent p v1 v2 /\ v1 IN e /\ v2 IN e)} *)
(* End *)

Theorem walk_reversible[simp]:
  !(G: fsgraph) P. walk G (REVERSE P) <=> walk G P
Proof
  rw [walk_def] >> METIS_TAC [adjacent_SYM]
QED

Theorem path_reversible[simp]:
  !(G: fsgraph) P. path G (REVERSE P) <=> path G P
Proof
  rw [path_def, walk_reversible]
QED

Theorem path_subset_nodes:
  !(G: fsgraph) p. path G p ==> (set p) SUBSET V
Proof
  rw [path_def, walk_def] >> rw [SUBSET_DEF]
QED

Theorem alternating_path_prefix:
  !(G: fsgraph) M P Q. alternating_path G M P /\ Q <<= P /\ Q <> [] ==> alternating_path G M Q
Proof
  rw [] >> REWRITE_TAC [alternating_path_def]
  >> ‘LENGTH Q <= LENGTH P’ by rw [IS_PREFIX_LENGTH]
  >> drule is_prefix_el >> disch_tac
  >> gvs [alternating_path_def] >> CONJ_TAC (* 2 *)
  >- (gvs [path_def, walk_def, GSYM CONJ_ASSOC]
      >> CONJ_TAC (* 2 *)
      >- (rw [MEM_EL]
          >> FIRST_X_ASSUM MATCH_MP_TAC
          >> ‘EL n Q = EL n P’ by rw [is_prefix_el]
          >> rw [EL_MEM]
         )
      >> reverse CONJ_TAC
      >- (gvs [IS_PREFIX_EQ_TAKE] >> rw [ALL_DISTINCT_TAKE])
      >> rpt STRIP_TAC
      >> FIRST_X_ASSUM MATCH_MP_TAC
      >> gvs [IS_PREFIX_APPEND]
      >> rw [adjacent_append1]
     )
  >- (qsuff_tac ‘HD P = HD Q’
      >- (gvs [alternating_path_def] >> rw [] >> gvs [])
      >> gvs [IS_PREFIX_EQ_TAKE] >> rw [HD_TAKE]
     )
QED

(* All alt. paths in bipartite graph starting in A zigzags between A and B, decided by parity *)
Theorem alternating_path_zigzag_parity:
  !(G: fsgraph) A B M P n. gen_bipartite G A B /\
                           matching G M /\
                           alternating_path G M P /\
                           HD P IN A /\
                           SUC n ≤ LENGTH P
                           ==> (ODD n <=> EL n P IN B)
Proof
  rw [gen_bipartite_def, matching_def, unmatched_def, alternating_path_def]
  >> Induct_on ‘n’
  >- (rw [] >> ASM_SET_TAC [])
  >> rw []
  >> Cases_on ‘ODD n’
  >- (rw []
      >> ‘SUC n < LENGTH P’ by simp []
      >> ‘~(ODD $ SUC n)’ by simp [ODD] >> gvs []
      >> ASM_SET_TAC []
     )
  >> ‘ODD $ SUC n’ by simp [ODD]
  >> gvs []
  >> sg ‘adjacent G (EL n P) (EL (SUC n) P)’
  >- (gvs [path_def, walk_def]
      >> FIRST_X_ASSUM irule
      >> rw [adjacent_EL]
      >> qexists_tac ‘n’ >> rw [ADD1]
     )
  >> ‘{EL n P; EL (SUC n) P} IN E’ by gvs [adjacent_fsg, COMPONENT]
  >> ‘EL n P IN V’ by gvs [path_def, walk_def, EL_MEM]
  >> ‘EL n P IN A’ by ASM_SET_TAC []
  >> METIS_TAC []
QED

(* equivalent theorem without relying on parity and head*)
Theorem alternating_path_zigzag:
  !(G: fsgraph) A B M P n. gen_bipartite G A B /\
                           matching G M /\
                           alternating_path G M P /\
                           SUC n < LENGTH P
                           ==> (EL n P IN A <=> EL (SUC n) P IN B)
Proof
  rw [gen_bipartite_def, alternating_path_def]
  >> sg ‘adjacent G (EL n P) (EL (SUC n) P)’
  >- (gvs [path_def, walk_def]
      >> FIRST_X_ASSUM irule
      >> rw [adjacent_EL]
      >> qexists_tac ‘n’ >> rw [ADD1]
     )
  >> ‘{EL n P; EL (SUC n) P} IN E’ by gvs [adjacent_fsg, COMPONENT]
  >> ASM_SET_TAC []
QED

(* Specifies the vertex order of matched edge traversed by an alt. path *)
Theorem alternating_path_matched_edge_traverse:
  !(G: fsgraph) A B M P v1 v2. gen_bipartite G A B /\
                               matching G M /\
                               alternating_path G M P /\
                               HD P IN A /\
                               {v1; v2} IN M /\
                               adjacent P v1 v2
                                    ==> v1 IN B /\ v2 IN A
Proof
  rpt GEN_TAC >> STRIP_TAC
  >> gs [adjacent_EL, GSYM ADD1]
  >> ‘SUC i < LENGTH P’ by rw []
  >> drule_all alternating_path_zigzag
  >> DISCH_TAC
  >> gs [gen_bipartite_def]
  >> ‘EL i P ∈ B’ suffices_by ASM_SET_TAC [matching_def, alternating_path_def, path_def, walk_def]
  >> gvs [alternating_path_def]
  >> ‘ODD i’ by gs []
  >> irule $ iffLR alternating_path_zigzag_parity >> rw []
  >> qexistsl_tac [‘A’, ‘G’, ‘M’]
  >> rw [gen_bipartite_def, alternating_path_def]
QED


Theorem alternating_path_matched_edge_iff:
  !(G: fsgraph) A B M P v1 v2. gen_bipartite G A B /\
                               matching G M /\
                               alternating_path G M P /\
                               HD P IN A /\
                               {v1; v2} IN M
                                    ==> (adjacent P v1 v2 ⇔ v2 IN A ∧ MEM v2 P)
Proof
  rw [] >> EQ_TAC
  >- (rpt DISCH_TAC
      >> drule adjacent_MEM >> rw []
      >> drule_all alternating_path_matched_edge_traverse >> rw []
     )
  >> gs [MEM_EL] >> rw [adjacent_EL, GSYM ADD1]
  >> Q.ABBREV_TAC ‘m = PRE n’
  >> sg ‘n = SUC m’
  >- (rw [Abbr ‘m’, GSYM SUC_PRE]
       >> CCONTR_TAC
       >> gs [alternating_path_def,unmatched_def]
       >> FIRST_X_ASSUM drule
       >> rw []
     )
  >> qexists_tac ‘m’ >> simp []
  >> gs [alternating_path_def]
  >> Q.ABBREV_TAC ‘v1' = EL m P’
  >> Q.ABBREV_TAC ‘v2 = EL (SUC m) P’
  >> Q.ABBREV_TAC ‘e = {v1; v2}’
  >> Q.ABBREV_TAC ‘e' = {v1'; v2}’
  >> qsuff_tac ‘ODD m’
  >- (disch_tac
      >> gvs [] >> ASM_SET_TAC [matching_def]
     )
  >> sg ‘v1 ∈ B’
  >- (gs [gen_bipartite_def, matching_def]
      >> gvs [Abbr ‘v1'’, Abbr ‘e’, Abbr ‘e'’]
      >> ASM_SET_TAC []
     )
  >> irule $ iffRL alternating_path_zigzag_parity
  >> qexistsl_tac [‘A’, ‘B’, ‘G’, ‘M’, ‘P’]
  >> rw [gen_bipartite_def, alternating_path_def]
  >> qsuff_tac ‘e' ∈ E’
  >- (gs [gen_bipartite_def, Abbr ‘e'’]
      >> ASM_SET_TAC []
     )
  >> sg ‘adjacent P v1' v2’
  >- (gvs [Abbr ‘v1'’, Abbr ‘v2’]
      >> rw [adjacent_EL]
      >> qexists_tac ‘m’ >> rw [GSYM ADD1]
     )
  >> gvs [path_def, walk_def]
  >> LAST_X_ASSUM drule >> rw [adjacent_fsg]
QED

p
(* Theorem augmenting_path_reversible: *)
(*   !G M P. matching G M ==> augmenting_path G M P ==> augmenting_path G M (REVERSE P) *)
(* Proof *)
(*   cheat *)
(* QED *)

Definition edges_in_path_def:
  edges_in_path (G: fsgraph) p = {{v1; v2} |
                                    path G p ∧ list$adjacent p v1 v2 ∧
                                    adjacent G v1 v2}
End

Theorem edges_in_path_alt:
  ∀G p. edges_in_path (G: fsgraph) p = {e | path G p ∧ e ∈ E ∧ ∃v1 v2. list$adjacent p v1 v2
                                              ∧ v1 ∈ e ∧ v2 ∈ e}
Proof
  rw [edges_in_path_def, EXTENSION] >> iff_tac >> disch_tac
  >- (gvs [] >> reverse CONJ_TAC
      >- (qexistsl_tac [‘v1’, ‘v2’] >> rw [])
      >> gvs [adjacent_fsg]
      >> ‘x = {v1; v2}’ by ASM_SET_TAC []
      >> gvs []
     )
  >> gvs [] >> qexistsl_tac [‘v1’, ‘v2’] >> rw []
  >- (‘∃a b. x = {a; b}’ by METIS_TAC [alledges_valid]
      >> ‘v1 ≠ v2’ suffices_by ASM_SET_TAC []
      >> ‘ALL_DISTINCT p’ by fs [path_def]
      >> drule ALL_DISTINCT_EL_IMP >> rw []
      >> gs [adjacent_EL] >> gvs []
     )
  >> gvs [path_def, walk_def]
QED

(* Overload E[local] = “path_edges G” *)


Definition path_xor_def:
  path_xor (G: fsgraph) es p = {e | XOR (e ∈ es) (e ∈ edges_in_path G p)}
End


Theorem augmenting_path_augments_matching:
  ∀(G: fsgraph) M P. bipartite G ∧ augmenting_path G M P ⇒ ∃M'. matching G M' ∧ CARD M < CARD M'
Proof
  cheat
QED
  (* rpt STRIP_TAC >> gvs [augmenting_path_def, alternating_path_def, bipartite_alt] *)
  (* >> gvs [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] *)
  (* >> rename [‘_ = {Aend _; Bend _}’] *)
  (* >> qabbrev_tac ‘M' = path_xor G M P’ *)
  (* >> gs [path_xor_def, XOR] *)
  (* >> qexists_tac ‘M'’ >> rw [Abbr ‘M'’] *)
  (* >- (gs [matching_def] >> rw [] (* 5 *) *)
  (*     >- (rw [GSPEC_OR, GSPEC_AND] *)
  (*         >- ASM_SET_TAC [matching_def] *)
  (*         >> ‘edges_in_path G P ⊆ E’ suffices_by ASM_SET_TAC [] *)
  (*         >> rw [edges_in_path_alt, adjacent_fsg, GSPEC_AND] *)
  (*        ) *)
  (*     >- (gvs [matching_def]) *)
  (*     >- (gvs [edges_in_path_alt] *)
  (*         >- (CCONTR_TAC >> ASM_SET_TAC []) *)
  (*         >> ‘ALL_DISTINCT P’ by METIS_TAC [path_def] *)
  (*         >> ‘v1 ≠ v2’ by ( *)
  (*           drule $ iffLR adjacent_EL *)
  (*           >> drule $ ALL_DISTINCT_EL_IMP *)
  (*           >> rw [] >> simp [] *)
  (*           ) *)
  (*         >> LAST_ASSUM drule >> rpt STRIP_TAC *)
  (*         >> ‘e1 ∈ E’ by ASM_SET_TAC [] *)
  (*         >> LAST_ASSUM drule >> rpt STRIP_TAC *)
  (*         >> ‘v1 ∉ e1 ∧ v2 ∉ e1’ suffices_by ( *)
  (*           rpt STRIP_TAC *)
  (*           >> ASM_SET_TAC [] *)
  (*           ) *)
  (*         >>  *)
  (*        ) *)

  (*    ) *)
  (* QED *)

(* Theorem alternating_path_el_matched: *)
(*   ∀G M p. bipartite G ∧ alternating_path G M p ⇒ ∀v. MEM v p ∧ v ≠ HD p ∧ v ≠ LAST p ⇒ matched G M v *)
(* Proof *)
(*   rw [alternating_path_def] *)
(*   >> ‘p ≠ []’ by gvs [path_def, walk_def] *)
(*   >> sg ‘∀n. 0 < n ∧ SUC n < LENGTH p ⇒ matched G M $ EL n p’ *)
(*   >- (Induct_on ‘n’ *)
(*       >- simp [] *)
(*       >> rw [] *)
(*       >> Cases_on ‘ODD $ SUC n’ *)
(*       >- (FIRST_X_ASSUM drule *)
(*           >> rw [matched_def] *)
(*           >> qexists_tac ‘{EL (SUC n) p; EL (SUC (SUC n)) p}’ >> rw [IN_APP] *)
(*          ) *)
(*       >> ‘ODD n’ by METIS_TAC [ODD] *)
(*       >> ‘SUC n < LENGTH p’ by simp [] *)
(*       >> FIRST_X_ASSUM drule >> rw [matched_def] *)
(*       >> qexists_tac ‘{EL n p; EL (SUC n) p}’ >> rw [IN_APP] *)
(*      ) *)
(*   >> gs [MEM_EL] >> FIRST_X_ASSUM irule >> rw [] *)
(*   >- (‘EL n p ≠ EL 0 p’ by simp [EL] *)
(*       >> ‘ALL_DISTINCT p’ by gvs [alternating_path_def, path_def] *)
(*       >> drule $ ALL_DISTINCT_EL_IMP >> rw [] *)
(*       >> gvs [] *)
(*      ) *)
(*   >> gvs [path_def] *)
(*   >> drule_all LAST_EL *)
(*   >> qabbrev_tac ‘m = PRE $ LENGTH p’ *)
(*   >> ‘m < LENGTH p’ by gvs [Abbr ‘m’] *)
(*   >> rw [] *)
(*   >> cheat *)
(* QED *)

Theorem alternating_path_append: (* TODO *)
  ∀G M A B p q. gen_bipartite G A B ∧ alternating_path G M p ∧
                HD p ∈ A ∧
                ~MEM q p ∧
                adjacent G (LAST p) q ∧
                (LAST p ∈ B ⇒ {q; LAST p} ∈ M)
                ⇒ alternating_path G M (p ++ [q])
Proof
  rw [] >> Cases_on ‘LAST p ∈ B’
  >- (gvs [gen_bipartite_def] >> rw [alternating_path_def]
      >- gvs [alternating_path_def]
      >- (rw [path_def, walk_def] (* 4 *)
          >- gvs [alternating_path_def, path_def, walk_def]
          >- (gvs [alternating_path_def, matching_def]
              >> ASM_SET_TAC [alledges_valid_alt])
          >- (Cases_on ‘v2 = q’
              >- (‘v1 = LAST p’ suffices_by rw []
                  >> ‘p = FRONT p ++ [LAST p]’ by
                    gvs [APPEND_FRONT_LAST, alternating_path_def, path_def, walk_def]
                  >> qabbrev_tac ‘p0 = FRONT p’
                  >> ‘p ++ [q] = p0 ++ [LAST p; q]’ by simp []
                  >> pop_assum (fn t => gs [t])
                               (* TODO *)
                     )
                 )
           )
         )
     )
QED

(* Definition max_matching_def: *)
(*   max_matching (G: fsgraph) M <=> matching G M /\ !N. matching G N ==> CARD N <= CARD M *)
(* End *)

(* Theorem max_matching_def_image_card: *)
(*   max_matching G M <=> matching G M /\ CARD M = MAX_SET (IMAGE CARD (matching G)) *)
(* Proof *)
(*   qsuff_tac ‘CARD M = MAX_SET (IMAGE CARD (matching G)) <=> !N. matching G N ==> CARD N <= CARD M’ *)
(*   >- rw [max_matching_def] *)
(*   >> Q.SPECL_THEN [‘N’, ‘matching G’] (fn t => rw [t]) (GSYM IN_APP) *)
(*   >> Q.SPECL_THEN [‘IMAGE CARD (matching G)’] MP_TAC MAX_SET_TEST_IFF *)
(*   >>   *)
(* QED *)

(* Q.SPECL [‘matching G’, ‘CARD’] *)



Definition max_matching_def:
  max_matching G M <=> matching G M /\ CARD M = MAX_SET (IMAGE CARD (matching G))
End

Theorem max_matching_alt:
  ∀G M. max_matching G M <=> (matching G M /\ !N. matching G N ==> CARD N <= CARD M)
Proof
  rw [max_matching_def]
  (* >> rw [] >> MATCH_MP_TAC MAX_SET_TEST_IFF *)

  >> ‘matching G M ==> (CARD M = MAX_SET (IMAGE CARD (matching G))
      <=> !N. matching G N ==> CARD N <= CARD M)’ suffices_by ASM_SET_TAC []
  >> rw []
  >> ‘FINITE M’ by METIS_TAC [finite_matching]
  >> ‘FINITE $ matching G’ by rw [finite_num_matching']
  >> ‘matching G <> {} ’ by rw [matching_not_empty]
  >> Q.SPEC_THEN ‘IMAGE CARD $ matching G’ ASSUME_TAC $ MAX_SET_TEST_IFF
  >> gvs []
  >> Q.ABBREV_TAC ‘x = CARD M’
  >> Q.PAT_X_ASSUM ‘!x. _’ $ Q.SPEC_THEN ‘x’ ASSUME_TAC
  >> pop_assum MP_TAC
  >> impl_tac
  >- (qexists_tac ‘M’ >> ASM_SET_TAC [])
  >> rw []
  >> iff_tac
  >- (rw []
      >> FIRST_X_ASSUM MATCH_MP_TAC
      >> qexists_tac ‘N''’ >> ASM_SET_TAC []
     )
  >> rw []
  >> FIRST_X_ASSUM MATCH_MP_TAC >> ASM_SET_TAC []
QED

Theorem max_matching_exists:
  !(G: fsgraph). ?M. max_matching G M
Proof
  rw [max_matching_def]
  >> Q.SPEC_THEN ‘IMAGE CARD (matching G)’ MP_TAC MAX_SET_IN_SET
  >> simp[is_measure_maximal_def, finite_num_matching']
  >> rw [matching_not_empty]
  >> qexists_tac ‘x’ >> ASM_SET_TAC []
QED

(* for compatibility *)
Theorem maximal_matching_exists:
  !(G: fsgraph). ?M. matching G M /\ !N. matching G N ==> CARD N <= CARD M
Proof
  simp [max_matching_exists, GSYM max_matching_alt]
QED

Theorem max_matching_no_aug_path:
  !(G: fsgraph) M. bipartite G ⇒ (max_matching G M <=> !p. alternating_path G M p ⇒ ~augmenting_path G M p)
Proof
  cheat
QED


(* Lemma: if U covers a matching M, then |M| <= |U|. *)
Theorem vertex_cover_matching_card:
  gen_vertex_cover V M U /\ matching G M ==> CARD M <= CARD U
Proof
  STRIP_TAC >> irule INJ_CARD >> CONJ_TAC
  >- (irule SUBSET_FINITE >> Q.EXISTS_TAC ‘V’
      >> gvs [gen_vertex_cover_def]
     )
  >> Q.EXISTS_TAC ‘\e. @x. x IN e /\ x IN U’
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
      >- (‘x IN e INTER e'’ by rw [INTER_DEF]
          >> Cases_on ‘DISJOINT e e'’
          >- METIS_TAC [NOT_IN_EMPTY, DISJOINT_DEF]
          >- (gvs [DISJOINT_DEF, matching_def'] >> METIS_TAC [matching_def'])
       )
      )
QED


Theorem matching_insert:
  matching G (e INSERT M) <=> matching G M /\ (DISJOINT e (BIGUNION M) \/ e IN M) /\ e IN E
Proof
  Cases_on ‘e IN M’
  >- (simp [ABSORPTION_RWT]
      >> simp [matching_def]
      >> ASM_SET_TAC []
     )
  >> rw [EQ_IMP_THM]  (* 4 *)
  >- gvs [matching_def]
  >- (gvs [matching_def]
      >> Q.PAT_X_ASSUM ‘!e1 e2. _’ (fn t => Q.SPECL_THEN [‘e’, ‘s'’] MP_TAC t)
      >> rw [] >> pop_assum irule
      >> ASM_SET_TAC []
     )
  >- gvs [matching_def]
  >> gvs [matching_def]
  >> rpt GEN_TAC
  >> Cases_on ‘e1 = e2’         (* 2 *)
  >- rw []
  >> Cases_on ‘e1 IN M /\ e2 IN M’ (* 2 *)
  >- rw []
  >> gvs []                     (* 2 *)
  >- (rw [] >> simp [])
  >> rw [Once DISJOINT_SYM]
  >> Q.PAT_X_ASSUM ‘!s. s IN M ==> _’ (fn t => Q.SPEC_THEN ‘e1’ irule t)
  >> rw []
QED

Theorem REVERSE_LAST_CONS_TL_lemma:
  !ls. ls <> [] ==> REVERSE ls = (LAST ls)::(TL $ REVERSE ls)
Proof
  rw []
  >> Q.ABBREV_TAC ‘sl = REVERSE ls’
  >> ‘LAST ls = HD sl’ by METIS_TAC [REVERSE_HD]
  >> pop_assum (fn t => rw [Once t])
  >> simp [Abbr ‘sl’]
QED

Theorem DISJOINT_elem_lemma:
  DISJOINT A B <=> !x y. (x IN A /\ y IN B) ==> x <> y
Proof
  ASM_SET_TAC []
QED

Theorem DISJOINT_pair_elem_lemma2:
  DISJOINT {a; b} {c; d} <=> a <> c /\ a <> d /\ b <> c /\ b <> d
Proof
  ASM_SET_TAC []
QED

Theorem LAST_EL_LENGTH_lemma:
  !n ls. LENGTH ls = SUC n ==> LAST ls = EL n ls
Proof
  rw [] >> sg ‘ls <> []’
  >- METIS_TAC [SUC_NOT_ZERO, LENGTH_NIL]
  >> Q.ABBREV_TAC ‘sl = REVERSE ls’
  >> sg ‘sl <> []’
  >- (‘?x xs. ls = x::xs’ by METIS_TAC [LIST_NOT_NIL] >> rw [Abbr ‘sl’, REVERSE_DEF]
     )
  >> ‘?y ys. sl = y::ys’ by METIS_TAC [LIST_NOT_NIL]
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

Theorem MEM_PREFIX_lemma:
  ∀x ls. MEM x ls ⇒ ∃ls'. ls' <<= ls ∧ ls' ≠ [] ∧ LAST ls' = x
Proof
  rw [MEM_EL] >> qexists_tac ‘TAKE (n + 1) ls’ >> rw [IS_PREFIX_EQ_TAKE]
  >- (qexists_tac ‘n + 1’ >> rw [])
  >- (CCONTR_TAC >> gvs [])
  >> ‘LENGTH $ TAKE (n + 1) ls = SUC n’ by simp []
  >> drule LAST_EL_LENGTH_lemma >> rw []
  >> irule EL_TAKE >> simp []
QED

Theorem ALL_DISTINCT_LAST_NOT_ADJ_lemma:
  ∀ls x. ALL_DISTINCT ls ∧ ls ≠ [] ⇒ ~adjacent ls (LAST ls) x
Proof
  rw [adjacent_EL] >> CCONTR_TAC >> gvs []
  >> ‘i < LENGTH ls’ by simp []
  >> drule_all ALL_DISTINCT_LAST_EL_IFF >> rw []
QED

(* flips an implication into contrapositive form *)
val contrapos_tac_rw = rw [Once MONO_NOT_EQ];

val CONTRAPOS_TAC = ONCE_REWRITE_TAC [MONO_NOT_EQ];

val contrapos_tac = CONTRAPOS_TAC;

fun my_tac term =
  ‘x IN fsgedges G /\ y IN fsgedges G’ by METIS_TAC [matching_def, SUBSET_DEF]
  >> ‘DISJOINT x y’ by METIS_TAC [matching_def] >> pop_assum MP_TAC
  >> rw [DISJOINT_DEF, INTER_DEF, GSYM MEMBER_NOT_EMPTY]
  >> Q.EXISTS_TAC term
  >> METIS_TAC [COMPONENT, genericGraphTheory.INSERT2_lemma];



(* Konig 1931, page 37 *)
Theorem konig_matching_thm:
  !G. bipartite G ==> MAX_SET (IMAGE CARD (matching G)) = MIN_SET (IMAGE CARD (vertex_cover G))
Proof                           (* TODO *)
  (*  *)
  rw [bipartite_alt]
  >> ‘gen_bipartite G A B’ by rw [gen_bipartite_alt]
  >> Q.SPEC_THEN ‘G’ MP_TAC maximal_matching_exists
  >> STRIP_TAC
  >> gvs [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]
  >> rename [‘_ = {Aend _; Bend _}’] (* This is to easily define f as well as find two ends in a bipartition. *)
  >> Q.ABBREV_TAC ‘f = \e. if ?p. alternating_path G M p /\ HD p IN A /\ LAST p = Bend e then Bend e else Aend e’
  >> Q.ABBREV_TAC ‘U = IMAGE f M’
  >> sg ‘CARD M = CARD U’       (* I probably need this outside the subgoal *)
  >- (Q.SPECL_THEN [‘f’,‘M’] MP_TAC CARD_IMAGE_INJ
      >> Q.SPECL_THEN [‘G’,‘M’] MP_TAC finite_matching
      >> rw []
      >> pop_assum (irule o GSYM)
      >> (rw[Abbr ‘f’] >> CCONTR_TAC) (* So that all 4 subgoals are contradiction *)
      (*
            Below is tediously repetitive - subgoals only differ in assumption "u = v"
            where u IN {Aend x; Bend x;} and v IN {Aend y; Bend y};
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
     by >= /\ <= *)
  >> pop_assum SUBST1_TAC
  >> qsuff_tac ‘U ∈ vertex_cover G’
  >- (STRIP_TAC
      >> irule MIN_SET_TEST >> simp [PULL_EXISTS]
      >> Q.EXISTS_TAC ‘U’ >> simp []
      >> simp [EXTENSION, PULL_EXISTS]
      >> Q.EXISTS_TAC ‘U’ >> simp []
      >> CCONTR_TAC >> gvs [NOT_LE]
      >> rename [‘CARD U' < CARD U’]
      >> ‘gen_vertex_cover V M U'’ by METIS_TAC [IN_APP, gen_vertex_cover_subset, matching_def]
      >> ‘CARD M <= CARD U'’ by METIS_TAC [vertex_cover_matching_card]
      >> rw [LET_TRANS]
     )
  >> simp [Once IN_APP] >> rw [gen_vertex_cover_def]
  (* RTP: U SUBSET V *)
  >- (‘M SUBSET E’ by gvs [matching_def]
      >> pop_assum MP_TAC
      >> rw [Abbr ‘U’, SUBSET_DEF]
      >> rw [Abbr ‘f’]
      >- METIS_TAC [Q.SPEC ‘G’ fsgraph_valid]
      >- METIS_TAC [Q.SPEC ‘G’ fsgraph_valid]
     )
  (* RTP: ?v. v IN U /\ v IN e *)
  >> qsuff_tac ‘Aend e NOTIN U ==> Bend e IN U’
  >- METIS_TAC [COMPONENT, INSERT2_lemma]
  >> DISCH_TAC
  >> sg ‘!e. e IN E ==> Aend e <> Bend e’
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
          >> sg ‘e NOTIN M’
          >- (gvs [unmatched_def]
              >> STRIP_TAC
              >> FIRST_X_ASSUM drule
              >> METIS_TAC [COMPONENT]
             )
          >> Q.PAT_X_ASSUM ‘!N. matching G N ==> _’ drule
          >> ‘FINITE M’ by METIS_TAC [finite_matching]
          >> simp []
         )
      >- (simp [Abbr ‘f’, Abbr ‘U’, AllCaseEqs ()] >> simp [EXISTS_OR_THM]
          >> gvs [AllCaseEqs (), FORALL_AND_THM]
          >> pop_assum MP_TAC >> rw [unmatched_def]
          >> qexists_tac ‘e'’ >> rw []
          >> DISJ1_TAC
          >> sg ‘Bend e' = Bend e’
          >- (‘e' IN E’ by ASM_SET_TAC [matching_def]
              >> LAST_ASSUM drule
              >> STRIP_TAC
              >> ‘Bend e = Aend e' \/ Bend e = Bend e'’ by ASM_SET_TAC []
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
  >> ‘e' IN E’ by ASM_SET_TAC [matching_def]
  >> ‘Aend e = Aend e'’ by ASM_SET_TAC []
  >> ‘Bend e' IN U’ by ASM_SET_TAC []
  >> Cases_on ‘e = e'’
  >- rw []
  >> sg ‘e NOTIN M’
  >- (
     gvs [matching_def]
     >> ‘e' IN E’ by ASM_SET_TAC [matching_def]
     >> Q.PAT_X_ASSUM ‘!e1 e2. _’ MP_TAC
     >> rw [Once MONO_NOT_EQ]
     >> Q.EXISTS_TAC ‘e’ >> Q.EXISTS_TAC ‘e'’
     >> ASM_SET_TAC []
  )
  >> sg ‘?p. alternating_path G M p /\ HD p IN A /\ LAST p = Bend e'’
  >- (gvs [Abbr ‘U’, Abbr ‘f’]
      >> ‘e' = e''’ by ASM_SET_TAC [matching_def, DISJOINT_DEF]
      >> rw []
      >> pop_assum MP_TAC >> rw [Once MONO_NOT_EQ] >> rw []
      >> METIS_TAC []
     )
  >> Q.ABBREV_TAC ‘b = Bend e’
  >> Cases_on ‘matched G M b’
  >- (gs [matched_def]
      >> gvs [Abbr ‘f’, Abbr ‘U’]
      >> ‘e''' = e'’ by ASM_SET_TAC [matching_def] >> rw []
      >> ‘LAST p = Bend e'’ by ASM_SET_TAC [] >> rw []
      >> ‘p <> []’ by METIS_TAC [alternating_path_def, path_def, walk_def]
      >> qexists_tac ‘e''’ >> rw [] (* 2 *)
      >- ASM_SET_TAC [matching_def]
      >> pop_assum MP_TAC >> rw [Once MONO_NOT_EQ]
      >> Q.ABBREV_TAC ‘a = Aend e’
      >> Q.ABBREV_TAC ‘b' = Bend e'’
      >> Cases_on ‘MEM b p’
      >- (drule $ iffLR MEM_EL >> DISCH_TAC >> gs []
          >> Q.ABBREV_TAC ‘pb = TAKE (SUC n) p’
          >> ‘pb <<= p’ by METIS_TAC [GSYM IS_PREFIX_EQ_TAKE']
          >> qexists_tac ‘pb’ >> rw []               (* 3 *)
          >- (irule alternating_path_prefix >> rw [] (* 2 *)
              >- (sg ‘LAST pb = EL n pb’
                  >- (irule LAST_EL_LENGTH_lemma
                      >> rw [LENGTH_TAKE, Abbr ‘pb’]
                     )
                  >> simp [Abbr ‘pb’]
                 )
              >> qexists_tac ‘p’ >> rw []
             )
          >- (‘HD pb = HD p’ suffices_by simp []
              >> Q.UNABBREV_TAC ‘pb’
              >> irule HD_TAKE >> simp []
             )
          >> sg ‘LAST pb = EL n p’
          >- (sg ‘LAST pb = EL n pb’
              >- (irule LAST_EL_LENGTH_lemma >> simp [Abbr ‘pb’])
              >> rw []
              >> irule is_prefix_el >> simp [Abbr ‘pb’]
             )
          >> rw []
          >> ‘e'' IN E’ by ASM_SET_TAC [matching_def]
          >> ASM_SET_TAC []
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
          >> ‘?x xs. p = x::xs’ by METIS_TAC [LIST_NOT_NIL]
          >> rw [Abbr ‘pb'ab’]
         )
      >> rw [alternating_path_def] (* 3 *)
      >- (rw [path_def]         (* 2 *)
          >- (rw [walk_def]     (* 3 *)
              >- rw [Abbr ‘pb'ab’]
              >- (rw [path_def, walk_def, alledges_valid]
                  >> pop_assum MP_TAC
                  >> rw [Abbr ‘pb'ab’, MEM_APPEND]
                  >- (‘path G p’ by METIS_TAC [alternating_path_def]
                      >> METIS_TAC [path_subset_nodes, SUBSET_DEF]
                     )
                  >- (Q.PAT_X_ASSUM ‘!e. e IN E ==> e = {_; _} /\ _’ (MP_TAC o Q.SPEC ‘e'’)
                      >> ASM_SET_TAC []
                     )
                  >> Q.SPECL_THEN [‘e''’, ‘G’] MP_TAC (GEN_ALL alledges_valid)
                  >> impl_tac
                  >- ASM_SET_TAC [matching_def]
                  >> rw [] >> gs []
                 )
              >> Know ‘adjacent (REVERSE pb'ab) v2 v1’
              >- (rw [adjacent_reversible])
              >> pop_assum K_TAC
              >> SIMP_TAC std_ss [Abbr ‘pb'ab’, REVERSE_APPEND]
              >> simp [adjacent_iff]
              >> STRIP_TAC      (* 2 *)
              >- (rw [Once adjacent_fsg]
                  >> ‘e = {Aend e'; b}’ by ASM_SET_TAC [COMPONENT]
                  >> pop_assum (fn t => rw [Once $ GSYM t])
                 )
              >> irule $ iffLR adjacent_fsg_reversible
              >> pop_assum mp_tac
              >> drule REVERSE_LAST_CONS_TL_lemma
              >> disch_then (fn t => ONCE_REWRITE_TAC [t])
              >> disch_tac
              >> drule $ (GEN_ALL o iffLR) adjacent_iff
              >> STRIP_TAC      (* 2 *)
              >- (gvs []
                  >> Q.PAT_X_ASSUM ‘Aend e' = _’ (fn t => rw [Once $ GSYM t])
                  >> rw [adjacent_fsg]
                  >> LAST_X_ASSUM drule
                  >> disch_then (fn t => rw [Once $ (GSYM o CONJUNCT1) t])
                 )
               >> gs [GSYM REVERSE_LAST_CONS_TL_lemma]
              >> METIS_TAC [alternating_path_def, path_def, walk_def]
             )
          >> simp [Abbr ‘pb'ab’]
          >> ONCE_REWRITE_TAC [GSYM APPEND_ASSOC]
          >> rw [Once ALL_DISTINCT_APPEND] (* 4 *)
          >- METIS_TAC [alternating_path_def, path_def]
          >- METIS_TAC [Abbr ‘b’]
          >- (STRIP_TAC >> gvs []
              >> sg ‘{Bend e'; Aend e'} ∈ M’
              >- (‘e' = {Bend e'; Aend e'}’ by ASM_SET_TAC [COMPONENT]
                  >> pop_assum (fn t => rw [GSYM t])
                 )
              >> ‘Aend e' ∈ A’ by METIS_TAC []
              >> drule_all $ iffRL alternating_path_matched_edge_iff
              >> simp [adjacent_ps_append]
              >> rpt STRIP_TAC
              >> ‘ALL_DISTINCT p’ by METIS_TAC [alternating_path_def, path_def]
              >> pop_assum MP_TAC
              >> Q.ABBREV_TAC ‘lp = LAST p’
              >> ‘MEM lp s’ suffices_by (simp [ALL_DISTINCT_APPEND] >> METIS_TAC [])
              >> Cases_on ‘s = []’
              >- gvs []
              >> Q.PAT_X_ASSUM ‘p = _’ (MP_TAC o Q.AP_TERM ‘LAST’)
              >> simp [LAST_APPEND_NOT_NIL, LAST_MEM]
             )
          >> METIS_TAC []
         )
      >- (‘HD pb'ab = HD p’ by (simp [Abbr ‘pb'ab’] >> Cases_on ‘p’ >> gvs [])
          >> METIS_TAC [alternating_path_def]
         )
      >> Cases_on ‘SUC n < LENGTH p’
      >- (simp [EL_APPEND1, Abbr ‘pb'ab’]
          >> METIS_TAC [alternating_path_def]
         )
      >> ‘LENGTH pb'ab = LENGTH p + 2’ by simp [Abbr ‘pb'ab’]
      >> gvs []
      >> ‘SUC n = LENGTH p ∨ SUC n = LENGTH p + 1’ by simp []
      >- (‘EL n pb'ab = Bend e'’ by simp [Abbr ‘pb'ab’, EL_APPEND1, LAST_EL_LENGTH_lemma]
          >> ‘EL (SUC n) pb'ab = Aend e'’ by  simp [Abbr ‘pb'ab’, EL_APPEND2, EL_APPEND1]
          >> NTAC 2 POP_ORW
          >> ‘{Bend e'; Aend e'} = e'’ by ASM_SET_TAC []
          >> simp []
          >> irule $ iffRL alternating_path_zigzag_parity
          >> qexistsl_tac [‘A’, ‘B’, ‘G’, ‘M’, ‘p’]
          >> sg ‘gen_bipartite G A B’
          >- (rw [gen_bipartite_alt]
              >> Q.EXISTS_TAC ‘Aend e'''’ >> Q.EXISTS_TAC ‘Bend e'''’
              >> rw []
             )
          >> rw []
          >> METIS_TAC [LAST_EL_LENGTH_lemma]
         )
      >> ‘n = LENGTH p’ by simp []
      >> sg ‘EL n pb'ab = Aend e'’
      >- (gvs [Abbr ‘pb'ab’, EL_APPEND1, EL_APPEND2] >> simp [])
      >> FIRST_ASSUM (fn t => ONCE_REWRITE_TAC [t])
      >> ‘EL (SUC n) pb'ab = b’ by simp [Abbr ‘pb'ab’, EL_APPEND1, EL_APPEND2]
      >> POP_ORW
      >> ‘{Aend e'; b} = e’ by ASM_SET_TAC [] >> simp []
      >> Q.ABBREV_TAC ‘m = PRE n’
      >> ‘EL m p ∈ B’ by (drule LAST_EL >> gvs [] >> ASM_SET_TAC [])
      >> ‘LENGTH p = SUC m’ by gvs [NOT_NIL_EQ_LENGTH_NOT_0, SUC_PRE]
      >> ‘ODD m’ suffices_by (POP_ORW >> simp [ODD])
      >> irule $ iffRL alternating_path_zigzag_parity
      >> qexistsl_tac [‘A’, ‘B’, ‘G’, ‘M’, ‘p’]
      >> rw [Abbr ‘m’, SUC_PRE]
     )
  (* Case: unmatched G M b, contradiction as max matching has no aug. path *)
  >> ‘∃P. augmenting_path G M P’ suffices_by METIS_TAC [
        NOT_LE, augmenting_path_augments_matching, bipartite_gen_bipartite
      ]
  >> Q.ABBREV_TAC ‘a = Aend e’  (*  *)
  >> Cases_on ‘MEM b p’
  >- (drule $ iffLR MEM_EL >> DISCH_TAC >> gs []
      >> Q.ABBREV_TAC ‘pb = TAKE (SUC n) p’
      >> ‘pb <<= p’ by METIS_TAC [GSYM IS_PREFIX_EQ_TAKE']
      >> ‘LENGTH pb = SUC n’ by gvs [LENGTH_TAKE, Abbr ‘pb’]
      >> qexists_tac ‘pb’ >> rw [augmenting_path_def]
      >- (irule alternating_path_prefix >> reverse $ rw []
          >- (qexists_tac ‘p’ >> rw [])
          >> CCONTR_TAC >> gvs []
         )
      >> drule LAST_EL_LENGTH_lemma >> rw []
      >> ‘EL n pb = EL n p’ suffices_by gvs [unmatched]
      >> irule is_prefix_el >> simp []
     )
  >> Q.ABBREV_TAC ‘pb'ab = p ++ [a] ++ [b]’
  >> Q.EXISTS_TAC ‘pb'ab’ >> reverse $ rw [augmenting_path_def]
  >- (simp [Abbr ‘pb'ab’, unmatched])
  >> rw [Abbr ‘pb'ab’] >> irule alternating_path_append >> rw []
  >- (gvs [Abbr ‘b’]
      >> Q.PAT_X_ASSUM ‘Aend e = _’ (fn t => ONCE_REWRITE_TAC [GSYM t])
      >> simp []
     )
  >- (rw [adjacent_fsg]
      >> Q.PAT_X_ASSUM ‘Aend e = _’ (fn t => ONCE_REWRITE_TAC [GSYM t])
      >> simp [Abbr ‘b’]
      >> ‘{Bend e; Aend e} = e’ by ASM_SET_TAC []
      >> rw []
     )
  >- (irule alternating_path_append >> rw []
      >- (CCONTR_TAC >> gs []
          >> ‘{Bend e'; Aend e'} = e'’ by ASM_SET_TAC []
          >> ‘{Bend e'; Aend e'} ∈ M’ by rw []
          >> drule_all alternating_path_matched_edge_iff >> rw []
          >> ‘¬adjacent p (LAST p) (Aend e')’ suffices_by gvs []
          >> irule ALL_DISTINCT_LAST_NOT_ADJ_lemma
          >> gvs [alternating_path_def, path_def, walk_def]
         )
      >- (rw [adjacent_fsg]
          >> ‘{Aend e'; Bend e'} = e'’ by ASM_SET_TAC []
          >> rw []
         )
      >> qexistsl_tac [‘A’, ‘B’] >> ‘{Aend e'; Bend e'} = e'’ by ASM_SET_TAC [] >> rw []
     )
  >> qexistsl_tac [‘A’, ‘B’] >> rw []
  >- (CCONTR_TAC >> ASM_SET_TAC [])
  >> ‘p ≠ []’ by gvs [alternating_path_def, path_def, walk_def]
  >> drule_then ASSUME_TAC $ iffLR LIST_NOT_NIL
  >> POP_ORW >> rw [HD]
QED

Theorem minimal_vertex_cover_exists:
  !(G: fsgraph). bipartite G ⇒ ?U. vertex_cover G U /\ CARD U = MIN_SET (IMAGE CARD (vertex_cover G))
Proof                           (* TODO *)
  (* By Above *)
  rw [] >> drule konig_matching_thm >> rw []
  >> MP_TAC $ Q.SPEC ‘G’ max_matching_exists >> rw [max_matching_def]
  >> cheat
QED


Theorem marriage_thm:
  !(G: fsgraph). gen_bipartite G A B ==>
                 ((?M. matching G M /\ matched_set G M A) <=> !S. S SUBSET A ==> CARD S ≤ CARD (N S))
Proof
  rw [gen_bipartite_def] >> iff_tac
  >- (rw [neighbour_def]
      >> drule matching_as_subgraph >> rpt STRIP_TAC
      >> ‘CARD S' = CARD (N' S')’ suffices_by (
        rw [] >> drule neighbour_set_subgraph_CARD >> ASM_SET_TAC []
        )
      >> ‘A ⊆ V’ by ASM_SET_TAC []
      >> drule_all matched_set_f
      >> rw []
      >> sg ‘INJ f S' V’
      >- (irule INJ_SUBSET
          >> qexistsl_tac [‘A’, ‘V’]
          >> rw []
         )
      >>
     )
QED









val _ = export_theory();
