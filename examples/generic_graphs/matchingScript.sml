Theory matching
Ancestors
  fsgraph pred_set arithmetic list genericGraph set_relation
  rich_list integer combin topology While pair real prim_rec
Libs
  pred_setLib hurdUtils tautLib

Overload V[local] = “nodes (G :fsgraph)”;
Overload E[local] = “fsgedges (G :fsgraph)”;

Type vertex[pp] = “:unit + num”;
Type edge = “:vertex set”

val ORW = ONCE_REWRITE_TAC;
val POP_ORW' = pop_assum (fn t => ORW [GSYM t])
val Keep_last_assum = (fn n => NTAC n (pop_assum mp_tac) >> KILL_TAC)
val Keep_last_assum_disch = (fn n => Keep_last_assum n >> rpt disch_tac)
val _ = clear_overloads_on "equiv_class";
val set_ss = std_ss ++ PRED_SET_ss;
val set_simp = ASM_SIMP_TAC set_ss;

(* List lemmas *)


(* Set lemmas *)
Theorem PAIR_SYM_lemma:
  ∀a b. {a; b} = {b; a}
Proof
  ASM_SET_TAC []
QED

Theorem CARD_LT_DIFF_lemma:
  ∀t s. FINITE t ∧ FINITE s ⇒ (CARD t < CARD s ⇔ CARD (t DIFF s) < CARD (s DIFF t))
Proof
  rw [] >> reverse iff_tac
  >- (rw [Once INTER_COMM, GSYM SUB_LESS_0] >> gvs [CARD_DIFF, Once $ GSYM SUB_LESS_0]
      >> gvs [INTER_COMM])
  >> rw [Once INTER_COMM, GSYM SUB_LESS_0]
  >> ONCE_REWRITE_TAC [INTER_COMM]
  >> ‘CARD (t ∩ s) ≤ CARD t’ by (irule CARD_INTER_LESS_EQ >> rw [])
  >> simp []
QED

Theorem IN_EDGE_lemma:
  ∀e a b. (∀x. x ∈ e ⇔ x = a ∨ x = b) ⇔ (e = {a; b})
Proof
  SET_TAC []
QED

Theorem EXT_CHOICE_DEF:
  ∀x s. s ≠ ∅ ⇒ (x = CHOICE s ⇒ x ∈ s)
Proof
  PROVE_TAC [CHOICE_DEF]
QED

Theorem EXT_CHOICE_ABBR:
  ∀x s. s ≠ ∅ ∧ Abbrev (x = CHOICE s) ⇒ x ∈ s
Proof
  rpt strip_tac >> rw [Abbr ‘x’, CHOICE_DEF]
QED


(* Set relation lemmas *)

Theorem finite_linear_order_has_local_maximal_lemma:
  ∀s t r. FINITE s ∧ linear_order r s ∧ t ⊆ s ∧ t ≠ ∅ ⇒ ∃x. x ∈ maximal_elements t r
Proof
  rw [] >> Suff ‘∃x. x ∈ maximal_elements t (rrestrict r t)’
  >- (simp [maximal_elements_def, rrestrict_def] >> PROVE_TAC []
     )
  >> irule finite_linear_order_has_maximal >> reverse $ rw []
  >- (irule linear_order_subset >> qexists_tac ‘s’ >> art [])
  >> PROVE_TAC [SUBSET_FINITE]
QED


Theorem maximal_linear_order_local:
  ∀s t r x y.
    t ⊆ s ∧ y ∈ t ∧ linear_order r s ∧ x ∈ maximal_elements t r ⇒ (y,x) ∈ r
Proof
  rw [] >> ‘(y,x) ∈ rrestrict r t’ suffices_by PROVE_TAC [rrestrict_SUBSET, SUBSET_DEF]
  >> irule maximal_linear_order >> qexists_tac ‘t’ >> rw []
  >- ASM_SET_TAC [maximal_elements_def, rrestrict_def]
  >> irule linear_order_subset >> qexists_tac ‘s’ >> art []
QED

(* Weaker. *)
Theorem maximal_linear_order_local':
  ∀s t r x y z.
    t ⊆ s ∧ y ∈ t ∧ linear_order r s ∧ z ∈ maximal_elements t r ∧ (z,x) ∈ r ⇒ (y,x) ∈ r
Proof
  rw [] >> ‘transitive r’ by gvs [linear_order_def]
  >> fs [transitive_def] >> pop_assum irule
  >> drule_all_then assume_tac maximal_linear_order_local
  >> qexists_tac ‘z’ >> art []
QED



Theorem SING_ELEMENT_IFF:
  ∀s. s ≠ ∅ ⇒ (SING s ⇔ ∀x y. x ∈ s ∧ y ∈ s ⇒ x = y)
Proof
  rw [] >> iff_tac
  >- (art [Q.SPEC ‘s’ SING_ELEMENT])
  >> rw [SING_DEF] >> ASM_SET_TAC []
QED


Theorem maximal_elements_IN:
  ∀x s r. x ∈ maximal_elements s r ⇒ x ∈ s
Proof
  rw [maximal_elements_def]
QED


Theorem finite_linear_order_maximal_SING:
  ∀s r. FINITE s ∧ s ≠ ∅ ∧ linear_order r s ⇒ SING $ maximal_elements s r
Proof
  rw [] >> drule_all finite_linear_order_has_maximal >> rw [maximal_elements_def, SING_DEF, Once EXTENSION]
  >> qexists_tac ‘x’ >> rw [] >> rename [‘_ ⇔ y = x’] >> iff_tac
  >- (rw [] >> gvs [linear_order_def] >> PROVE_TAC []
     )
  >> PROVE_TAC []
QED

Theorem finite_linear_order_local_maximal_SING:
  ∀s t r. FINITE s ∧ t ⊆ s ∧ t ≠ ∅ ∧ linear_order r s ⇒ SING $ maximal_elements t r
Proof
  rw [] >> Suff ‘SING $ maximal_elements t (rrestrict r t)’
  >- (rw [maximal_elements_def, rrestrict_def, SING_DEF]
      >> qexists_tac ‘x’ >> ASM_SET_TAC []
     )
  >> Suff ‘linear_order (rrestrict r t) t’
  >- (disch_tac >> irule finite_linear_order_maximal_SING >> PROVE_TAC [SUBSET_FINITE]
     )
  >> drule linear_order_restrict
  >> ‘t = s ∩ t’ by ASM_SET_TAC [] >> PROVE_TAC []
QED

Theorem maximal_linear_SING = finite_linear_order_local_maximal_SING

Theorem linear_order_restrict_SUBSET = linear_order_subset

(* fsg lemma *)
Theorem alledges_valid_alt:
  ∀(G: fsgraph) n1 n2. {n1; n2} ∈ E ⇒ n1 ∈ V ∧ n2 ∈ V ∧ n1 ≠ n2
Proof
  NTAC 4 STRIP_TAC >> drule alledges_valid >> ASM_SET_TAC []
QED

Theorem alledges_valid_adj:
  ∀(G: fsgraph) n1 n2. adjacent G n1 n2 ⇒ n1 ∈ V ∧ n2 ∈ V ∧ n1 ≠ n2
Proof
  REWRITE_TAC [adjacent_fsg, alledges_valid_alt]
QED

Theorem adjacent_fsg_SYM:
  ∀(G: fsgraph) n1 n2. adjacent G n1 n2 ⇔ adjacent G n2 n1
Proof
  rw [adjacent_fsg]
  >> ‘{n1; n2} = {n2; n1}’ by SET_TAC []
  >> POP_ORW >> rw []
QED

Theorem fsg_FINITE_degree:
  ∀(G: fsgraph) v. v ∈ V ⇒ FINITE {e | e ∈ E ∧ v ∈ e}
Proof
  rw [] >> irule SUBSET_FINITE_I >> qexists_tac ‘E’
  >> simp [FINITE_fsgedges] >> ASM_SET_TAC []
QED


(* Bipartite graph identities *)
Theorem gen_bipartite_sym:
  ∀(G: fsgraph) A B. gen_bipartite G A B ⇔ gen_bipartite G B A
Proof
  ASM_SET_TAC [gen_bipartite_def]
QED

Theorem bipartite_gen_bipartite:
  ∀G. bipartite G ⇔ ∃A B. gen_bipartite G A B
Proof
  rw [gen_bipartite_def, bipartite_def]
QED

Theorem gen_bipartite_bipartite:
  ∀G A B. gen_bipartite G A B ⇒ bipartite G
Proof
  rw [gen_bipartite_def, bipartite_def]
  >> qexistsl_tac [‘A’, ‘B’] >> simp []
QED

Theorem gen_bipartite_SUBSET:
  ∀G A B ns. gen_bipartite G A B ∧ ns ⊆ V ⇒ ∃ns1 ns2. ns1 ⊆ A ∧ ns2 ⊆ B ∧ ns1 ∪ ns2 = ns ∧ DISJOINT ns1 ns2
Proof
  rw [gen_bipartite_def]
  >> qexistsl_tac [‘ns ∩ A’, ‘ns ∩ B’] >> ASM_SET_TAC []
QED

Theorem gen_bipartite_FINITE:
  ∀G A B. gen_bipartite G A B ⇒ FINITE A ∧ FINITE B
Proof
  NTAC 4 strip_tac >> gvs [gen_bipartite_def]
  >> ‘FINITE V’ by simp [FINITE_nodes] >> ‘A ⊆ V ∧ B ⊆ V’ by ASM_SET_TAC []
  >> PROVE_TAC [SUBSET_FINITE]
QED

(* paired_v: Helper that returns the neighbour of v ∈ e w.r.t. e ∈ E. *)
Definition paired_v_def:
  paired_v (e :edge) (v :vertex) = CHOICE $ e DELETE v
End

Theorem paired_v_thm:
  ∀(v1 :vertex) (v2 :vertex). v1 ≠ v2 ⇒ paired_v {v1; v2} v1 = v2
Proof
  rw [paired_v_def]
  >> sg ‘{v1; v2} DELETE v1 = {v2}’
  >- (ORW [DELETE_DEF] >> ORW [DIFF_DEF]
      >> rw [GSYM INTER_DEF, EXTENSION] >> METIS_TAC []
     )
  >> POP_ORW >> rw [CHOICE_SING]
QED

Theorem paired_v_thm2:
  ∀(v1 :vertex) (v2 :vertex). v1 ≠ v2 ⇒ paired_v {v1; v2} v2 = v1
Proof
  rpt STRIP_TAC
  >> ‘{v1; v2} = {v2; v1}’ by SET_TAC []
  >> POP_ORW >> irule paired_v_thm >> rw []
QED

Theorem paired_v_def':
  ∀(G :fsgraph) (e: edge) (v1 :vertex) (v2 :vertex). e ∈ E ∧ v1 ∈ e ∧ v2 ∈ e ∧ v1 ≠ v2 ⇒ paired_v e v1 = v2
Proof
  rw [] >> drule_then ASSUME_TAC alledges_valid >> rw []
  >> ‘v1 = a ∨ v1 = b’ by ASM_SET_TAC []
  >- (‘v2 = b’ by ASM_SET_TAC [] >> gvs []
      >> drule paired_v_thm >> rw []
     )
  >> ‘v2 = a’ by ASM_SET_TAC [] >> gvs []
  >> drule paired_v_thm2 >> rw []
QED

Theorem paired_v_IN:
  ∀(G :fsgraph) (e: edge) (v :vertex). e ∈ E ⇒ paired_v e v ∈ e
Proof
  rw [paired_v_def] >> reverse $ Cases_on ‘v ∈ e’
  >- (rw [DELETE_NON_ELEMENT_RWT] >> irule CHOICE_DEF
      >> drule alledges_valid >> SET_TAC [])
  >> drule alledges_valid >> rw [] >> gvs []
  >- (DISJ2_TAC >> ‘a ≠ b ⇒ {a; b} DELETE a = {b}’ by SET_TAC [] >> gvs []
     )
  >> DISJ1_TAC >> ‘a ≠ b ⇒ {a; b} DELETE b = {a}’ by SET_TAC [] >> gvs []
QED

Theorem paired_v_INJ:
  ∀(G :fsgraph) (e: edge) (v1 :vertex) (v2 :vertex).
    e ∈ E ∧ v1 ∈ e ∧ v2 ∈ e ⇒ (v1 = v2 ⇔ paired_v e v1 = paired_v e v2)
Proof
  rw [] >> iff_tac
  >- simp []
  >> rw [paired_v_def]
  >> drule alledges_valid >> rw [] >> gvs []
  >- (‘{a; b} DELETE a = {b} ∧ {a; b} DELETE b = {a}’ by ASM_SET_TAC []
      >> gvs []
     )
  >> ‘{a; b} DELETE a = {b} ∧ {a; b} DELETE b = {a}’ by ASM_SET_TAC []
  >> gvs []
QED

Theorem paired_v_NOTEQ:
  ∀(G :fsgraph) (e: edge) (v :vertex). e ∈ E ∧ v ∈ e ⇒ paired_v e v ≠ v
Proof
  rw [] >> drule alledges_valid >> rw [] >> gvs []
  >- (drule paired_v_thm >> rw [])
  >> drule paired_v_thm2 >> rw []
QED

Theorem paired_v_self:
  ∀(G :fsgraph) (e :edge) (v1 :vertex). e ∈ E ∧ v1 ∈ e ⇒ {v1; paired_v e v1} = e
Proof
  rw [] >> drule alledges_valid >> rw [] >> gvs [] >> simp [paired_v_thm, paired_v_thm2, PAIR_SYM_lemma]
QED



(* Subgraph. Probably should be in fsgraphtheory. *)
Overload V'[local] = “nodes (G' :fsgraph)”;
Overload E'[local] = “fsgedges (G' :fsgraph)”;
Overload V''[local] = “nodes (G'' :fsgraph)”;
Overload E''[local] = “fsgedges (G'' :fsgraph)”;

Definition subgraph_def:
  subgraph (G': fsgraph) (G: fsgraph) <=> V' SUBSET V /\ E' SUBSET E
End

Overload SUBSET = “subgraph”


(* Following might be useful as an overload ie. ‘G spans G'’ or smth *)
Definition span_subgraph_def:
  span_subgraph (G': fsgraph) (G: fsgraph) ⇔ G' ⊆ G ∧ V' = V
End


Definition induced_subgraph_def:
  induced_subgraph (G': fsgraph) (G: fsgraph) ⇔ G' ⊆ G ∧ ∀x y. (x ∈ V' ∧ y ∈ V' ∧ {x; y} ∈ E) ⇒ {x; y} ∈ E'
End



Theorem subgraph_id[simp]:
  ∀(G: fsgraph). G ⊆ G
Proof
  simp [subgraph_def]
QED

Theorem subgraph_exists:
  ∀(G: fsgraph). ∃G'. G' ⊆ G
Proof
  rw [] >> qexists_tac ‘G’ >> rw [subgraph_id]
QED

Theorem edges_as_subgraph:
  ∀(G: fsgraph) es. es ⊆ E ⇒ ∃G'. G' ⊆ G ∧ V' = V ∧ E' = es
Proof
  rw [subgraph_def]
  >> ‘∃G'. nodes G' = V ∧ fsgedges G' = es’ suffices_by ASM_SET_TAC []
  >> Q.EXISTS_TAC ‘fsgAddEdges es $ fsgAddNodes V emptyG’
  >> rw [fsgedges_fsgAddEdges, EXTENSION] >> iff_tac
  >- (rw []
      >> ‘x = {m; n}’ by ASM_SET_TAC [] >> simp []
     )
  >> rw []
  >> ‘x ∈ E’ by ASM_SET_TAC []
  >> drule alledges_valid >> rpt strip_tac
  >> qexistsl_tac [‘a’, ‘b’] >> simp []
  >> gvs []
QED


(* Neighbour *)
(* TODO: refactor ‘paired_v’ into ‘neighbour’ after replacing existing ‘neighbour’ with ‘neighbours’ *)
(* Originally defined using neighbour_def but was oberved to be equivalent to adjacent_fsg *)
(* Hence the nuance lies within treating adjacent as (naive) relation and neighbour as a set *)


Definition neighbour:
  neighbour (G :fsgraph) = adjacent G
End

Theorem neighbour_def:
  ∀G v. neighbour (G: fsgraph) v = {v' | v' IN V /\ v' <> v /\ ?e. e IN E /\ v IN e /\ v' IN e}
Proof
  rw [neighbour, Once EXTENSION]
  >> ‘x ∈ adjacent G v ⇔ adjacent G v x’ by simp [IN_APP] >> POP_ORW
  >> rw [adjacent_fsg] >> iff_tac
  >- (disch_tac >> drule alledges_valid_alt >> rw []
      >> qexists_tac ‘{v; x}’ >> simp []
     )
  >> rw [] >> drule_then strip_assume_tac alledges_valid >> gvs [PAIR_SYM_lemma]
QED

(* Definition neighbour_def: *)
(*   neighbour (G: fsgraph) v = {v' | v' IN V /\ v' <> v /\ ?e. e IN E /\ v IN e /\ v' IN e} *)
(* End *)


Theorem neighbour_def_adj:
  ∀G v. neighbour G v = {v' | v' ∈ V ∧ adjacent (G: fsgraph) v v'}
Proof
  rw [neighbour_def, adjacent_fsg, EXTENSION] >> iff_tac
  >- (rw []
      >> ‘e = {v; x}’ suffices_by (rpt $ rw [])
      >> drule_then ASSUME_TAC alledges_valid >> gvs []
      >> ASM_SET_TAC []
     )
  >> strip_tac >> simp []
  >> drule alledges_valid_alt >> rw []
  >> qexists_tac ‘{v; x}’ >> rw []
QED

Theorem neighbour_def_adj_weak:
  ∀G v. neighbour G v = {v' | adjacent (G: fsgraph) v v'}
Proof
  rw [neighbour_def_adj, adjacent_fsg, Once EXTENSION]
  >> (iff_tac >> simp [])
  >> PROVE_TAC [alledges_valid_alt]
QED

Theorem neighbour_def_adj' = neighbour_def_adj_weak;

Theorem neighbour_iff_adj:
  ∀G v1 v2. v2 ∈ neighbour G v1 ⇔ adjacent G v1 v2
Proof
  rw [neighbour_def_adj_weak]
QED

Theorem adj_iff_neighbour = GSYM neighbour_iff_adj;

Theorem neighbour_iff_inedge:
  ∀G v1 v2. v2 ∈ neighbour G v1 ⇔ {v1; v2} ∈ E
Proof
  rw [neighbour_iff_adj, adjacent_fsg]
QED

Theorem neighbour_inedge':
  ∀G v1 v2. v2 ∈ neighbour G v1 ⇔ {v1; v2} ∈ E ∨ {v2; v1} ∈ E
Proof
  PROVE_TAC [neighbour_iff_inedge, PAIR_SYM_lemma]
QED

Theorem degree_neighbour_CARD_EQ:
  ∀G v. degree G v = CARD (neighbour G v)
Proof
  rw [neighbour_def_adj, degree_def]
  >> qabbrev_tac ‘f = \(n :vertex). {v; n}’
  >> qabbrev_tac ‘P = {v' | v' ∈ V ∧ adjacent G v v'}’
  >> qabbrev_tac ‘Q = {e | e ∈ E ∧ v ∈ e}’
  >> ORW [EQ_SYM_EQ] >> irule FINITE_BIJ_CARD >> rw []
  >- rw [Abbr ‘P’, GSPEC_AND]
  >> qexists_tac ‘f’ >> rw [Abbr ‘f’, Abbr ‘P’, Abbr ‘Q’, BIJ_DEF]
  >- (rw [INJ_DEF]
      >- (gvs [adjacent_fsg] >> simp [PAIR_SYM_lemma])
      >> ASM_SET_TAC []
     )
  >> rw [SURJ_DEF]
  >- (gvs [adjacent_fsg] >> simp [PAIR_SYM_lemma])
  >> drule alledges_valid >> rw [] >> gvs []
  >- (qexists_tac ‘b’ >> rw [adjacent_fsg])
  >> qexists_tac ‘a’ >> ORW [adjacent_fsg_SYM] >> rw []
  >- rw [Once adjacent_fsg]
  >> SET_TAC []
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

Theorem paired_v_in_neighbour:
  ∀G e v1 v2. e ∈ E ∧ v1 ∈ e ∧ v2 ∈ e ⇒ paired_v e v1 = v2 ⇒ v2 ∈ neighbour G v1
Proof
  rw [paired_v_def', neighbour_def]
  >- (drule alledges_valid >> rw [] >> gvs [])
  >- (irule paired_v_NOTEQ >> rw []
      >> qexists_tac ‘G’ >> rw []
     )
  >> qexists_tac ‘e’ >> rw []
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

Theorem neighbour_set_neighbour_set:
  ∀G U. U ⊆ V ∧ (∀n. n ∈ U ⇒ 0 < degree G n) ⇒ U ⊆ N (N U)
Proof
  rpt strip_tac >> rw [SUBSET_DEF, neighbour_set, PULL_EXISTS]
  >> first_x_assum (drule_then strip_assume_tac)
  >> sg ‘∃x'. adjacent G x x'’
  >- (gvs [degree_def]
      >> qabbrev_tac ‘es = {e | e ∈ E ∧ x ∈ e}’
      >> sg ‘∃e. e ∈ es’
      >- (ORW [MEMBER_NOT_EMPTY]
          >> ‘0 ≠ CARD es’ by simp [] >> pop_assum mp_tac
          >> ‘FINITE E’ by simp [FINITE_fsgedges]
          >> ‘es ⊆ E’ by ASM_SET_TAC []
          >> ‘FINITE es’ by PROVE_TAC [SUBSET_FINITE]
          >> drule CARD_EQ_0 >> PROVE_TAC []
         )
      >> ‘e ∈ E’ by ASM_SET_TAC []
      >> drule alledges_valid >> rw [Abbr ‘es’]
      >> gvs []
      >- (qexists_tac ‘b’ >> simp [adjacent_fsg]
         )
      >> qexists_tac ‘a’ >> simp [adjacent_fsg, Once PAIR_SYM_lemma]
     )
  >> qexistsl_tac [‘x'’, ‘x’] >> simp [neighbour_def_adj]
  >> gvs [adjacent_fsg] >> drule alledges_valid_alt >> rw [Once PAIR_SYM_lemma]
QED


(* k-regular, k-factor & set of preferences *)
Definition regular_def:
  regular k (G: fsgraph) ⇔ ∀v. v ∈ V ⇒ degree G v = k
End

(* FIXME: move G' to front *)
Definition factor_def:
  factor k (G': fsgraph) (G: fsgraph) ⇔ G' ⊆ G ∧ V' = V ∧ regular k G'
End

(* Definition preference: *)
(*   preference (G: fsgraph) (R: vertex -> (edge # edge) -> bool) ⇔ ∀v. v ∈ V ⇒ linear_order (R v) E *)
(* End *)

Definition preference_def:
  preference (G: fsgraph) R ⇔ ∀v. v ∈ V ⇒ linear_order (R v) (neighbour G v)
End

Theorem preference_no_equal:
  ∀G R v1 v2 v3. preference G R ∧ v1 ∈ V ∧ v2 ∈ neighbour G v1 ∧ v3 ∈ neighbour G v1 ⇒
                 ~((v2, v3) ∈ R v1 ∧ (v3, v2) ∈ R v1 ∧ v2 ≠ v3)
Proof
  rw [preference_def, linear_order_def, antisym_def, neighbour_def_adj_weak, adjacent_fsg]
  >> NTAC 2 $ dxrule_then strip_assume_tac alledges_valid_alt >> PROVE_TAC []
QED

Theorem preference_notin:
  ∀G R v1 v2 v3. preference G R ∧ v1 ∈ V ∧ v2 ∈ neighbour G v1 ∧ v3 ∈ neighbour G v1 ∧ v2 ≠ v3 ⇒
                 ((v2, v3) ∉ R v1 ⇔ (v3, v2) ∈ R v1)
Proof
  rw [preference_def, linear_order_def, antisym_def, neighbour_def_adj_weak, adjacent_fsg]
  >> NTAC 2 $ drule_then strip_assume_tac alledges_valid_alt
  >> ASM_SET_TAC []
QED

Theorem preference_notin2:
  ∀G R v1 v2 v3. preference G R ∧ v1 ∈ V ∧ {v1; v2} ∈ E ∧ {v1; v3} ∈ E ∧ v2 ≠ v3 ⇒
                 ((v2, v3) ∉ R v1 ⇔ (v3, v2) ∈ R v1)
Proof
  rw [GSYM adjacent_fsg, adj_iff_neighbour] >> PROVE_TAC [preference_notin]
QED

(* Component *)
Definition component_fsg_def:
  component G (H :fsgraph) ⇔ H ⊆ G ∧ connected H ∧ ~(∃G'. H ⊆ G' ∧ G' ⊆ G ∧ fsgsize H < fsgsize G' ∧ connected G')
End

Definition odd_comp_count_def:
  odd_comp_count G ⇔ {G' | component G G' ∧ ODD (CARD V')}
End


(* Matching *)

Definition matching_def:
  matching (G: fsgraph) M <=> (M SUBSET E) /\ (!e1 e2. e1 IN M /\ e2 IN M /\ e1 <> e2 ==> DISJOINT e1 e2)
End

Theorem matching_as_subgraph:
  ∀G M. matching G M ⇒ ∃G'. G' ⊆ G ∧ V' = V ∧ E' = M
Proof
  rw [matching_def] >> PROVE_TAC [edges_as_subgraph]
QED



Theorem matching_SUBSET:
  ∀G M. matching G M ⇒ ∀M'. M' ⊆ M ⇒ matching G M'
Proof
  ASM_SET_TAC [matching_def]
QED

Theorem matching_subgraph:
  ∀G G' M. G' ⊆ G ∧ matching G' M ⇒ matching G M
Proof
  ASM_SET_TAC [matching_def, subgraph_def]
QED

Theorem matching_UNION:
  ∀(G :fsgraph) M1 M2. matching G M1 ∧ matching G M2 ∧ DISJOINT (BIGUNION M1) (BIGUNION M2) ⇒ matching G (M1 ∪ M2)
Proof
  (rw [matching_def] >> METIS_TAC [DISJOINT_SYM])
QED

Theorem matching_DISJOINT_UNION_EQ:
  ∀(G :fsgraph) M1 M2. DISJOINT M1 M2 ⇒ (matching G (M1 ∪ M2) ⇔ matching G M1 ∧ matching G M2 ∧ DISJOINT (BIGUNION M1) (BIGUNION M2))
Proof
  rpt strip_tac >> reverse eq_tac
  >- simp [matching_UNION]
  >> rw [matching_def]
  >> first_x_assum irule >> rw []
  >> ASM_SET_TAC []
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

Theorem EMPTY_is_matching:
  ∀G. matching G ∅
Proof
  ASM_SET_TAC [matching_def]
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


Definition matched:
  matched (G: fsgraph) M v ⇔ matching G M ⇒ v ∈ BIGUNION M
End

Theorem matched_def:
  ∀G M v. matched G M v <=> matching G M ==> (?e. e IN M /\ v IN e)
Proof
  rw [matched, BIGUNION] >> METIS_TAC []
QED

Theorem matched_def_alt:
  ∀G M v. matched G M v <=> matching G M ==> (?v'. {v; v'} IN M)
Proof
  rw [matched] >> (reverse iff_tac >> rpt strip_tac)
  >- (gvs [] >> qexists_tac ‘{v; v'}’ >> rw []
     )
  >> gvs [matching_def] >> ‘s ∈ E’ by ASM_SET_TAC []
  >> drule_then strip_assume_tac alledges_valid >> gvs []
  >- (qexists_tac ‘b’ >> art [])
  >> qexists_tac ‘a’ >> art [Once PAIR_SYM_lemma]
QED

Theorem matched_impl:
  ∀G M v. matching G M ∧ matched G M v ==> (?e. e IN M /\ v IN e)
Proof
  PROVE_TAC [matched_def]
QED

Theorem matched_impl_alt:
  ∀G M v. matching G M ∧ matched G M v ==> (?v'. {v; v'} IN M)
Proof
  PROVE_TAC [matched_def_alt]
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

Theorem matched_set_UNION:
  ∀G M U W. matched_set G M U ∧ matched_set G M W ⇒ matched_set G M (U ∪ W)
Proof
  ASM_SET_TAC [matched_set_def]
QED

Theorem matched_set_CARD_LE_matching:
  ∀G M U. matching G M ∧ matched_set G M U ∧ (∀v1 v2. v1 ∈ U ∧ v2 ∈ U ⇒ {v1; v2} ∉ E) ⇒ CARD U ≤ CARD M
Proof
  rw [matched_set_def, matched_def]
  >> gvs [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]
  >> irule INJ_CARD >> CONJ_TAC
  >- PROVE_TAC [finite_matching]
  >> qexists_tac ‘f’ >> rw [INJ_DEF] >> gvs [matching_def]
  >> ‘f x ∈ M ∧ f x ∈ E’ by ASM_SET_TAC [] >> drule alledges_valid >> rw [] >> gvs [] >> ASM_SET_TAC []
QED

Theorem matched_set_CARD_LE_matching_bipartite:
  ∀G A B M U. gen_bipartite G A B ∧ matching G M ∧ matched_set G M U ∧ U ⊆ A ⇒ CARD U ≤ CARD M
Proof
  rw [] >> irule matched_set_CARD_LE_matching >> qexists_tac ‘G’ >> rw []
  >> gvs [gen_bipartite_def] >> ASM_SET_TAC []
QED

Theorem matched_set_inj_f_neighbour:
  ∀G M U. matching G M ∧ U ⊆ V ∧ matched_set G M U ⇒ (∃f. INJ f U (N U))
Proof
  rw [matched_set_def, matched] >> gvs []
  >> Cases_on ‘U = ∅’
  >- gvs []
  >> ‘N U ⊆ V’ by rw [SUBSET_DEF, neighbour_set_def]
  >> ‘∃f. ∀v. v ∈ U ⇒ v ∈ (f v) ∧ (f v) ∈ M’ by METIS_TAC [SKOLEM_THM]
  >> qexists_tac ‘λv. paired_v (f v) v’
  >> rw [INJ_DEF]
  >- (first_x_assum $ drule_then assume_tac >> gvs []
      >> ‘f v ∈ E’ by ASM_SET_TAC [matching_def]
      >> drule alledges_valid
      >> rw [paired_v_def'] >> gvs []
      >- (drule paired_v_thm >> rw []
          >> ‘a ∈ {a; b} ∧ b ∈ {a; b}’ by SET_TAC []
          >> drule_all paired_v_in_neighbour >> rw [neighbour_set_def]
          >> qexists_tac ‘a’ >> METIS_TAC []
         )
      >> drule paired_v_thm2 >> rw []
      >> ‘a ∈ {a; b} ∧ b ∈ {a; b}’ by SET_TAC []
      >> drule_all paired_v_in_neighbour >> rw [neighbour_set_def]
      >> qexists_tac ‘b’ >> METIS_TAC []
     )
  >> gvs [matching_def]
  >> Cases_on ‘f v = f v'’
  >- (‘v ∈ f v ∧ v ∈ f v'’ by ASM_SET_TAC []
      >> ‘f v ∈ M ∧ f v' ∈ M’ by ASM_SET_TAC []
      >> irule $ iffRL paired_v_INJ
      >> qexistsl_tac [‘G’, ‘f v’] >> rw [] >> ASM_SET_TAC []
     )
  >> ‘f v ∈ M ∧ f v' ∈ M’ by ASM_SET_TAC []
  >> last_x_assum drule_all
  >> ‘~DISJOINT (f v) (f v')’ suffices_by rw []
  >> rw [DISJOINT_DEF]
  >> qabbrev_tac ‘u = paired_v (f v) v’
  >> ‘u ∈ f v’ by (
    qunabbrev_tac ‘u’
    >> irule paired_v_IN
    >> qexists_tac ‘G’
    >> gvs [SUBSET_DEF]
    )
  >> ‘u ∈ f v'’ by (
    qpat_x_assum ‘u = _’ (fn t => rw [Once t])
    >> irule paired_v_IN
    >> qexists_tac ‘G’
    >> gvs [SUBSET_DEF]
    )
  >> ASM_SET_TAC []
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

(* Theorem: Given a matching M, there exists matched subsets Am ⊆ A, Bm ⊆ B with |Am| = |Bm| = M. *)
Theorem matching_between_nodes:
  ∀G A B M. gen_bipartite G A B ∧ matching G M
            ⇒ ∃Am Bm. Am ⊆ A ∧ Bm ⊆ B ∧
                      matched_set G M Am ∧ matched_set G M Bm ∧
                      CARD Am = CARD M ∧ CARD Bm = CARD M
Proof
  rw [gen_bipartite_alt] >> gvs [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]
  >> rename [‘_ = {Aend _; Bend _}’]
  >> ‘FINITE M’ by (drule finite_matching >> simp [])
  >> gvs [matching_def]
  >> sg ‘INJ Aend M A’
  >- (rw [INJ_DEF]
      >- ASM_SET_TAC []
      >> CCONTR_TAC >> ASM_SET_TAC []
     )
  >> sg ‘INJ Bend M B’
  >- (rw [INJ_DEF]
      >- ASM_SET_TAC []
      >> CCONTR_TAC >> ASM_SET_TAC []
     )
  >> qexistsl_tac [‘IMAGE Aend M’, ‘IMAGE Bend M’] >> rw [IMAGE_DEF, SUBSET_DEF]
  >- ASM_SET_TAC []
  >- ASM_SET_TAC []
  >- (rw [matched_set_def, matched_def]
      >> qexists_tac ‘x’ >> ASM_SET_TAC []
     )
  >- (rw [matched_set_def, matched_def]
      >> qexists_tac ‘x’ >> ASM_SET_TAC []
     )
  >- (pop_assum K_TAC
      >> drule_all INJ_CARD_IMAGE >> simp [IMAGE_DEF]
     )
  >> drule_all INJ_CARD_IMAGE >> simp [IMAGE_DEF]
QED


(* Vertex cover *)

Definition gen_vertex_cover_def:
  gen_vertex_cover ns es U <=> U SUBSET ns /\ !e. e IN es ==> ?v. v IN U /\ v IN e
End

(* Overload vertex_cover = “\(G: fsgraph) U. gen_vertex_cover V E U” *)
Overload vertex_cover = “λ(G: fsgraph). gen_vertex_cover V E”
val vertex_cover_def = gen_vertex_cover_def;

Theorem gen_vertex_cover_subset:
  !ns es1 es2 U. gen_vertex_cover ns es1 U /\ es2 SUBSET es1 ==> gen_vertex_cover ns es2 U
Proof
  METIS_TAC [gen_vertex_cover_def, SUBSET_DEF]
QED

Theorem gen_vertex_cover_UNION:
  !ns es1 es2 U1 U2. gen_vertex_cover ns es1 U1 ∧
                     gen_vertex_cover ns es2 U2
                     ⇒ gen_vertex_cover ns (es1 ∪ es2) (U1 ∪ U2)
Proof
  simp [gen_vertex_cover_def, SUBSET_DEF] >> SET_TAC []
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

Theorem vertex_cover_bipartition:
  ∀(G: fsgraph) A B. gen_bipartite G A B ⇒ vertex_cover G A
Proof
  rw [gen_bipartite_alt, vertex_cover_def]
  >- ASM_SET_TAC []
  >> gvs [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]
  >> qexists_tac ‘f e’ >> ASM_SET_TAC []
QED

(* Lemma: if U covers a matching M, then |M| <= |U|. *)
Theorem vertex_cover_matching_card:
  ∀(G: fsgraph) M U. gen_vertex_cover V M U /\ matching G M ==> CARD M <= CARD U
Proof
  rpt STRIP_TAC >> irule INJ_CARD >> CONJ_TAC
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
  >- (gvs [matching_def]
      >> pop_assum MP_TAC >> rpt SELECT_ELIM_TAC >> rw []
      >- METIS_TAC [gen_vertex_cover_def]
      >- METIS_TAC [gen_vertex_cover_def]
      >- (‘x IN e INTER e'’ by rw [INTER_DEF]
          >> Cases_on ‘DISJOINT e e'’
          >- METIS_TAC [NOT_IN_EMPTY, DISJOINT_DEF]
          >- (gvs [DISJOINT_DEF, matching_def] >> METIS_TAC [matching_def])
         )
     )
QED

Theorem vertex_cover_gen_matching_card:
  ∀G U. vertex_cover G U ⇒ ∀M. matching G M ⇒ CARD M ≤ CARD U
Proof
  rw [] >> irule vertex_cover_matching_card
  >> qexists_tac ‘G’ >> rw []
  >> irule gen_vertex_cover_subset
  >> qexists_tac ‘E’ >> gvs [matching_def]
QED

(* Alternating & Augmenting Path *)
Definition alternating_path:
  alternating_path G M P <=> matching G M /\ path G P /\
                             unmatched G M (HD P) /\
                             !(n: num). SUC n < LENGTH P ==> ({EL n P; EL (SUC n) P} IN M ⇔ ODD n)
End

Theorem alternating_path_def:
  ∀G M P. alternating_path G M P <=> matching G M /\ path G P /\
                             unmatched G M (HD P) /\
                             !(n: num). SUC n < LENGTH P ==> (ODD n <=> {EL n P; EL (SUC n) P} IN M)
Proof
  METIS_TAC [alternating_path]
QED

Theorem adjacent_reversible[simp]: (* TODO: chuck this elsewhere *)
  !l a b. adjacent (REVERSE l) a b <=> adjacent l b a
Proof
  ‘!l a b. adjacent l b a ==> adjacent (REVERSE l) a b’ suffices_by METIS_TAC [REVERSE_REVERSE]
  >> Induct_on ‘list$adjacent’ >> ORW [CONS_APPEND]
  >> rw [adjacent_append2]
QED

Theorem adjacent_fsg_reversible[simp]:
  !(G: fsgraph) a b. adjacent G a b <=> adjacent G b a
Proof
  rw [adjacent_SYM]
QED

(* tautLib *)
Definition XOR:                 (* boolTheory may need this, could not find *)
  $XOR = (\t1 t2. (t1 ∧ ~t2) ∨ (~t1 ∧ t2))
End

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

(* Definition augmenting_path_def: *)
(*   augmenting_path G M P <=> alternating_path G M P /\ unmatched G M (LAST P) *)
(* End *)

(* CHANGED: added 1 < LENGTH P *)
Definition augmenting_path_def:
  augmenting_path G M P <=> alternating_path G M P /\ unmatched G M (LAST P) ∧ 1 < LENGTH P
End


Theorem augmenting_path_even_length:
  ∀G M P. bipartite G ∧ augmenting_path G M P ⇒ EVEN $ LENGTH P
Proof
  rw [augmenting_path_def]
  >> drule $ iffLR alternating_path_def >> rw []
  >> qabbrev_tac ‘l = LENGTH P’
  >> qsuff_tac ‘EVEN (l - 2)’
  >- (rw [EVEN_MOD2] >> rfs [SUB_MOD])
  >> ‘P ≠ []’ by fs [path_def, walk_def]
  >> gvs [LAST_EL, bipartite_def]
  >> ‘gen_bipartite G A B’ by rfs [gen_bipartite_def]
  >> ‘SUC (l - 2) < l’ by simp [Abbr ‘l’]
  >> first_x_assum drule >> rw [EVEN_ODD, ADD1]
  >> rfs [LAST_EL, PRE_SUB1, unmatched_def]
  >> qabbrev_tac ‘e = {EL (l − 2) P; EL (l − 1) P}’
  >> rfs [Once MONO_NOT_EQ]
  >> last_x_assum irule
  >> rw [Abbr ‘e’]
QED


Theorem augmenting_path_bipartite_hd_last:
  ∀G A B M P. gen_bipartite G A B ∧ augmenting_path G M P ∧ HD P ∈ A ⇒ LAST P ∈ B
Proof
  rw []
  >> qabbrev_tac ‘l = LENGTH P’
  >> ‘EVEN l’ by
    (rw [Abbr ‘l’]
     >> irule augmenting_path_even_length
     >> drule_then assume_tac gen_bipartite_bipartite
     >> qexistsl_tac [‘G’, ‘M’] >> rw []
    )
  >> fs [augmenting_path_def]
  >> ‘P ≠ []’ by (gvs [alternating_path_def, path_def, walk_def])
  >> ‘matching G M’ by gvs [alternating_path_def]
  >> rw [LAST_EL]
  >> irule $ iffLR alternating_path_zigzag_parity
  >> simp [] >> reverse CONJ_TAC
  >- (qexistsl_tac [‘A’, ‘G’, ‘M’] >> rw [])
  >> rw [PRE_SUB1]
  >> irule $ iffRL ODD_SUB >> simp [GSYM EVEN_ODD]
QED

Theorem augmenting_path_reversible:
  ∀G M P. bipartite G ⇒ (augmenting_path G M P ⇔ augmenting_path G M (REVERSE P))
Proof
  rw []
  >> qsuff_tac ‘∀M P. bipartite G ∧ augmenting_path G M P ⇒ augmenting_path G M (REVERSE P)’
  >- (rw [] >> eq_tac
      >- rw []
      >> ‘P = REVERSE $ REVERSE P’ by rw [REVERSE_REVERSE]
      >> POP_ORW >> rw []
     )
  >> rw [augmenting_path_def, alternating_path_def] >~
  [‘unmatched _ _ (HD _) (*g*)’]
  >- (gvs [alternating_path_def, path_def, walk_def] >> rw [HD_REVERSE]) >~
  [‘unmatched _ _ (LAST _) (*g*)’]
  >- (gvs [alternating_path_def, path_def, walk_def] >> rw [LAST_REVERSE])
  >> rw [EL_REVERSE]
  >> qabbrev_tac ‘l = LENGTH P’
  >> simp [PRE_SUB1, ADD1] >> ORW [SUB_PLUS]
  >> last_assum $ drule_all_then assume_tac
  >> pop_assum (fn t => ORW [GSYM ADD1] >> ORW [GSYM t])
  >> qabbrev_tac ‘m = l - n - 2’
  >> ‘l - n - 1 = m + 1’ by gvs [Abbr ‘m’] >> POP_ORW
  >> ORW [PAIR_SYM_lemma] >> ORW [GSYM ADD1]
  >> ‘SUC m < l’ by simp [Abbr ‘m’]
  >> last_assum $ drule_all_then assume_tac
  >> pop_assum (fn t => ORW [GSYM ADD1] >> ORW [GSYM t])
  >> ‘augmenting_path G M P’ by rw [augmenting_path_def, alternating_path_def]
  >> drule_all augmenting_path_even_length
  >> qpat_x_assum ‘∀n. _’ (fn t => all_tac)
  >> gvs [Abbr ‘m’]
  >> intLib.ARITH_TAC
QED


(* alt definition using head and last *)
Theorem augmenting_path_alt:
  ∀G A B M P. gen_bipartite G A B ⇒ (
    augmenting_path G M P ⇔ alternating_path G M P /\ unmatched G M (LAST P) ∧ (HD P ∈ A ⇔ LAST P ∈ B)
    )
Proof
  rw [] >> (reverse iff_tac >> rw [augmenting_path_def])
  >- (gvs [gen_bipartite_def]
      >> Cases_on ‘HD P ∈ A’
      >- (CCONTR_TAC
          >> fs [Once NOT_LT]
          >> ‘P ≠ []’ by (gvs [alternating_path_def, path_def, walk_def])
          >> ‘LENGTH P ≠ 0’ by gvs [LENGTH]
          >> ‘LENGTH P = 1’ by simp []
          >> drule $ (iffLR LENGTH_EQ_1) >> strip_tac
          >> ‘HD P = x’ by METIS_TAC [HD]
          >> ‘LAST P = x’ by METIS_TAC [LAST_CONS]
          >> gvs [] >> ASM_SET_TAC []
         )
      >> ‘∀n. n ∈ V ⇒ (n ∉ A ⇔ n ∈ B)’ by ASM_SET_TAC [DISJOINT_DEF]
      >> sg ‘HD P ∈ V ∧ LAST P ∈ V’
      >- (gvs [alternating_path_def, path_def, walk_def] >> CONJ_TAC
          >- (last_x_assum irule >> rw [HEAD_MEM])
          >> last_x_assum irule >> rw [LAST_MEM]
         )
      >> gvs []
      >> ‘LAST P ∈ A’ by ASM_SET_TAC []
      >> CCONTR_TAC
      >> fs [Once NOT_LT]
      >> ‘P ≠ []’ by (gvs [alternating_path_def, path_def, walk_def])
      >> ‘LENGTH P ≠ 0’ by gvs [LENGTH]
      >> ‘LENGTH P = 1’ by simp []
      >> drule $ (iffLR LENGTH_EQ_1) >> strip_tac
      >> ‘HD P = x’ by METIS_TAC [HD]
      >> ‘LAST P = x’ by METIS_TAC [LAST_CONS]
      >> gvs [] >> ASM_SET_TAC []
     )
  >> ‘augmenting_path G M P’ by rw [augmenting_path_def]
  >> eq_tac
  >- (disch_tac
      >> irule augmenting_path_bipartite_hd_last
      >> qexistsl_tac [‘A’, ‘G’, ‘M’] >> rw []
     )
  >> ‘gen_bipartite G B A’ by gvs [gen_bipartite_sym]
  >> qabbrev_tac ‘R = REVERSE P’
  >> ‘P ≠ []’ by (gvs [alternating_path_def, path_def, walk_def])
  >> ‘R ≠ []’ by (CCONTR_TAC >> gvs [])
  >> rw [Once $ GSYM HD_REVERSE] >> rw [GSYM LAST_REVERSE]
  >> ‘bipartite G’ by (drule gen_bipartite_bipartite >> rw [])
  >> ‘augmenting_path G M R’ by gvs [Once augmenting_path_reversible, Abbr ‘R’]
  >> drule_all augmenting_path_bipartite_hd_last >> rw []
QED


Definition edges_in_path_def:
  edges_in_path (G: fsgraph) p = {{v1; v2} |
                                    path G p ∧ list$adjacent p v1 v2 ∧
                                    adjacent G v1 v2}
End


Theorem edges_in_path_alt:
  ∀G p. edges_in_path (G: fsgraph)
                      p = {e | path G p ∧ e ∈ E ∧ ∃v1 v2. list$adjacent p v1 v2
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

Theorem edges_in_path_in_fsgedges:
  ∀G p e. path G p ∧ e ∈ edges_in_path G p ⇒ e ∈ E
Proof
  rw [edges_in_path_alt]
QED

Theorem edges_in_path_iff:
  ∀G p v. path G p ∧ 1 < LENGTH p ⇒ ((∃e. e ∈ edges_in_path G p ∧ v ∈ e) ⇔ MEM v p)
Proof
  rw [edges_in_path_alt] >> eq_tac
  >- (strip_tac
      >> drule alledges_valid >> rw []
      >> drule adjacent_MEM
      >> strip_tac
      >> Suff ‘v1 ≠ v2’
      >- (gs []
         )
      >> last_x_assum mp_tac
      >> qpat_x_assum ‘adjacent _ _ _’ mp_tac
      >> KILL_TAC
      >> rw [path_def, adjacent_EL]
      >> rw [ALL_DISTINCT_EL_IMP]
     )
  >> last_x_assum mp_tac >> rw [path_def, walk_def, MEM_EL]
  >> Cases_on ‘n = 0’
  >- (qexists_tac ‘{EL 0 p; EL 1 p}’
      >> rw [GSYM adjacent_fsg]
      >- (first_x_assum irule
          >> rw [adjacent_EL]
          >> qexists_tac ‘0’
          >> simp []
         )
      >> qexistsl_tac [‘HD p’, ‘EL 1 p’] >> simp []
      >> rw [adjacent_EL]
      >> qexists_tac ‘0’
      >> simp []
     )
  >> qexists_tac ‘{EL (PRE n) p; EL n p}’
  >> rw [GSYM adjacent_fsg]
  >- (ORW [adjacent_fsg_reversible]
      >> first_x_assum irule
      >> rw [adjacent_EL]
      >> qexists_tac ‘PRE n’
      >> simp [PRE_SUB1]
     )
  >> qexistsl_tac [‘EL (PRE n) p’, ‘EL n p’] >> simp []
  >> rw [adjacent_EL]
  >> qexists_tac ‘PRE n’
  >> simp [PRE_SUB1]
QED

Theorem edges_in_path_imp:
  ∀G p e v. path G p ∧ e ∈ edges_in_path G p ⇒ ∀v. v ∈ e ⇒ MEM v p
Proof
  rw [path_def, walk_def, edges_in_path_alt]
  >> drule alledges_valid >> rpt strip_tac
  >> ‘v1 <> v2’ by gvs [ALL_DISTINCT_EL_IMP, adjacent_EL]
  >> drule adjacent_MEM >> ASM_SET_TAC []
QED

Theorem augmenting_path_augments_matching:
  ∀(G: fsgraph) M P. bipartite G ∧ augmenting_path G M P ⇒ ∃M'. matching G M' ∧ CARD M < CARD M'
Proof
  rpt STRIP_TAC
  >> drule_all_then assume_tac augmenting_path_even_length
  >> gvs [augmenting_path_def, alternating_path_def, bipartite_alt]
  >> ‘M ⊆ E’ by gvs [matching_def]
  >> qabbrev_tac ‘M1 = M ∩ edges_in_path G P’
  >> qabbrev_tac ‘M2 = M DIFF edges_in_path G P’
  >> sg ‘M = M1 ∪ M2 ∧ DISJOINT M1 M2’
  >- (gvs [Abbr ‘M1’, Abbr ‘M2’] >> SET_TAC []
     )
  >> sg ‘{{EL n P; EL (SUC n) P} | n | ODD n ∧ SUC n < LENGTH P} = M1’
  >- (ORW [EQ_SYM_EQ]
      >> gvs [Abbr ‘M1’] >> rw [EXTENSION] >> ORW [IN_EDGE_lemma]
      >> iff_tac
      >- (rw [edges_in_path_def] >> rw []
          >> gvs [adjacent_EL]
          >> qexists_tac ‘i’ >> rw [ADD1]
         )
      >> rw []
      >- (first_x_assum drule >> rw [])
      >> rw [edges_in_path_def]
      >> qexistsl_tac [‘EL n P’, ‘EL (SUC n) P’] >> simp []
      >> STRONG_CONJ_TAC
      >- (rw [adjacent_EL] >> qexists_tac ‘n’ >> simp [ADD1])
      >> gvs [path_def, walk_def]
     )
  >> qabbrev_tac ‘M1' = {{EL n P; EL (SUC n) P} | n | EVEN n ∧ SUC n < LENGTH P}’
  >> sg ‘DISJOINT M1' M2’
  >- (‘M1' ⊆ edges_in_path G P’ suffices_by ASM_SET_TAC []
      >> simp [edges_in_path_def, SUBSET_DEF, Abbr ‘M1'’] >> rw []
      >> qexistsl_tac [‘EL n P’, ‘EL (SUC n) P’] >> simp []
      >> STRONG_CONJ_TAC
      >- (rw [adjacent_EL] >> qexists_tac ‘n’ >> simp [ADD1])
      >> gvs [path_def, walk_def]
     )
  >> sg ‘M1' ⊆ E’
  >- (gvs [path_def, walk_def] >> rw [Abbr ‘M1'’, SUBSET_DEF]
      >> ORW [GSYM adjacent_fsg]
      >> first_x_assum irule >> rw [adjacent_EL]
      >> qexists_tac ‘n’ >> simp [ADD1])
  >> ASSUME_TAC $ (Q.SPEC ‘G’ o GEN_ALL) FINITE_fsgedges
  >> ‘FINITE M’ by METIS_TAC [finite_matching]
  >> ‘FINITE M ∧ FINITE M1'’ by PROVE_TAC [SUBSET_FINITE]
  >> sg ‘FINITE M1 ∧ FINITE M2’
  >- (‘M1 ⊆ M ∧ M2 ⊆ M’ by ASM_SET_TAC []
       >> PROVE_TAC [SUBSET_FINITE]
     )
  >> qexists_tac ‘M1' ∪ M2’ >> reverse CONJ_TAC
  >- (qpat_x_assum ‘M = _ ∪ _’ (fn t => ORW [t])
      >> ‘M1 ⊆ M ∧ M2 ⊆ M’ by ASM_SET_TAC []
      >> ASSUME_TAC $ (Q.SPEC ‘G’ o GEN_ALL) FINITE_fsgedges
      >> simp [CARD_UNION_DISJOINT]
      >> qabbrev_tac ‘M1'' = {{EL n P; EL (SUC n) P} | n | 0 < n ∧ EVEN n ∧ SUC n < LENGTH P}’
      >> qabbrev_tac ‘f = (λi. {EL i P; EL (SUC i) P})’
      >> sg ‘M1' = IMAGE f {n | EVEN n ∧ SUC n < LENGTH P}’
      >- (rw [Abbr ‘M1'’, Once EXTENSION]
         )
      >> sg ‘M1'' = IMAGE f {n | 0 < n ∧ EVEN n ∧ SUC n < LENGTH P}’
      >- (rw [Abbr ‘M1''’, Once EXTENSION]
         )
      >> sg ‘M1 = IMAGE f {n | ODD n ∧ SUC n < LENGTH P}’
      >- (rw [Once EXTENSION]
         )
      >> sg ‘INJ f {(n :num) | SUC n < LENGTH P} E’
      >- (rw [INJ_DEF, Abbr ‘f’]
          >- (simp [GSYM adjacent_fsg]
              >> gvs [path_def, walk_def]
              >> last_x_assum irule >> ORW [adjacent_EL]
              >> qexists_tac ‘i’ >> PROVE_TAC [ADD1]
             )
          >> qpat_x_assum ‘path G P’ mp_tac >> NTAC 3 $ pop_assum mp_tac >> KILL_TAC
          >> rw [path_def]
          >> ‘i < LENGTH P ∧ i' < LENGTH P’ by intLib.ARITH_TAC
          (* irule $ INST_TYPE [alpha |-> “:vertex”] $ iffLR ALL_DISTINCT_EL_IMP does not work: No parse *)
          >> ‘EL i P = EL i' P’ suffices_by PROVE_TAC [EL_ALL_DISTINCT_EL_EQ]
          >> gvs [Once INSERT2_lemma, EL_ALL_DISTINCT_EL_EQ]
         )
      >> ‘∀x y. SUC x < LENGTH P ∧ SUC y < LENGTH P ⇒ f x = f y ⇒ x = y’ by gs [INJ_DEF]
      >> qabbrev_tac ‘N1 = {n | ODD n ∧ SUC n < LENGTH P}’
      >> qabbrev_tac ‘N1' = {n | EVEN n ∧ SUC n < LENGTH P}’
      >> qabbrev_tac ‘N0 = {(n :num) | SUC n < LENGTH P}’
      >> sg ‘INJ f N1 E ∧ INJ f N1' E’
      >- (‘N1 ⊆ N0 ∧ N1' ⊆ N0’ by ASM_SET_TAC []
          >> (CONJ_TAC >> irule INJ_SUBSET >> qexists_tac ‘N0’)
          >- (qexists_tac ‘E’ >> rw [])
          >> qexists_tac ‘E’ >> rw []
         )
      >> ‘FINITE N1 ∧ FINITE N1'’ by METIS_TAC [FINITE_INJ]
      >> Suff ‘CARD N1 < CARD N1'’
      >- (simp [] >> PROVE_TAC [GEN_ALL INJ_CARD_IMAGE])
      >> sg ‘CARD N1 = CARD $ IMAGE PRE N1’
      >- (irule FINITE_BIJ_CARD
          >> simp []
          >> qexists_tac ‘PRE’ >> simp [BIJ_ALT, IN_FUNSET, PULL_EXISTS, EXISTS_UNIQUE_ALT]
          >> rw []
          >> qexists_tac ‘x’ >> simp [EQ_IMP_THM, FORALL_AND_THM]
          >> qx_gen_tac ‘y’
          >> strip_tac
          >> sg ‘x ≠ 0 ∧ y ≠ 0’
          >- (rpt STRIP_TAC
              >> qpat_x_assum ‘x ∈ N1’ MP_TAC
              >> qpat_x_assum ‘y ∈ N1’ MP_TAC
              >>  qpat_x_assum ‘∀n. SUC n < LENGTH P ⇒ _’ kall_tac
              >> simp [Abbr ‘N1’]
             )
          >> intLib.ARITH_TAC
         )
      >> POP_ORW
      >> irule CARD_PSUBSET >> simp []
      >> simp [PSUBSET_DEF] >> CONJ_TAC
      >- (rw [SUBSET_DEF, Abbr ‘N1’, Abbr ‘N1'’]
          >- (qpat_x_assum ‘ODD _’ mp_tac >> KILL_TAC
              >> intLib.ARITH_TAC
             )

          >> intLib.ARITH_TAC
         )
      >> simp [EXTENSION]
      >> qexists_tac ‘LENGTH P - 2’
      >> simp [Abbr ‘N1’, Abbr ‘N1'’, EVEN_SUB]
      >> qpat_x_assum ‘∀n. SUC n < LENGTH P ⇒ _’ kall_tac
      >> simp [DECIDE ``x = PRE y <=> x = 0 /\ y = 0 \/ y = x + 1``, DISJ_IMP_THM, FORALL_AND_THM]
     )
  >> irule matching_UNION
  >> STRONG_CONJ_TAC
  >- (Suff ‘BIGUNION M1' = HD P INSERT ((LAST P) INSERT (BIGUNION M1))’
      >- (‘DISJOINT (BIGUNION M1) (BIGUNION M2)’ by gvs [matching_DISJOINT_UNION_EQ]
          >> Rewr >> simp [DISJOINT_INSERT, Abbr ‘M2’]
          >> simp [GSYM IMP_DISJ_THM]
          >> reverse $ rpt strip_tac >> gvs [unmatched_def]
         )
      >> simp [EXTENSION] >> rpt strip_tac >> reverse eq_tac
      >- (‘P ≠ []’ by gvs [path_def, walk_def]
          >> qpat_x_assum ‘_ = M1’ (fn t => simp [GSYM t])
          >> rpt strip_tac
          >- (qexists_tac ‘{EL 0 P; EL 1 P}’ >> simp [Abbr ‘M1'’]
              >> qexists_tac ‘0’ >> simp []
             )
          >- (qexists_tac ‘{EL (LENGTH P - 2) P; EL (LENGTH P - 1) P}’
              >> drule LAST_EL
              >> ORW [GSYM PRE_SUB1]
              >> rw [Abbr ‘M1'’]
              >> qexists_tac ‘LENGTH P - 2’
              >> simp [DECIDE “1 < a ⇒ PRE a = SUC (a − 2)”, EVEN_SUB]
             )
          >> Cases_on ‘x = EL n P’
          >- (qexists_tac ‘{EL (n - 1) P; EL n P}’ >> rw [Abbr ‘M1'’]
              >> qexists_tac ‘n - 1’ >> CONJ_TAC
              >- (‘SUC (n - 1) = n’ suffices_by Rewr
                  >> drule ODD_POS >> simp []
                 )
              >> ‘1 ≤ n’ by (drule ODD_POS >> simp [])
              >> rw [EVEN_SUB] >> ORW [EVEN_ODD] >> simp []
             )
          >> ‘x = EL (SUC n) P’ by gvs [] >> qpat_x_assum ‘x ≠ _’ K_TAC
          >> qexists_tac ‘{EL (SUC n) P; EL (n + 2) P}’ >> rw [Abbr ‘M1'’]
          >> qexists_tac ‘SUC n’
          >> simp [ADD1, EVEN_ADD] >> simp [EVEN_ODD]
          >> ‘1 < LENGTH P - SUC n’ suffices_by simp []
          >> ‘EVEN $ SUC n’ by (Keep_last_assum 2 >> intLib.ARITH_TAC)
          >> ‘EVEN (LENGTH P - SUC n)’ by gvs [EVEN_SUB]
          >> (Keep_last_assum 3 >> intLib.ARITH_TAC)
         )
      >> simp [Abbr ‘M1'’] >> rpt strip_tac
      >> Cases_on ‘x = HD P’
      >- (rw [])
      >> Cases_on ‘LENGTH P = 2’
      >- (simp []
          >> ‘n = 0’ by gvs []
          >> ‘x = EL (SUC n) P’ by gvs [] >> DISJ1_TAC
          >> fs [path_def, walk_def] >> drule LAST_EL >> Rewr
          >> simp []
         )
      >> ‘2 < LENGTH P’ by simp [] >> qpat_x_assum ‘_ ≠ 2’ K_TAC
      >> Cases_on ‘n = 0’
      >- (‘x = EL 1 P’ by gvs [] >> rpt DISJ2_TAC
          >> qexists_tac ‘{EL 1 P; EL 2 P}’ >> rw []
          >> qexists_tac ‘1’
          >> pop_assum mp_tac >> KILL_TAC >> simp []
         )
      >> Cases_on ‘n = LENGTH P - 2’
      >- (qpat_x_assum ‘x ∈ s’ mp_tac >> qpat_x_assum ‘s = _’ (fn t => ORW [t])
          >> simp [] >> reverse $ rpt strip_tac
          >- (pop_assum mp_tac
              >> simp [DECIDE “2 < a ⇒ SUC (a − 2) = PRE a”]
              >> disch_then K_TAC
              >> DISJ1_TAC >> irule $ GSYM LAST_EL
              >> gvs [path_def, walk_def]
             )
          >> DISJ2_TAC
          >> qexists_tac ‘{EL (LENGTH P - 3) P; EL (LENGTH P - 2) P}’ >> rw []
          >> qpat_x_assum ‘EVEN (LENGTH P)’ mp_tac >> Keep_last_assum_disch 5
          >> qexists_tac ‘LENGTH P - 3’
          >> rw [DECIDE “2 < a ⇒ a - 2 = SUC (a - 3)”]
          >> ‘ODD (LENGTH P - 2 - 1)’ suffices_by simp []
          >> rw [ODD_SUB, ODD_EVEN]
         )
      >> rpt DISJ2_TAC
      >> qpat_x_assum ‘x ∈ s’ mp_tac >> qpat_x_assum ‘s = _’ (fn t => ORW [t])
      >> simp [] >> rpt strip_tac
      >- (qexists_tac ‘{EL (n-1) P; EL n P}’ >> rw []
          >> qexists_tac ‘n - 1’ >> Keep_last_assum_disch 6
          >> simp [ODD_SUB, ODD_EVEN, ADD1]
         )
      >> qexists_tac ‘{EL (SUC n) P; EL (n+2) P}’ >> rw []
      >> qexists_tac ‘n+1’ >> Keep_last_assum_disch 6
      >> simp [EVEN_ADD, ODD_SUB, ODD_EVEN, ADD1]
     )
  >> simp [] >> reverse $ rpt strip_tac
  >- (‘M2 ⊆ M’ by gvs [] >> drule_all matching_SUBSET >> rw []
     )
  >> simp [matching_def, Abbr ‘M1'’] >> rpt strip_tac
  >> Cases_on ‘n = n'’
  >- gvs []
  >> ‘ALL_DISTINCT P’ by gvs [path_def]
  >> Keep_last_assum_disch 9
  >> ‘n < LENGTH P ∧ n' < LENGTH P’ by simp []
  >> simp [ALL_DISTINCT_EL_IMP]
  >> CCONTR_TAC >> gvs [EVEN_ODD, ODD]
QED

Theorem alternating_path_append_A:
  ∀G M A B p q. gen_bipartite G A B ∧ alternating_path G M p ∧
                HD p ∈ A ∧
                LAST p ∈ B ∧
                ~MEM q p ∧
                {q; LAST p} ∈ M
                ⇒ alternating_path G M (p ++ [q])
Proof
  rpt strip_tac >> rw [alternating_path_def] >~
  [‘matching G M’]
  >- gvs [alternating_path_def] >~
  [‘unmatched G M (HD _)’]
  >- (gvs [alternating_path_def]
      >> ‘HD (p ⧺ [q]) = HD p’ suffices_by simp []
      >> gvs [path_def, walk_def]
      >> drule_then assume_tac $ iffLR LIST_NOT_NIL
      >> POP_ORW >> simp []
     ) >~
  [‘path G (p ⧺ [q])’]
  >- (gvs [alternating_path_def, path_def, walk_def] >> rw []
      >- simp []
      >- (‘{q; LAST p} ∈ E’ by ASM_SET_TAC [matching_def]
         >> drule fsgraph_valid >> rw []
         )
      >- (pop_assum mp_tac >> simp [adjacent_EL] >> rw []
          >> Cases_on ‘i + 1 = LENGTH p’
          >- (simp [EL_LENGTH_APPEND_0]
              >> ORW [DECIDE “i = PRE (i + 1)”] >> POP_ORW
              >> simp [EL_APPEND, GSYM LAST_EL]
              >> ORW [adjacent_fsg] >> gvs [matching_def, SUBSET_DEF]
             )
          >> simp [EL_APPEND] >> last_x_assum irule
          >> simp [adjacent_EL]
          >> qexists_tac ‘i’ >> simp []
         )
      >> simp [ALL_DISTINCT_APPEND]
     )
  >> gvs [alternating_path_def]
  >> Cases_on ‘SUC n < LENGTH p’
  >- (gvs [EL_APPEND])
  >> ‘SUC n = LENGTH p’ by simp []
  >> simp [EL_APPEND]
  >> ORW [DECIDE “n = PRE (SUC n)”] >> POP_ORW
  >> gvs [path_def, walk_def] >> simp [GSYM LAST_EL]
  >> rw [PAIR_SYM_lemma]
  >> irule $ iffRL alternating_path_zigzag_parity
  >> qexistsl_tac [‘A’,‘B’,‘G’,‘M’,‘p’] >> simp [alternating_path_def, path_def, walk_def]
  >> drule LAST_EL >> METIS_TAC []
QED

Theorem alternating_path_append_B:
  ∀G M A B p q. gen_bipartite G A B ∧ alternating_path G M p ∧
                HD p ∈ A ∧
                LAST p ∈ A ∧
                ~MEM q p ∧
                {q; LAST p} ∈ E
                    ⇒ alternating_path G M (p ++ [q])
Proof
  rw [alternating_path_def, gen_bipartite_alt]
  >- (gvs [path_def, walk_def] >> rw []
      >- simp []
      >- (drule fsgraph_valid >> rw [])
      >- (pop_assum mp_tac >> simp [adjacent_EL] >> rw []
          >> Cases_on ‘i + 1 = LENGTH p’
          >- (simp [EL_LENGTH_APPEND_0]
              >> ORW [DECIDE “i = PRE (i + 1)”] >> POP_ORW
              >> simp [EL_APPEND, GSYM LAST_EL]
              >> ORW [adjacent_fsg] >> rw []
             )
          >> simp [EL_APPEND] >> last_x_assum irule
          >> simp [adjacent_EL]
          >> qexists_tac ‘i’ >> simp []
         )
      >> gvs [ALL_DISTINCT_APPEND]
     )
  >- (‘p ≠ []’ by gvs [path_def, walk_def]
      >> pop_assum mp_tac >> ORW [LIST_NOT_NIL] >> Rewr'
      >> rw []
     )
  >> Cases_on ‘n = 0’
  >- (‘p ≠ []’ by gvs [path_def, walk_def]
      >> pop_assum mp_tac >> ORW [LIST_NOT_NIL] >> Rewr' >> rw []
      >> CCONTR_TAC >> gvs [unmatched_def]
      >> first_x_assum drule >> simp []
     )
  >> ‘n < LENGTH p’ by simp []
  >> Cases_on ‘SUC n = LENGTH p’
  >- (simp [EL_APPEND1, EL_APPEND2]
      >> ‘gen_bipartite G A B ∧ alternating_path G M p ∧ SUC n ≤ LENGTH p’
        by rw [gen_bipartite_alt, alternating_path_def]
      >> drule_all alternating_path_zigzag_parity >> rw []
      >> sg ‘EL n p = LAST p’
      >- (ORW [DECIDE “n = PRE (SUC n)”]
          >> qpat_assum ‘SUC n = _’ mp_tac >> Rewr'
          >> ‘p ≠ []’ by gvs [path_def, walk_def]
          >> rw [GSYM LAST_EL]
         )
      >> simp [] >> iff_tac
      >- (rw [] >> ASM_SET_TAC [])
      >> ‘LAST p ∉ B’ by ASM_SET_TAC [] >> rw []
      >> ‘2 ≤ LENGTH p’ by simp []
      >> Suff ‘∃e. e ∈ M ∧ LAST p ∈ e ∧ e ≠ {LAST p; q}’
      >- (rpt strip_tac >> gvs [matching_def]
          >> first_x_assum drule_all >> ASM_SET_TAC []
         )
      >> qexists_tac ‘{EL (n-1) p; LAST p}’ >> simp [] >> reverse CONJ_TAC
      >- (‘EL (n - 1) p ≠ q’ suffices_by SET_TAC []
          >> ‘MEM (EL (n − 1) p) p’ by simp [EL_MEM]
          >> METIS_TAC []
         )
      >> ‘LAST p = EL n p’ by METIS_TAC [LAST_EL] >> POP_ORW
      >> ‘n = SUC (n - 1)’ by simp []
      >> ‘EL n p = EL (SUC (n-1)) p’ by METIS_TAC [] >> POP_ORW
      >> last_x_assum (irule o iffLR) >> simp []
      >> ‘~ODD n’ suffices_by simp [ODD_SUB]
      >> gs []
     )
  >> ‘SUC n < LENGTH p’ by simp []
  >> simp [EL_APPEND1]
QED


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

(* Excercise 1 *)

(* Theorem max_matching_iff_no_aug_path: *)
(*   !(G: fsgraph) M. bipartite G ⇒ (max_matching G M <=> !p. alternating_path G M p ⇒ ~augmenting_path G M p) *)
(* Proof *)
(*   cheat *)
(* QED *)

Definition perfect_matching_def:
  perfect_matching G M ⇔ matching G M ∧ V = BIGUNION M
End

Theorem perfect_matching_alt:
  ∀G M. perfect_matching G M ⇔ matching G M ∧ (∀v. v ∈ V ⇒ ∃e. e ∈ M ∧ v ∈ e)
Proof
  rw [perfect_matching_def, BIGUNION] >> iff_tac
  >- rw []
  >> rw [Once EXTENSION] >> iff_tac
  >- gvs []
  >> rpt strip_tac >> gvs [matching_def]
  >> ‘s ∈ E’ by ASM_SET_TAC [] >> drule alledges_valid >> ASM_SET_TAC []
QED

Theorem perfect_matching_def_matched_set:
  ∀G M. perfect_matching G M ⇔ matching G M ∧ matched_set G M V
Proof
  rw [matched_set_def, matched_def, perfect_matching_alt] >> PROVE_TAC []
QED

Theorem perfect_matching_bipartite_BIJ:
  ∀G A B M. gen_bipartite G A B ∧ perfect_matching G M ⇒ ∃f. BIJ f A B
Proof
  rw [perfect_matching_alt, matching_def]
  >> gvs [gen_bipartite_alt]
  >> ‘A ⊆ V’ by ASM_SET_TAC []
  >> gvs [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] >> rename [‘Edge _ ∈ M’, ‘_ = {Aend _; Bend _;}’]
  >> irule SCHROEDER_BERNSTEIN >> rw [INJ_DEF]
  >- (qexists_tac ‘Bend o Edge’ >> rw []
      >- (‘Edge x ∈ E’ by ASM_SET_TAC []
          >> first_x_assum drule >> rw []
         )
      >> ‘Edge x ∈ M ∧ Edge y ∈ M’ by ASM_SET_TAC []
      >> ‘~DISJOINT (Edge x) (Edge y)’ by ASM_SET_TAC []
      >> ‘Edge x = Edge y’ by METIS_TAC []
      >> ASM_SET_TAC []
     )
  >> qexists_tac ‘Aend o Edge’ >> rw []
  >- (‘Edge x ∈ E’ by ASM_SET_TAC []
      >> first_x_assum drule >> rw []
     )
  >> ‘Edge x ∈ M ∧ Edge y ∈ M’ by ASM_SET_TAC []
  >> ‘~DISJOINT (Edge x) (Edge y)’ by ASM_SET_TAC []
  >> ‘Edge x = Edge y’ by METIS_TAC []
  >> ASM_SET_TAC []
QED

Theorem perfect_matching_bipartite_CARD:
  ∀G A B M. gen_bipartite G A B ∧ perfect_matching G M ⇒ CARD A = CARD B
Proof
  rw [] >> drule_all_then strip_assume_tac perfect_matching_bipartite_BIJ
  >> ‘FINITE A’ suffices_by (disch_tac >> drule_all FINITE_BIJ_CARD >> rw [])
  >> PROVE_TAC [gen_bipartite_FINITE]
QED


Theorem perfect_matching_as_1factor:
  ∀G A B M. gen_bipartite G A B ∧ perfect_matching G M ⇒ ∃G'. factor 1 G' G
Proof
  rw [perfect_matching_alt] >>
  drule_all_then strip_assume_tac matching_as_subgraph >>
  rename [‘G1 ⊆ G’] >>
  qexists_tac ‘G1’ >> rw [factor_def, regular_def, degree_def] >>
  first_x_assum $ drule_then strip_assume_tac >> gvs [matching_def] >>
  irule SING_CARD_1 >> rw [SING_DEF] >>
  ASM_SET_TAC []
QED

Theorem perfect_matching_between_nodes:
  ∀G A B M. gen_bipartite G A B ∧ perfect_matching G M ⇒ matched_set G M A ∧
                                                         matched_set G M B ∧
                                                         CARD A = CARD M ∧ CARD B = CARD M
Proof
  Suff ‘∀G A B M. gen_bipartite G A B ∧
                  perfect_matching G M ⇒
                  matched_set G M A ∧ CARD A = CARD M’
  >- (rw []
      >- (last_x_assum drule_all >> rw [])
      >- (last_x_assum (mp_tac o Q.SPECL [‘G’, ‘B’, ‘A’, ‘M’]) >> rw [Once gen_bipartite_sym])
      >- (last_x_assum drule_all >> rw [])
      >> last_x_assum (mp_tac o Q.SPECL [‘G’, ‘B’, ‘A’, ‘M’]) >> rw [Once gen_bipartite_sym]
     )
  >> NTAC 5 strip_tac >> drule_all_then assume_tac perfect_matching_bipartite_CARD
  >> gs [perfect_matching_def_matched_set]
  >> ‘A ⊆ V’ by ASM_SET_TAC [gen_bipartite_def] >> drule matched_set_subset >> rw []
  >> qpat_assum ‘_ = CARD B’ (ORW o wrap o SYM)
  >> ‘matched_set G M A’ by PROVE_TAC [matched_set_subset]
  >> ‘A ⊆ A’ by simp [SUBSET_DEF] >> drule_all_then assume_tac matched_set_CARD_LE_matching_bipartite
  >> ‘CARD M ≤ CARD A’ suffices_by simp [] >> irule vertex_cover_gen_matching_card
  >> qexists_tac ‘G’ >> drule vertex_cover_bipartition >> rw []
QED


Theorem perfect_matching_cond:
  ∀G A B M. gen_bipartite G A B ∧ matching G M ∧ CARD A = CARD B ∧ CARD M = CARD A ⇒ perfect_matching G M
Proof
  rw [perfect_matching_def_matched_set]
  >> drule_all_then strip_assume_tac matching_between_nodes
  >> sg ‘Am = A ∧ Bm = B’
  >- (CONJ_TAC >> irule SUBSET_EQ_CARD >> drule_all gen_bipartite_FINITE >> PROVE_TAC [SUBSET_FINITE])
  >> gvs [] >> mp_tac $ Q.SPECL [‘G’, ‘M’, ‘A’, ‘B’] matched_set_UNION >> gvs [gen_bipartite_def]
QED


Theorem perfect_matching_iff:
  ∀G A B M. gen_bipartite G A B ∧ matching G M ⇒ (perfect_matching G M ⇔ CARD A = CARD M ∧ CARD B = CARD M)
Proof
  PROVE_TAC [perfect_matching_cond, perfect_matching_between_nodes]
QED

Theorem perfect_matching_exists_iff:
  ∀G A B M. gen_bipartite G A B ⇒ ((∃M. perfect_matching G M) ⇔ (∃M. matching G M ∧ CARD A = CARD M ∧ CARD B = CARD M))
Proof
  rw [] >> iff_tac
  >> rw [] >> qexists_tac ‘M’ >> PROVE_TAC [perfect_matching_alt, perfect_matching_iff]
QED


(* Theorem perfect_matching_exists: *)
(*   ∀G A B. gen_bipartite G A B ∧ CARD A = CARD B ∧ (∀v. v ∈ V ⇒ degree G v ≠ 0) ⇒ ∃M. perfect_matching G M *)
(* Proof *)
(*   rw [perfect_matching_def_matched_set] >> cheat *)
(* QED *)


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
  ‘x IN E /\ y IN E’ by ASM_SET_TAC [matching_def]
  >> ‘DISJOINT x y’ by METIS_TAC [matching_def] >> pop_assum MP_TAC
  >> rw [DISJOINT_DEF, INTER_DEF, GSYM MEMBER_NOT_EMPTY]
  >> Q.EXISTS_TAC term
  >> METIS_TAC [COMPONENT, genericGraphTheory.INSERT2_lemma];




(* BEGIN OF DIESTEL, CH. 2 *)

(* Konig 1931, page 37 *)
Theorem konig_matching_thm:
  !G. bipartite G ==> MAX_SET (IMAGE CARD (matching G)) = MIN_SET (IMAGE CARD (vertex_cover G))
Proof
  rw [bipartite_alt]
  >> ‘gen_bipartite G A B’ by rw [gen_bipartite_alt]
  >> Q.SPEC_THEN ‘G’ MP_TAC maximal_matching_exists >> strip_tac
  >> gvs [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]
  >> rename [‘_ = {Aend _; Bend _}’] (* This is to easily define f as well as find two ends in a bipartition. *)
  >> qabbrev_tac ‘f = \e. if ?p. alternating_path G M p /\ HD p IN A /\ LAST p = Bend e then Bend e else Aend e’
  >> qabbrev_tac ‘U = IMAGE f M’
  >> sg ‘CARD M = CARD U’
  >- (Q.SPECL_THEN [‘f’,‘M’] MP_TAC CARD_IMAGE_INJ
      >> Q.SPECL_THEN [‘G’,‘M’] MP_TAC finite_matching
      >> rw []
      >> pop_assum (irule o GSYM)
      >> (rw [Abbr ‘f’]
          >> CCONTR_TAC
          >> ‘x IN E /\ y IN E’ by ASM_SET_TAC [matching_def]
          >> ‘DISJOINT x y’ by METIS_TAC [matching_def] >> pop_assum MP_TAC
          >> rw [DISJOINT_DEF, INTER_DEF, GSYM MEMBER_NOT_EMPTY]
          )
      >- (qexists_tac ‘Bend x’ >> ASM_SET_TAC [])
      >- (qexists_tac ‘Aend x’ >> ASM_SET_TAC [])
      >- (qexists_tac ‘Bend x’ >> ASM_SET_TAC [])
      >- (qexists_tac ‘Aend x’ >> ASM_SET_TAC [])
     )
  >> sg ‘MAX_SET (IMAGE CARD (matching G)) = CARD M’
  >- (Q.SPEC_THEN ‘IMAGE CARD (matching G)’ MP_TAC MAX_SET_TEST_IFF
      >> impl_tac
      >- (CONJ_TAC
          >- (irule IMAGE_FINITE >> rw [finite_num_matching'])
          >- (rw [EXTENSION, matching_exists, IN_APP])
         )
      >> DISCH_THEN (MP_TAC o Q.SPEC ‘CARD (M: (unit + num -> bool) -> bool)’)
      >> impl_tac
      >- (rw []
          >> qexists_tac ‘M’
          >> rw [IN_APP]
       )
      >> ASM_SET_TAC [maximal_matching_exists]
     )
  (* Proof CARD U = MIN_SET (...)
     by >= /\ <= *)
  >> POP_ORW
  >> Suff ‘U ∈ vertex_cover G’
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
  >> simp [Once IN_APP] >> rw [gen_vertex_cover_def] >~
  [‘U ⊆ V’]
  >- (‘M SUBSET E’ by gvs [matching_def]
      >> pop_assum MP_TAC
      >> rw [Abbr ‘U’, SUBSET_DEF]
      >> (rw [Abbr ‘f’] >> METIS_TAC [Q.SPEC ‘G’ fsgraph_valid])
     ) >~
  [‘∃v. v ∈ U ∧ v ∈ e’]
  >> Suff ‘Aend e NOTIN U ==> Bend e IN U’
  >- ASM_SET_TAC []
  >> DISCH_TAC
  >> sg ‘!e. e IN E ==> Aend e <> Bend e’
  >- (rpt STRIP_TAC >> ASM_SET_TAC [])
  >> Cases_on ‘~matched G M (Aend e)’
  >- (Cases_on ‘~matched G M (Bend e)’
      >- (sg ‘e ∉ M ∧ matching G (e INSERT M)’
          >- (‘e INSERT M = {e} ∪ M’ by SET_TAC [] >> POP_ORW
              >> STRONG_CONJ_TAC
              >- (gvs [matched] >> ASM_SET_TAC []
                 )
              >> disch_tac
              >> irule matching_UNION
              >> gvs [matched]
              >> simp [matching_def]
              >> ASM_SET_TAC []
             )
          >> qpat_x_assum ‘!N. matching G N ==> _’ drule
          >> ‘FINITE M’ by METIS_TAC [finite_matching]
          >> simp []
         )
      >> simp [Abbr ‘f’, Abbr ‘U’] >> simp [EXISTS_OR_THM]
      >> gvs [AllCaseEqs (), FORALL_AND_THM]
      >> pop_assum MP_TAC >> rw [matched_def]
      >> qexists_tac ‘e'’ >> rw [] >> DISJ1_TAC
      >> ORW [CONJ_SYM] >> STRONG_CONJ_TAC
      >- (‘e' IN E’ by ASM_SET_TAC [matching_def]
          >> LAST_ASSUM drule
          >> STRIP_TAC
          >> ASM_SET_TAC []
         )
      >> disch_tac \\
      qexists_tac ‘[Aend e; Bend e]’ >> simp [] \\
      rw [alternating_path_def]
      >- (rw [path_def, walk_def]
          >- ASM_SET_TAC []
          >- ASM_SET_TAC []
          >> gvs [adjacent_iff, adjacent_fsg]
          >> METIS_TAC []
         )
      >- (rw [unmatched])
      >> ‘n = 0’ by simp [] >> simp []
      >> strip_tac
      >> gvs [matching_def]
      >> ‘e' ≠ {Aend e; Bend e}’ by ASM_SET_TAC [matched_def]
      >> qpat_x_assum ‘∀e1 e2. _ ⇒ DISJOINT e1 e2’ drule_all
      >> ASM_SET_TAC []
     )
  >> gvs [matched_def]
  >> ‘e' IN E’ by ASM_SET_TAC [matching_def]
  >> ‘Aend e = Aend e'’ by ASM_SET_TAC []
  >> ‘Bend e' IN U’ by ASM_SET_TAC []
  >> Cases_on ‘e = e'’
  >- rw []
  >> sg ‘e NOTIN M’
  >- (gvs [matching_def]
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
      >> pop_assum MP_TAC >> rw [Once MONO_NOT_EQ]
      >> METIS_TAC []
     )
  >> qabbrev_tac ‘b = Bend e’
  >> Cases_on ‘matched G M b’
  >- (gs [matched_def]
      >> gvs [Abbr ‘f’, Abbr ‘U’]
      >> ‘e''' = e'’ by ASM_SET_TAC [matching_def] >> rw []
      >> ‘LAST p = Bend e'’ by ASM_SET_TAC [] >> rw []
      >> ‘p <> []’ by (Keep_last_assum 7 >> gvs [alternating_path_def, path_def, walk_def])
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
      >> qexists_tac ‘pb'ab’ >> rpt (reverse CONJ_TAC) >~
      [‘LAST pb'ab = Bend e''’]
      >- (sg ‘LAST pb'ab = b’
          >- METIS_TAC [LAST_CONS, Abbr ‘pb'ab’, LAST_APPEND_NOT_NIL]
          >> pop_assum (fn t => ONCE_REWRITE_TAC [t])
          >> ASM_SET_TAC [matching_def]
         ) >~
      [‘HD pb'ab ∈ A’]
      >- (‘HD pb'ab = HD p’ suffices_by rw []
          >> ‘?x xs. p = x::xs’ by (Keep_last_assum 6 >> METIS_TAC [LIST_NOT_NIL])
          >> rw [Abbr ‘pb'ab’]
         )
      >> rw [alternating_path_def] >~(* 3 *)
      [‘unmatched G M (HD pb'ab)’]
      >- (‘HD pb'ab = HD p’ by (simp [Abbr ‘pb'ab’] >> Cases_on ‘p’ >> gvs [])
          >> METIS_TAC [alternating_path_def]
         ) >~
      [‘path G pb'ab’]
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
      >- (drule LAST_EL_LENGTH_lemma >> rw []
          >> ‘EL n pb = EL n p’ suffices_by gvs [unmatched]
          >> irule is_prefix_el >> simp []
         )
      >> ‘n ≠ 0’ suffices_by simp [alternating_path_def, path_def, walk_def]
      >> CCONTR_TAC >> gs []
      >> ASM_SET_TAC []         (* Bend e = HD p ∧ HD p ∈ A, contradiction *)
     )
  >> Q.ABBREV_TAC ‘pb'ab = p ++ [a] ++ [b]’
  >> Q.EXISTS_TAC ‘pb'ab’
  >> reverse $ rw [augmenting_path_def, unmatched, Abbr ‘pb'ab’]
  >> irule alternating_path_append_B >> rw []
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
  >- (irule alternating_path_append_A >> rw []
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
  >> ‘p ≠ []’ by gvs [alternating_path_def, path_def, walk_def]
  >> drule_then ASSUME_TAC $ iffLR LIST_NOT_NIL
  >> POP_ORW >> rw [HD]
QED



(* Theorem minimal_vertex_cover_exists: *)
(*   !(G: fsgraph). bipartite G ⇒ ?U. vertex_cover G U /\ CARD U = MIN_SET (IMAGE CARD (vertex_cover G)) *)
(* Proof *)
(*   (* By Above *) *)
(*   rw [] >> drule konig_matching_thm >> rw [] *)
(*   >> MP_TAC $ Q.SPEC ‘G’ max_matching_exists >> rw [max_matching_def] *)
(*   >> cheat *)
(* QED *)


Theorem marriage_thm:
  !(G: fsgraph) A B. gen_bipartite G A B ==>
                     ((?M. matching G M /\ matched_set G M A) <=>
                      !(S :vertex set). S SUBSET A ==> CARD S ≤ CARD (N S))
Proof
  rw []
  >> ‘bipartite G’ by METIS_TAC [bipartite_gen_bipartite]
  >> iff_tac
  >- (gs [gen_bipartite_def] >> rw [neighbour_def]
      >> drule matching_as_subgraph >> rpt STRIP_TAC
      >> ‘S' ⊆ V’ by ASM_SET_TAC []
      >> ‘matched_set G M S'’ by (irule matched_set_subset >> qexists_tac ‘A’ >> rw [])
      >> drule_all matched_set_inj_f_neighbour
      >> sg ‘FINITE $ N S'’
      >- (‘FINITE S'’ by (irule SUBSET_FINITE >> qexists_tac ‘V’ >> rw [FINITE_nodes])
          >> rw [neighbour_set, neighbour_def, GSPEC_AND]
          >> ‘FINITE V’ by rw [FINITE_nodes] >> simp []
         )
      >> rw [] >> drule INJ_CARD >> rw []
     )
  >> gvs [gen_bipartite_alt]
  >> ‘gen_bipartite G A B’ by rw [gen_bipartite_alt]
  >> gvs [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]
  >> rename [‘_ = {Aend _; Bend _}’]
  >> ‘FINITE V’ by PROVE_TAC [FINITE_nodes]
  >> drule konig_matching_thm >> rw []
  >> ASSUME_TAC $ SPEC “(G :fsgraph)” max_matching_exists >> gvs []
  >> qexists_tac ‘M’
  >> fs [max_matching_def] >> gvs []
  >> rw [matched_set_def, matched]
  >> sg ‘∀a. a ∈ A ⇒ ∃b. b ∈ B ∧ {a; b} ∈ E’
  >- (rpt strip_tac
      >> Suff ‘0 < CARD (neighbour G a)’
      >- (disch_tac
          >> ‘a ∈ V’ by ASM_SET_TAC []
          >> drule_then strip_assume_tac neighbour_FINITE
          >> drule_then strip_assume_tac CARD_EQ_0
          >> sg ‘neighbour G a ≠ ∅’
          >- (CCONTR_TAC >> gvs []
             )
          >> ‘∃b. b ∈ neighbour G a’ by ASM_SET_TAC []
          >> qexists_tac ‘b’ >> gvs [neighbour_def]
          >> last_x_assum $ drule_then assume_tac
          >> ‘a = Aend e ∧ b = Bend e’ by ASM_SET_TAC []
          >> NTAC 2 POP_ORW >> PROVE_TAC []
          )
      >- (qpat_x_assum ‘∀S. S ⊆ A ⇒ _’ (mp_tac o Q.SPEC ‘{a}’)
          >> simp [neighbour_set, SUBSET_DEF]
         )
     )
  >> Suff ‘MIN_SET (IMAGE CARD (vertex_cover G)) = CARD A’
  >- (qpat_x_assum ‘CARD M = _’ (fn t => ORW [GSYM t]) >> disch_tac
      >> drule_all matching_between_nodes >> disch_then strip_assume_tac
      >> sg ‘Am = A’
      >- (irule SUBSET_EQ_CARD >> simp []
          >> ‘FINITE V’ by simp [FINITE_nodes]
          >> ‘A ⊆ V’ by ASM_SET_TAC []
          >> drule SUBSET_FINITE >> ASM_SET_TAC []
         )
      >> fs [matched_set_def, matched_def]
      >> PROVE_TAC []
     )
  >> ‘CARD A ≤ CARD (N A)’ by ASM_SET_TAC []
  >> sg ‘CARD (N A) ≤ CARD B’
  >- (‘FINITE B’ by (irule SUBSET_FINITE_I >> qexists_tac ‘V’ >> rw [] >> ASM_SET_TAC [])
      >> ‘N A ⊆ B’ suffices_by simp [CARD_SUBSET]
      >> ‘A ⊆ V’ by ASM_SET_TAC []
      >> rw [neighbour_set]
      >> simp [SUBSET_DEF, IN_BIGUNION_IMAGE]
      >> gen_tac >> disch_then $ qx_choose_then ‘y’ strip_assume_tac
      >> ‘y ∈ V’ by ASM_SET_TAC []
      >> ‘gen_bipartite G A B’ by rw [gen_bipartite_alt]
      >> drule_all neighbour_bipartite
      >> rw [SUBSET_DEF]
     )
  >> sg ‘vertex_cover G A’
  >- (‘gen_bipartite G A B’ by rw [gen_bipartite_def]
      >> drule vertex_cover_bipartition >> rw []
     )
  >> qmatch_abbrev_tac ‘MIN_SET s = x’
  >> Know ‘MIN_SET s = x ⇔ ∀y. y ∈ s ⇒ x ≤ y’
  >- (irule MIN_SET_TEST_IFF
      >> CONJ_TAC
      >- (rw [Abbr ‘s’, Once EXTENSION, NOT_IN_EMPTY, IN_APP]
          >> qexists_tac ‘A’ >> art []
         )
      >> rw [Abbr ‘s’, Abbr ‘x’, IN_APP]
     )
  >> Rewr' >> rw [Abbr ‘s’, Abbr ‘x’, IN_APP]
  >> rename [‘CARD A ≤ CARD U’]
  >> Cases_on ‘A = U’
  >- (rw [])
  >> CCONTR_TAC >> gs [NOT_LE]
  >> Cases_on ‘U ⊆ A’
  >- (‘U ⊂ A’ by simp [PSUBSET_DEF]
      >> gvs [PSUBSET_MEMBER, SUBSET_DEF, gen_vertex_cover_def]
      >> qpat_x_assum ‘∀a. a ∈ A ⇒ ∃b. _’ drule
      >> rpt strip_tac
      >> qpat_x_assum ‘∀e. e ∈ E ⇒ ∃v. v ∈ U ∧ v ∈ e’ drule
      >> ASM_SET_TAC []
     )
  >> ‘U ⊆ V’ by ASM_SET_TAC [gen_vertex_cover_def]
  >> ‘FINITE V’ by simp [FINITE_nodes]
  >> ‘FINITE U’ by METIS_TAC [SUBSET_FINITE]
  >> qabbrev_tac ‘Ua = U ∩ A’
  >> qabbrev_tac ‘Ub = U ∩ B’
  >> ‘FINITE Ua ∧ FINITE Ub’ by METIS_TAC [INTER_FINITE]
  >> sg ‘DISJOINT Ua Ub ∧ Ua ⊆ A ∧ Ub ⊆ B ∧ Ua ∪ Ub = U’
  >- (gs [Abbr ‘Ua’, Abbr ‘Ub’] >> ASM_SET_TAC []
     )
  >> sg ‘Ub ≠ ∅’
  >- (CCONTR_TAC >> gvs []
     )
  >> ‘U DIFF Ua = Ub’ by ASM_SET_TAC []
  >> qabbrev_tac ‘Ea = {e | e ∈ E ∧ Aend e ∈ Ua}’
  >> sg ‘gen_vertex_cover V Ea Ua’
  >- (rw [gen_vertex_cover_def, Abbr ‘Ea’]
      >- ASM_SET_TAC []
      >> qexists_tac ‘Aend e’
      >> qpat_x_assum ‘∀e. e ∈ E ⇒ _’ drule >> ASM_SET_TAC []
     )
  >> sg ‘gen_vertex_cover V (E DIFF Ea) Ub’
  >- (rw [gen_vertex_cover_def, Abbr ‘Ea’, Abbr ‘Ub’]
      >- ASM_SET_TAC []
      >> qexists_tac ‘Bend e’
      >> qpat_assum ‘∀e. e ∈ E ⇒ _’ drule
      >> strip_tac >> reverse CONJ_TAC
      >- ASM_SET_TAC []
      >> simp [] >> gs [gen_vertex_cover_def]
      >> ‘Aend e ∉ U’ by ASM_SET_TAC []
      >> pop_assum mp_tac
      >> last_assum drule >> ASM_SET_TAC []
     )
  >> sg ‘∀e. e ∈ E DIFF Ea ⇒ Aend e ∉ Ua ∧ Bend e ∈ Ub’
  >- (simp [Abbr ‘Ub’, Abbr ‘Ua’, gen_vertex_cover_def] >> gvs [gen_vertex_cover_def]
      >> NTAC 2 strip_tac >> first_x_assum drule_all
      >> strip_tac >> ORW [CONJ_SYM] >> STRONG_CONJ_TAC
      >- (first_x_assum drule_all >> rw []
          >> ‘Bend e = v'’ suffices_by simp []
          >> last_x_assum drule >> ASM_SET_TAC []
         )
      >> gvs [Abbr ‘Ea’]
     )
  >> qabbrev_tac ‘Ua' = A DIFF Ua’
  >> sg ‘Ua' ≠ ∅’
  >- (simp [Abbr ‘Ua'’]
      >> ‘Ua ≠ A’ suffices_by ASM_SET_TAC []
      >> CCONTR_TAC
      >> ‘FINITE A’ by ASM_SET_TAC [INTER_FINITE]
      >> gvs [Abbr ‘Ua’]
      >> ‘CARD (U ∩ A) = CARD A’ by gvs []
      >> ‘CARD (U ∩ A) ≤ CARD U’ by METIS_TAC [CARD_INTER_LESS_EQ]
      >> gvs []
     )
  >> ‘Ua' ⊆ A’ by simp [Abbr ‘Ua'’]
  >> qpat_assum ‘∀S. S ⊆ A ⇒ _’ $ drule_then assume_tac
  >> sg ‘CARD (N Ua') ≤ CARD Ub’
  >- (irule CARD_SUBSET
      >> ‘Ua' ⊆ V’ by ASM_SET_TAC []
      >> rw [SUBSET_DEF, neighbour_set_def, Abbr ‘Ua'’]
      >- (‘v'' = Aend e ∧ x = Bend e’ by ASM_SET_TAC [] \\
          fs [] >> NTAC 2 (pop_assum K_TAC)
          >> ASM_SET_TAC [gen_vertex_cover_def]
         )
      >> ASM_SET_TAC []
     )
  >> ‘CARD Ua' ≤ CARD Ub’ by simp [Abbr ‘Ua'’]
  >> sg ‘CARD A ≤ CARD U’
  >- (qpat_x_assum ‘CARD U < CARD A’ K_TAC
      >> ‘A = Ua' ∪ Ua’ by ASM_SET_TAC [] >> POP_ORW
      >> qpat_x_assum ‘_ ∪ _ = U’ (fn t => ORW [GSYM t])
      >> ‘DISJOINT Ua' Ua’ by ASM_SET_TAC []
      >> sg ‘FINITE Ua'’
      >- (qunabbrev_tac ‘Ua'’
          >> irule FINITE_DIFF
          >> ‘A ⊆ V’ by ASM_SET_TAC []
          >> METIS_TAC [SUBSET_FINITE]
         )
      >> simp [CARD_UNION_DISJOINT]
     )
  >> gvs []
QED

Theorem regular_bipartition_CARD_EQ:
  ∀G A B k. gen_bipartite G A B ∧ 1 ≤ k ∧ regular k G ⇒ CARD A = CARD B
Proof
  rw [gen_bipartite_alt, regular_def]
  >> ASSUME_TAC $ Q.SPEC ‘G’ sumdegrees
  >> qabbrev_tac ‘deg = (degree G)’
  >> ‘(∀v. v ∈ A ⇒ deg v = k) ∧ (∀v. v ∈ B ⇒ deg v = k)’ by ASM_SET_TAC []
  >> ‘FINITE V’ by simp [FINITE_nodes]
  >> ‘FINITE E’ by simp [FINITE_fsgedges]
  >> ‘A ⊆ V ∧ B ⊆ V’ by ASM_SET_TAC []
  >> ‘FINITE A ∧ FINITE B’ by PROVE_TAC [SUBSET_FINITE]
  >> qabbrev_tac ‘f =  λv. {e | e ∈ E ∧ v ∈ e}’
  >> qabbrev_tac ‘E1 = BIGUNION (IMAGE f A)’
  >> Suff ‘∑ deg A = fsgsize G’
  >- (drule_all_then strip_assume_tac SUM_IMAGE_DISJOINT >> gvs []
      >> disch_tac
      >> ‘∑ deg B = fsgsize G’ by simp []
      >> rev_drule_all SIGMA_CONSTANT
      >> qpat_x_assum ‘∀v. v ∈ A ⇒ _’ K_TAC
      >> rev_drule_all SIGMA_CONSTANT
      >> simp []
     )
  >> sg ‘FINITE E1’
  >- (rw [Abbr ‘E1’, BIGUNION, Abbr ‘f’]
      >> irule SUBSET_FINITE_I >> qexists_tac ‘E’ >> simp [SUBSET_DEF]
     )
  >> qpat_x_assum ‘∀v. v ∈ B ⇒ _’ K_TAC >> drule_all SIGMA_CONSTANT >> Rewr'
  >> sg ‘CARD E1 = k * CARD A’
  >- (ORW [MULT_SYM]
      >> sg ‘CARD (IMAGE f A) = CARD A’
      >- (irule INJ_CARD_IMAGE >> simp []
          >> qexists_tac ‘IMAGE f A’ >> rw [INJ_DEF, IN_IMAGE]
          >- (qexists_tac ‘x’ >> rw []
             )
          >> gvs [Abbr ‘f’] >> pop_assum mp_tac >> rw [Once EXTENSION]
          >> gvs [Abbr ‘deg’, degree_def]
          >> ‘k ≠ 0’ by rw []
          >> ‘FINITE E’ by simp [FINITE_fsgedges]
          >> sg ‘∀v. FINITE {e | e ∈ E ∧ v ∈ e}’
          >- (strip_tac >> irule SUBSET_FINITE_I
              >> qexists_tac ‘E’ >> rw [SUBSET_DEF]
             )
          >> ‘∀v. v ∈ V ⇒ 0 < CARD {e | e ∈ E ∧ v ∈ e}’ by simp []
          >> ‘∀v. v ∈ V ⇒ {e | e ∈ E ∧ v ∈ e} ≠ ∅’ by METIS_TAC [CARD_EQ_0]
          >> fs [GSYM MEMBER_NOT_EMPTY]
          >> pop_assum mp_tac
          >> simp [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] >> rpt strip_tac
          >> ‘x ∈ V’ by ASM_SET_TAC []
          >> ‘f x ∈ E ∧ x ∈ f x’ by rw []
          >> ‘y ∈ f x’ by PROVE_TAC []
          >> ‘x ∈ A ∧ y ∈ A’ by ASM_SET_TAC []
          >> qpat_x_assum ‘∀e. e ∈ E ⇒ _’ drule >> strip_tac >> gvs [] >> ASM_SET_TAC []
         )
      >> pop_assum (ORW o wrap o SYM) >> simp [Abbr ‘E1’] >> ORW [MULT_SYM]
      >> irule CARD_BIGUNION_SAME_SIZED_SETS >> reverse CONJ_TAC
      >- (reverse CONJ_TAC
          >- (irule IMAGE_FINITE >> art []
             )
          >> simp [Abbr ‘f’] >> NTAC 2 strip_tac >> STRONG_CONJ_TAC
          >- (‘e ⊆ E’ by ASM_SET_TAC [] >> PROVE_TAC [SUBSET_FINITE]
             )
          >> ‘v ∈ V’ by gvs [SUBSET_DEF] >> first_x_assum drule
          >> gvs [Abbr ‘deg’, degree_def]
         )
      >> rw [Abbr ‘f’] >> rw [DISJOINT_ALT]
      >> ASM_SET_TAC []
     )
  >> pop_assum (ORW o wrap o SYM) >> simp [fsgsize_def]
  >> ‘E1 = E’ suffices_by simp []
  >> simp [Abbr ‘E1’, Abbr ‘f’, PULL_EXISTS, Once EXTENSION] >> ASM_SET_TAC []
QED


Theorem bipartite_k_regular_1_factor:
  ∀G k. bipartite G ∧ 1 ≤ k ∧ regular k G ⇒ ∃G'. factor 1 G' G
Proof
  rpt strip_tac >> gvs [bipartite_gen_bipartite]
  >> drule_all_then assume_tac regular_bipartition_CARD_EQ
  >> Suff ‘∃M. matching G M ∧ matched_set G M A’
  >- (rpt strip_tac >> ‘vertex_cover G A’ by (drule vertex_cover_bipartition >> rw [])
      >> ‘A ⊆ A’ by simp [SUBSET_DEF] >> drule_all matched_set_CARD_LE_matching_bipartite
      >> drule_all vertex_cover_gen_matching_card >> rw [] >> drule_all $ iffRL EQ_LESS_EQ
      >> NTAC 2 (pop_assum K_TAC) >> rw [] >> ‘CARD M = CARD A’ by gvs []
      >> drule_all_then strip_assume_tac perfect_matching_cond
      >> irule perfect_matching_as_1factor >> PROVE_TAC []
     )
  >> drule marriage_thm >> Rewr'
  >> drule gen_bipartite_FINITE >> gvs [regular_def, gen_bipartite_alt] >> rpt strip_tac
  >> ‘∀v. v ∈ S' ⇒ degree G v = k’ by ASM_SET_TAC []
  >> ‘FINITE S'’ by PROVE_TAC [SUBSET_FINITE] >> drule_all_then assume_tac SIGMA_CONSTANT
  >> sg ‘N S' ⊆ V’
  >- (‘S' ⊆ V’ by ASM_SET_TAC [] >> rw [neighbour_set_def]
      >> ASM_SET_TAC []
     )
  >> ‘FINITE V’ by simp [FINITE_nodes] >> ‘FINITE (N S')’ by PROVE_TAC [SUBSET_FINITE]
  >> ‘FINITE E’ by simp [FINITE_fsgedges]
  (* >> ‘ ∀v. v ∈ (N S') ⇒ degree G v = k’ by ASM_SET_TAC [] *)
  (* >>  drule_all_then assume_tac SIGMA_CONSTANT *)
  >> ‘k * CARD S' ≤ k * CARD (N S')’ suffices_by simp []
  >> qabbrev_tac ‘f =  λv. {e | e ∈ E ∧ v ∈ e}’
  >> qabbrev_tac ‘E1 = BIGUNION (IMAGE f S')’
  >> qabbrev_tac  ‘E2 = BIGUNION (IMAGE f (N S'))’
  >> sg ‘CARD E1 = k * CARD S'’
  >- (rw [Abbr ‘E1’] >> ORW [MULT_SYM]
      >> sg ‘CARD S' = CARD (IMAGE f S')’
      >- (ORW [EQ_SYM_EQ] >> irule INJ_CARD_IMAGE >> simp []
          >> qexists_tac ‘IMAGE f S'’ >> rw [INJ_DEF, IN_IMAGE]
          >- (qexists_tac ‘x’ >> rw []
             )
          >> gvs [Abbr ‘f’] >> pop_assum mp_tac >> rw [Once EXTENSION]
          >> gvs [degree_def]
          >> ‘k ≠ 0’ by rw []
          >> ‘FINITE E’ by simp [FINITE_fsgedges]
          >> sg ‘∀v. FINITE {e | e ∈ E ∧ v ∈ e}’
          >- (strip_tac
              >> ‘{e | e ∈ E ∧ v ∈ e} ⊆ E’ by SET_TAC []
              >> PROVE_TAC [SUBSET_FINITE]
             )
          >> ‘∀v. v ∈ V ⇒ 0 < CARD {e | e ∈ E ∧ v ∈ e}’ by simp []
          >> ‘∀v. v ∈ V ⇒ {e | e ∈ E ∧ v ∈ e} ≠ ∅’ by METIS_TAC [CARD_EQ_0]
          >> fs [GSYM MEMBER_NOT_EMPTY]
          >> pop_assum mp_tac >> simp [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] >> rpt strip_tac
          >> ‘x ∈ V’ by ASM_SET_TAC []
          >> ‘f x ∈ E ∧ x ∈ f x’ by rw []
          >> ‘y ∈ f x’ by PROVE_TAC []
          >> ‘x ∈ A ∧ y ∈ A’ by ASM_SET_TAC []
          >> qpat_x_assum ‘∀e. e ∈ E ⇒ _’ drule >> strip_tac >> gvs [] >> ASM_SET_TAC []
         )
      >> POP_ORW
      >> irule CARD_BIGUNION_SAME_SIZED_SETS >> reverse CONJ_TAC
      >- (reverse CONJ_TAC
          >- (irule IMAGE_FINITE >> art []
             )
          >> simp [Abbr ‘f’] >> NTAC 2 strip_tac >> STRONG_CONJ_TAC
          >- (‘e ⊆ E’ by ASM_SET_TAC [] >> PROVE_TAC [SUBSET_FINITE]
             )
          >> first_x_assum drule >> simp [degree_def]
         )
      >> rw [Abbr ‘f’] >> rw [DISJOINT_ALT]
      >> ASM_SET_TAC []
     )
  >> pop_assum (ORW o wrap o SYM)
  >> sg ‘N S' ⊆ B’
  >- (simp [neighbour_set, SUBSET_DEF] >> rpt strip_tac
      >> ‘x' ∈ V ∧ x' ∈ A’ by ASM_SET_TAC [] \\
      ‘gen_bipartite G A B’ by rw [gen_bipartite_alt]
      >> drule_all neighbour_bipartite >> ASM_SET_TAC []
     )
  >> sg ‘CARD E2 = k * CARD (N S')’
  >- (rw [Abbr ‘E2’] >> ORW [MULT_SYM]
      >> sg ‘CARD (N S') = CARD (IMAGE f (N S'))’
      >- (ORW [EQ_SYM_EQ] >> irule INJ_CARD_IMAGE >> simp []
          >> qexists_tac ‘IMAGE f (N S')’ >> rw [INJ_DEF, IN_IMAGE]
          >- (qexists_tac ‘x’ >> rw []
             )
          >> gs [Abbr ‘f’, degree_def] >> pop_assum mp_tac >> rw [Once EXTENSION]
          >> ‘FINITE E’ by simp [FINITE_fsgedges]
          >> sg ‘∀v. v ∈ V ⇒ ∃e. e ∈ E ∧ v ∈ e’
          >- (‘∀v. v ∈ V ⇒ {e | e ∈ E ∧ v ∈ e} ≠ ∅’
                suffices_by (disch_tac >> fs [GSYM MEMBER_NOT_EMPTY])
              >> ‘∀v. v ∈ V ⇒ CARD {e | e ∈ E ∧ v ∈ e} ≠ 0’ by simp []
              >> sg ‘∀v. FINITE {e | e ∈ E ∧ v ∈ e}’
              >- (strip_tac
                  >> ‘{e | e ∈ E ∧ v ∈ e} ⊆ E’ by SET_TAC [] >> PROVE_TAC [SUBSET_FINITE]
                 )
              >> METIS_TAC [CARD_EQ_0]
             )
          >> pop_assum mp_tac >> simp [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] >> rpt strip_tac
          >> ‘x ∈ V’ by ASM_SET_TAC []
          >> ‘f x ∈ E ∧ x ∈ f x’ by rw []
          >> ‘y ∈ f x’ by PROVE_TAC []
          >> ‘x ∈ B ∧ y ∈ B’ by ASM_SET_TAC []
          >> qpat_x_assum ‘∀e. e ∈ E ⇒ _’ drule >> strip_tac >> gvs [] >> ASM_SET_TAC []
         )
      >> POP_ORW >> irule CARD_BIGUNION_SAME_SIZED_SETS >> reverse CONJ_TAC
      >- (reverse CONJ_TAC
          >- (irule IMAGE_FINITE >> art []
             )
          >> simp [Abbr ‘f’] >> NTAC 2 strip_tac >> STRONG_CONJ_TAC
          >- (‘e ⊆ E’ by ASM_SET_TAC [] >> PROVE_TAC [SUBSET_FINITE]
             )
          >> ‘v ∈ V’ by gvs [SUBSET_DEF] >> first_x_assum drule >> simp [degree_def]
         )
      >> rw [Abbr ‘f’] >> rw [DISJOINT_ALT]
      >> ASM_SET_TAC []
      >> last_x_assum drule >> gvs []
     )
  >> pop_assum (ORW o wrap o SYM)
  >> Suff ‘E1 ⊆ E2’
  >- (disch_tac >> irule CARD_SUBSET >> rw [Abbr ‘E2’, Abbr ‘f’]
      >> ‘FINITE E’ by simp [FINITE_fsgedges] >> irule SUBSET_FINITE
      >> qexists_tac ‘E’ >> ASM_SET_TAC []
     )
  >> rw [Abbr ‘E1’, Abbr ‘E2’, Abbr ‘f’, BIGUNION_IMAGE] >> rw [SUBSET_DEF]
  >> ‘S' ⊆ V’ by ASM_SET_TAC []
  >> qexists_tac ‘paired_v x v’
  >> simp [paired_v_IN, neighbour_set, BIGUNION_IMAGE]
  >> ORW [CONJ_SYM] >> STRONG_CONJ_TAC
  >- (irule paired_v_IN >> qexists_tac ‘G’ >> art [])
  >> strip_tac >> qexists_tac ‘v’ >> art []
  >> irule paired_v_in_neighbour >> qexists_tac ‘x’ >> art []
QED

Definition stable_matching_def:
  stable_matching G R M ⇔ matching G M ∧ preference G R ∧
                          ∀v1 v2. {v1; v2} ∈ E DIFF M ==>
                                       (∃v3. {v1; v3} ∈ M ∧ (v2, v3) ∈ (R v1)) ∨
                                       (∃v3. {v3; v2} ∈ M ∧ (v1, v3) ∈ (R v2))
End


Theorem stable_matching_def_bipartite:
  ∀G A B R M. gen_bipartite G A B ⇒
              (stable_matching G R M ⇔ matching G M ∧ preference G R ∧
                                       ∀a b. a ∈ A ∧ {a; b} ∈ E DIFF M ==>
                                                             (∃b'. {a; b'} ∈ M ∧ (b, b') ∈ (R a)) ∨
                                                             (∃a'. {a'; b} ∈ M ∧ (a, a') ∈ (R b))
              )
Proof
  rw [gen_bipartite_def, stable_matching_def] >> iff_tac >> rw []
  >> last_x_assum (drule_then strip_assume_tac)
  >- (first_x_assum drule_all >> rw []
  )
  >> ‘{v2; v1} ∈ E ∧ {v2; v1} ∉ M’ by rw [PAIR_SYM_lemma]
  >> first_x_assum dxrule_all >> rw []
  >- (disj2_tac >> qexists_tac ‘b'’ >> rw [Once PAIR_SYM_lemma]
     )
  >> disj1_tac >> qexists_tac ‘a'’ >> rw [Once PAIR_SYM_lemma]
QED


(* Given a stable matching, no edges in E have both ends unmatched *)
(* Theorem stable_matching_edges_ends_matched: *)
(*   ∀G R M. stable_matching G R M ⇒ ∀v1 v2. {v1; v2} ∈ E ⇒ matched G M v1 *)
(* Proof *)
(*   rw [stable_matching_def, matched_def] *)
(*   >> Cases_on ‘{v1; v2} ∈ M’ *)
(*   >- (qexists_tac ‘{v1; v2}’ >> simp [] *)
(*      ) *)
(*   >> first_x_assum dxrule >> rw [] *)
(*   >> qexists_tac ‘{v3; v2}’ >> simp [] *)
(* QED *)

(* Theorem stable_matching_edges_ends_matched_alt: *)
(*   ∀G R M e. stable_matching G R M ∧ e ∈ E ⇒ ∃v. v ∈ e ∧ matched G M v *)
(* Proof *)
(*   rw [] >> drule_then strip_assume_tac alledges_valid >> gvs [] *)
(*   >> drule_all stable_matching_edges_ends_matched *)
(*   >> disch_tac >> qexists_tac ‘a’ >> simp [] *)
(* QED *)


(* M better than M'; {v1; v2} ∈ M ∧ {v1; v3} ∈ M' implies v2 >= v3 *)
Definition better_matching_def:
  better_matching G A B R M' M ⇔ gen_bipartite G A B ∧ matching G M ∧ matching G M' ∧ M ≠ M' ∧
                                 ∀v1 v2 v3. {v1; v2} ∈ M ∧ {v1; v3} ∈ M' ⇒ (v3, v2) ∈ (R v1)
End


Theorem fsg_ind = fsg_edge_induction |> CONV_RULE SWAP_FORALL_CONV;


Definition gale_shapley_def:
  gale_shapley (G :fsgraph) A B R =
  let acc = λm a b. a ∈ A ∧ b ∈ B ∧
                    {a; b} ∈ E ∧
                        ∀a'. a' ∈ A ∧ {a'; b} ∈ m ⇒ (a', a) ∈ (R b);
      P = λes m.
            {a | a ∈ A ∧ a ∉ BIGUNION m ∧ ∃b. acc m a b ∧ {a; b} ∈ es};
      Amax = λes m a.
               CHOICE (maximal_elements ({b | acc m a b ∧ {a; b} ∈ es}) (R a));
      Q = λ(es :edge set, m).
            es ⊆ E DIFF m ∧ P es m ≠ ∅;
      h = λ(es :edge set, m :edge set).
            let a = CHOICE (P es m);
                b = Amax es m a
            in
              (es DELETE {a; b},
               ({a; b} INSERT m) DIFF {e | e ∈ m ∧ b ∈ e}
              )
  in
      SND $ WHILE Q h (E, ∅)
End


Theorem stable_marriage_thm:
  ∀G R. bipartite G ∧ preference G R ⇒ ∃M. stable_matching G R M
Proof
  rw [] >> Cases_on ‘E = ∅’
  >- rw [stable_matching_def, matching_exists]
  >> gvs [bipartite_alt, EXT_SKOLEM_THM] >> rename [‘_ = {Aend _; Bend _}’] >> gvs []
  >> ‘∀e. e ∈ E ⇒ ∃n1 n2. e = {n1; n2} ∧ n1 ∈ A ∧ n2 ∈ B’ by METIS_TAC []
  >> ‘gen_bipartite G A B’ by rw [gen_bipartite_alt] >> gvs [gen_bipartite_def]
  (* Definition of 'a is acceptable by b WRT m' *)
  >> qabbrev_tac ‘acc = λm a b. a ∈ A ∧ b ∈ B ∧
                                {a; b} ∈ E ∧
                                    ∀a'. a' ∈ A ∧ {a'; b} ∈ m ⇒ (a', a) ∈ (R b)’
  >> sg ‘∀m a b. matching G m ∧ a ∈ A ∧ b ∈ B ∧ {a; b} ∈ m ⇒ acc m a b’
  >- (rw [Abbr ‘acc’, matching_def, SUBSET_DEF]
      >> ‘a ∈ V ∧ b ∈ V ∧ {a; b} ∈ E’ by ASM_SET_TAC []
      >> sg ‘a' = a’
      >- (CCONTR_TAC >> ‘{a; b} ≠ {a'; b}’ by (pop_assum mp_tac >> SET_TAC [])
          >> first_x_assum drule_all >> SET_TAC []
         )
      >> ‘a ∈ neighbour G b’ by rw [neighbour_iff_inedge, PAIR_SYM_lemma] >> gvs [preference_def]
      >> last_x_assum drule >> rw [linear_order_def] >> PROVE_TAC []
     )
  >> sg ‘∀m m' a b. matching G m ∧ m' ⊆ m ⇒ acc m a b ⇒ acc m' a b’
  >- (rw [] >> ‘matching G m'’ by (irule matching_SUBSET >> qexists_tac ‘m’ >> art [])
      >> qpat_x_assum ‘acc _ _ _’ mp_tac >> simp [Abbr ‘acc’] >> rw [] >> fs []
      >> Cases_on ‘{a; b} ∈ m’
      >- (first_x_assum irule >> art []
          >> ‘a' = a’ suffices_by gvs []
          >> CCONTR_TAC >> ‘{a; b} ≠ {a'; b}’ by (pop_assum mp_tac >> SET_TAC [])
          >> ‘{a'; b} ∈ m’ by gvs [SUBSET_DEF]
          >> qpat_x_assum ‘matching G m’ mp_tac >> simp [matching_def] >> disj2_tac
          >> qexistsl_tac [‘{a; b}’, ‘{a'; b}’] >> art [] >> SET_TAC []
         )
      >> last_x_assum (irule o Q.SPEC ‘m’) >> gvs [SUBSET_DEF]
     )
  >> sg ‘∀m a b. matching G m ∧ a ∈ A ∧ b ∈ B ∧ {a; b} ∈ E ⇒ unmatched G m b ⇒ acc m a b’
  >- (rw [Abbr ‘acc’, Once unmatched, Once matched] >> METIS_TAC [IN_INSERT]
     )
  >> sg ‘∀m a b. a ∈ A ∧ b ∈ B ∧
         {a; b} ∈ E DIFF m ∧
             (∀a'. a' ∈ A ∧ {a'; b} ∈ m ⇒ (a', a) ∈ (R b)) ⇒ acc m a b
        ’
  >- ASM_SET_TAC []
  >> sg ‘∀m m' a b. matching G m ∧ m' ⊆ m ∧ {a; b} ∈ m' ⇒ acc m' a b ⇒ acc m a b’
  >- (rw [Abbr ‘acc’] >> Suff ‘a' = a’
      >- (Rewr'
          >> qpat_x_assum ‘_ ∈ E’ mp_tac >> ORW [GSYM neighbour_iff_inedge]
          >> qpat_x_assum ‘preference _ _’ mp_tac >> simp [preference_def]
         )
      >> CCONTR_TAC
      >> ‘{a'; b} ≠ {a; b}’ by (pop_assum mp_tac >> SET_TAC [])
      >> ‘{a; b} ∈ m’ by PROVE_TAC [SUBSET_DEF]
      >> fs [matching_def] >> qpat_x_assum ‘∀e1 e2. _ ⇒ DISJOINT _ _’ dxrule_all
      >> SET_TAC []
     )
  (* acc_set es m a = set of b's in es such that a is acceptable to b WRT m *)
  >> qabbrev_tac ‘acc_set = λes m a. {b | acc m a b ∧ {a; b} ∈ es}’
  >> sg ‘∀es m a. es ⊆ E ∧ a ∈ A ⇒ acc_set es m a ⊆ neighbour G a’
  >- (rw [Abbr ‘acc_set’ , neighbour_iff_adj, adjacent_fsg, SUBSET_DEF]
     )
  (* P es m = set of unmatched a's in A and acceptable to some b *)
  >> qabbrev_tac ‘P = λes m.
                        {a | a ∈ A ∧ a ∉ BIGUNION m ∧ ∃b. b ∈ acc_set es m a}’
  >> sg ‘∀a es m. a ∈ P es m ∧ matching G m ⇒ unmatched G m a’
  >- (rw [Abbr ‘P’, Abbr ‘acc_set’, unmatched, matched]
     )
  (* Amax es m a = (R a)-maximal element of acc_set es m a *)
  >> qabbrev_tac ‘Amax = λes m a. CHOICE (maximal_elements (acc_set es m a) (R a))’
  >> sg ‘∀es m a. a ∈ A ∧ es ⊆ E ∧ matching G m ∧ acc_set es m a ≠ ∅ ⇒ a ∈ P es m ⇒ Amax es m a ∈ B’
  >- (rw [Abbr ‘Amax’, Abbr ‘acc_set’] >> Suff ‘maximal_elements {b | acc m a b ∧ {a; b} ∈ es} (R a) ⊆ B’
      >- (rw [SUBSET_DEF] >> pop_assum irule
          >> irule CHOICE_DEF >> rw [Once EXTENSION]
          >> irule finite_linear_order_has_local_maximal_lemma
          >> rw []
          >> qexists_tac ‘neighbour G a’ >> ‘a ∈ V’ by ASM_SET_TAC [] >> reverse $ rw [neighbour_FINITE]
          >- gvs [preference_def]
          >> rw [SUBSET_DEF, neighbour_iff_adj, adjacent_fsg] >> gvs [SUBSET_DEF]
         )
      >> rw [SUBSET_DEF] >> drule maximal_elements_IN >> rw []
      >> ‘{a; x} ∈ E’ by ASM_SET_TAC [] >> qpat_x_assum ‘∀e. e ∈ E ⇒ ∃n1 n2. _’ drule
      >> rw [INSERT2_lemma] >> ASM_SET_TAC []
     )
  (* termination condition *)
  >> qabbrev_tac ‘Q = λ(es :edge set, m).
                        es ⊆ E DIFF m ∧ P es m ≠ ∅’
  (* iteration step *)
  >> qabbrev_tac ‘h = λ(es :edge set, m :edge set).
                        let a = CHOICE (P es m);
                            b = Amax es m a
                        in
                          (es DELETE {a; b},
                           ({a; b} INSERT m) DIFF {e | e ∈ m ∧ b ∈ e}
                          )
                 ’
  >> qabbrev_tac ‘happy = λm a. a ∈ BIGUNION m ⇒ ∃b. {a; b} ∈ m ∧ ∀b'. acc m a b' ∧ {a; b'} ∈ E ⇒ (b',b) ∈ (R a)’
  (* >> qabbrev_tac ‘happy = λm a. a ∈ BIGUNION m ⇒ ∃b. {a; b} ∈ m ∧ b ∈ maximal_elements (acc_set E m a) (R a)’ *)
  >> qabbrev_tac ‘Inv = λ(es :edge set, m :edge set).
                          let rejected = E DIFF es DIFF m
                          in
                            matching G m ∧
                            es ⊆ E DIFF m ∧
                            (∀a. a ∈ A ⇒ happy m a ∧ (∀b. {a; b} ∈ rejected ⇒ ~acc m a b))
                 ’
  >> qabbrev_tac ‘r = measure (λ(es :edge set, m :edge set). CARD es)’
  >> ‘WF r’ by simp [Abbr ‘r’] >> dxrule WHILE_RULE
  >> disch_then (qspecl_then [‘Inv’, ‘Q’, ‘h’] mp_tac) >> impl_tac
  >- (CONJ_TAC
      >- (simp [Abbr ‘Q’, Abbr ‘r’, pairTheory.FORALL_PROD]
          >> qx_genl_tac [‘es’, ‘m’]
          >> qabbrev_tac ‘a = CHOICE (P es m)’ >> rw [Abbr ‘P’, Abbr ‘h’]
          >> ‘FINITE E’ by simp [FINITE_fsgedges] >> ‘es ⊆ E’ by ASM_SET_TAC []
          >> ‘FINITE es’ by PROVE_TAC [SUBSET_FINITE]
          >> rw [CARD_DELETE]
          >- (‘CARD es ≠ 0’ suffices_by intLib.ARITH_TAC
              >> drule CARD_EQ_0 >> METIS_TAC [MEMBER_NOT_EMPTY]
             )
          >> pop_assum mp_tac >> simp []
          >> qabbrev_tac ‘b = Amax es m a’ >> fs [Abbr ‘Amax’]
          >> qabbrev_tac ‘bs = (maximal_elements (acc_set es m a) (R a))’ >> fs []
          >> drule_at (Pos last) EXT_CHOICE_ABBR >> impl_tac
          >- (simp [GSYM MEMBER_NOT_EMPTY, Abbr ‘bs’, Abbr ‘acc_set’]
              >> irule finite_linear_order_has_local_maximal_lemma >> CONJ_TAC
              >- (qabbrev_tac ‘as = {a' | a' ∈ A ∧ (∀s. a' ∉ s ∨ s ∉ m) ∧ ∃b. acc m a' b ∧ {a'; b} ∈ es}’
                  >> gvs []
                  >> mp_tac (Q.SPEC ‘as’ $ INST_TYPE [alpha |-> “:vertex”] CHOICE_DEF)
                  >> ASM_SET_TAC []
                 )
              >> qexists_tac ‘neighbour G a’ >> gvs [preference_def]
              >> sg ‘a ∈ V’
              >- (qabbrev_tac ‘as = {a' | a' ∈ A ∧ (∀s. a' ∉ s ∨ s ∉ m) ∧ ∃b. acc m a' b ∧ {a'; b} ∈ es}’
                  >> gvs []
                  >> mp_tac (Q.SPEC ‘as’ $ INST_TYPE [alpha |-> “:vertex”] CHOICE_DEF)
                  >> ASM_SET_TAC []
                 )
              >> rw [neighbour_FINITE] >> rw [SUBSET_DEF, neighbour_def_adj', adjacent_fsg]
              >> PROVE_TAC [SUBSET_DEF]
             )
          >> simp [Abbr ‘bs’, Abbr ‘acc_set’] >> ASM_SET_TAC [maximal_elements_def]
         )
      >> simp [HOARE_SPEC_DEF, Abbr ‘Inv’, Abbr ‘Q’, Abbr ‘h’, pairTheory.FORALL_PROD]
      >> qx_genl_tac [‘es’, ‘m’]
      >> qabbrev_tac ‘a = CHOICE (P es m)’
      >> qabbrev_tac ‘b = Amax es m a’
      >> sg ‘P es m ≠ ∅ ⇒ a ∈ A’
      >- (strip_tac >> drule_all EXT_CHOICE_ABBR >> rw [Abbr ‘P’])
      >> sg ‘P es m ≠ ∅ ⇒ {a; b} ∉ m’
      >- (rw [] >> drule_all EXT_CHOICE_ABBR >> fs [Abbr ‘P’]
          >> rpt strip_tac >> qpat_x_assum ‘∀s. a ∉ s ∨ s ∉ m’ (mp_tac o Q.SPEC ‘{a; b}’) >> rw []
         )
      >> sg ‘∀es m a. es ⊆ E ∧ m ⊆ E ∧ a ∈ V ∧ acc_set es m a ≠ ∅ ⇒
                      Amax es m a ∈ maximal_elements (acc_set es m a) (R a)’
      >- (rpt strip_tac >> irule EXT_CHOICE_DEF >> rw [Abbr ‘Amax’, Abbr ‘acc_set’, GSYM MEMBER_NOT_EMPTY]
          >> irule finite_linear_order_has_local_maximal_lemma >> gvs []
          >> qexists_tac ‘neighbour G a'’ >> rw [neighbour_FINITE]
          >- (rw [SUBSET_DEF, neighbour_iff_adj, adjacent_fsg] >> ASM_SET_TAC [])
          >> gvs [preference_def]
         )
      >> strip_tac >> simp []
      (* Eliminating P es m ≠ ∅ antesdent *)
      >> rpt (qpat_x_assum ‘P es m ≠ _ ⇒ _’ imp_res_tac)
      >> sg ‘b ∈ B’
      >- (rw [Abbr ‘b’, Abbr ‘acc_set’] >> first_x_assum irule >> rw [EXT_CHOICE_ABBR]
          >- (rw [Once EXTENSION] >> drule_all EXT_CHOICE_ABBR >> rw [Abbr ‘P’]
             )
          >> PROVE_TAC [SUBSET_DIFF]
         )
      >> drule_all_then assume_tac EXT_CHOICE_ABBR
      >> sg ‘b ∈ maximal_elements (acc_set es m a) (R a)’
      >- (simp [Abbr ‘b’] >> first_x_assum irule
          >> pop_assum mp_tac >> simp [Abbr ‘P’] >> rw [Once EXTENSION]
          >- (qpat_x_assum ‘a ∈ A’ mp_tac
              >> qpat_x_assum ‘_ = V’ (ORW o wrap o SYM)
              >> SET_TAC []
             )
          >- (qpat_x_assum ‘es ⊆ _’ mp_tac >> SET_TAC []
             )
          >> qpat_x_assum ‘matching G m’ mp_tac >> simp [matching_def]
         )
      >> qabbrev_tac ‘m' = {a; b} INSERT m DIFF {e | e ∈ m ∧ b ∈ e}’
      >> CONJ_ASM1_TAC
      >- (rw [Abbr ‘m'’, Abbr ‘acc_set’] >> ORW [matching_insert] >> conj_asm1_tac
          >- (irule matching_SUBSET >> qexists_tac ‘m’ >> rw [DIFF_SUBSET]
             )
          >> reverse conj_tac
          >- (drule_all EXT_CHOICE_ABBR
              >> rw [GSYM adjacent_fsg, adj_iff_neighbour, Abbr ‘Amax’]
              >> fs [] >> drule_at (Pos last) EXT_CHOICE_ABBR
              >> impl_tac
              >- (rw [GSYM MEMBER_NOT_EMPTY]
                  >> irule finite_linear_order_has_local_maximal_lemma >> rw [Abbr ‘P’]
                  >- (fs [] >> rw [GSYM MEMBER_NOT_EMPTY] >> qexists_tac ‘b'’ >> art []
                     )
                  >> qexists_tac ‘neighbour G a’
                  >> ‘a ∈ V’ by ASM_SET_TAC [] >> conj_asm1_tac
                  >- (irule neighbour_FINITE >> art []
                     )
                  >> conj_asm2_tac
                  >- (rw [SUBSET_DEF, neighbour_iff_adj, adjacent_fsg] >> ASM_SET_TAC []
                     )
                  >> gvs [preference_def]
                 )
              >> strip_tac >> dxrule maximal_elements_IN
              >> rw [neighbour_iff_adj, adjacent_fsg] >> ASM_SET_TAC []
             )
          >> rw [DISJOINT_ALT]
          >- PROVE_TAC []
          >> qpat_x_assum ‘a ∈ P es m’ mp_tac >> rw [Abbr ‘P’]
          >> ORW [DISJ_ASSOC] >> disj1_tac >> PROVE_TAC []
         )
      >> sg ‘{a; b} ∈ E’
      >- (qpat_x_assum ‘matching G m'’ (mp_tac o REWRITE_RULE [matching_def])
          >> pop_assum mp_tac >> SET_TAC []
         )
      >> sg ‘acc m a b’
      >- (drule_all EXT_CHOICE_ABBR >> rw [Abbr ‘P’]
          >> imp_res_tac $ iffLR $ Q.SPEC ‘acc_set es m a’ MEMBER_NOT_EMPTY
          >> Cases_on ‘unmatched G m b’
          >- (qpat_x_assum ‘∀m a b. _ ⇒ unmatched G m b ⇒ acc m a b’ irule >> art []
             )
          >> pop_assum mp_tac >> rw [unmatched, matched]
          >> qpat_x_assum ‘a ∈ P es m’ mp_tac
          >> disch_tac >> dxrule_all maximal_elements_IN >> rw [Abbr ‘acc_set’]
         )
      >> CONJ_TAC
      >- (qpat_x_assum ‘es ⊆ _’ mp_tac >> simp [Abbr ‘m'’] >> SET_TAC [])
      >> qx_gen_tac ‘a'’ >> strip_tac >> CONJ_ASM1_TAC
      >- (Cases_on ‘a' = a’
          >- (rw []
              >> ‘a ∈ V’ by ASM_SET_TAC []
              >> first_x_assum $ drule_then strip_assume_tac
              >> simp [Abbr ‘happy’] >> rw []
              >> qexists_tac ‘b’ >> conj_asm1_tac
              >- simp [Abbr ‘m'’]
              >> sg ‘b ∈ maximal_elements (acc_set es m a) (R a)’
              >- (irule EXT_CHOICE_DEF >> rw [Abbr ‘b’, Abbr ‘Amax’, Abbr ‘acc_set’]
                  >> rw [Once EXTENSION] >> irule finite_linear_order_has_local_maximal_lemma
                  >> conj_asm2_tac
                  >- (qpat_x_assum ‘a ∈ P es m’ mp_tac
                      >> rw [Abbr ‘P’, Once EXTENSION]
                     )
                  >> qexists_tac ‘neighbour G a’ >> conj_tac
                  >- PROVE_TAC [neighbour_FINITE]
                  >> reverse conj_tac
                  >- (qpat_x_assum ‘preference G R’ mp_tac >> simp [preference_def])
                  >> rw [SUBSET_DEF, neighbour_iff_inedge]
                  >> pop_assum mp_tac >> qpat_x_assum ‘es ⊆ E DIFF _’ mp_tac >> SET_TAC []
                 )
              >> rpt strip_tac >> Cases_on ‘b' = b’
              >- (qpat_x_assum ‘preference _ _’ mp_tac >> simp [preference_def, linear_order_def]
                  >> rw [] >> ‘b ∈ neighbour G a’ suffices_by PROVE_TAC [] >> rw [neighbour_iff_inedge]
                 )
              >> sg ‘{a; b'} ∉ m'’
              >- (CCONTR_TAC
                  >> qpat_x_assum ‘matching G m'’ mp_tac >> simp [matching_def]
                  >> disj2_tac >> qexistsl_tac [‘{a; b}’, ‘{a; b'}’]
                  >> rw [] >> qpat_x_assum ‘b' ≠ b’ mp_tac >> SET_TAC []
                 )
              >> Cases_on ‘{a; b'} ∈ es’
              >- (sg ‘b' ∈ acc_set es m a’
                  >- (rw [Abbr ‘acc_set’] >> simp [Abbr ‘acc’]
                      >> qpat_x_assum ‘(\m a b. _) m' a b'’ mp_tac >> rw []
                      >> first_x_assum irule >> simp [Abbr ‘m'’]
                      >> ‘b ≠ a'’ suffices_by rw []
                      >> qpat_x_assum ‘b ∈ B’ mp_tac
                      >> qpat_x_assum ‘a' ∈ A’ mp_tac
                      >> qpat_x_assum ‘DISJOINT A B’ mp_tac
                      >> KILL_TAC >> SET_TAC []
                     )
                  >> irule maximal_linear_order_local
                  >> qexists_tac ‘neighbour G a’ >> qexists_tac ‘acc_set es m a’ >> rw []
                  >- (first_x_assum irule >> ASM_SET_TAC [])
                  >> gvs [preference_def]
                 )
              >> qpat_x_assum ‘∀b. _ ⇒ ¬acc m a b’ (mp_tac o Q.SPEC ‘b'’) >> rw []
              >> CCONTR_TAC >> qpat_x_assum ‘acc m' _ _’ mp_tac >> simp []
              >> qpat_x_assum ‘_ ⇒ ~acc m _ _’ mp_tac >> impl_tac
              >- (qpat_x_assum ‘_ ∉ m'’ mp_tac >> simp [Abbr ‘m'’] >> rw []
                  >> ASM_SET_TAC []
                 )
              >> simp [Abbr ‘acc’] >> rw []
              >- (PROVE_TAC [])
              >> rpt DISJ2_TAC >> qexists_tac ‘a'’ >> simp [Abbr ‘m'’]
              >> sg ‘b ≠ a'’
              >- (qpat_x_assum ‘b ∈ B’ mp_tac
                  >> qpat_x_assum ‘a' ∈ A’ mp_tac
                  >> qpat_x_assum ‘DISJOINT A B’ mp_tac
                  >> KILL_TAC >> SET_TAC []
                 )
              >> rw []
             )
          >> Know ‘happy m a'’ >- PROVE_TAC []
          >> Cases_on ‘unmatched G m' a'’
          >- (pop_assum mp_tac >> simp [unmatched, matched, Abbr ‘happy’] >> PROVE_TAC []
             )
          >> pop_assum mp_tac >> simp [matched, Abbr ‘happy’] >> rw []
          >> sg ‘∃b''. {a'; b''} ∈ m'’
          >- (qexists_tac ‘paired_v s a'’
              >> qspecl_then [‘G’, ‘s’, ‘a'’] mp_tac paired_v_self
              >> ‘s ∈ E’ by PROVE_TAC [matching_def, SUBSET_DEF] >> simp []
             )
          >> qexists_tac ‘b''’ >> rw []
          >> qpat_x_assum ‘∀a. a ∈ A ⇒ _’ $ qspec_then ‘a'’ $ mp_tac >> rw []
          >> Know ‘∃s. a' ∈ s ∧ s ∈ m’
          >- (qexists_tac ‘{a'; b''}’ >> qpat_x_assum ‘{a'; b''} ∈ m'’ mp_tac >> simp [Abbr ‘m'’]
              >> strip_tac >> pop_assum mp_tac >> ASM_SET_TAC []
             )
          >> disch_tac >> qpat_x_assum ‘(∃s. a' ∈ s ∧ s ∈ m) ⇒ _’ dxrule >> rw []
          >> Suff ‘b'' = b'''’
          >- (rw [] >> pop_assum irule >> art []
              >> Cases_on ‘b' ∉ BIGUNION m’
              >- (pop_assum mp_tac
                  >> rw [] >> qpat_x_assum ‘acc _ _ _’ mp_tac >> simp [Abbr ‘acc’] >> rw []
                  >> CCONTR_TAC
                  >> qpat_x_assum ‘∀s'. b' ∉ s' ∨ s' ∉ m’ mp_tac
                  >> qpat_x_assum ‘{a''; b'} ∈ m’ mp_tac
                  >> rw [] >> qexists_tac ‘{a''; b'}’ >> art [] >> SET_TAC []
                 )
              >> rw []
              >> Cases_on ‘b' = b’
              >- (rw [] >> qpat_x_assum ‘acc m' _ _’ mp_tac >> simp [Abbr ‘acc’] >> rw []
                  >> qpat_x_assum ‘∀a''. _ ⇒ (a'',a') ∈ R b’ (mp_tac o Q.SPEC ‘a’) >> impl_tac
                  >- simp [Abbr ‘m'’]
                  >> disch_tac >> irule $ iffLR preference_notin2
                  >> conj_tac
                  >- (strip_tac >> rw []
                      >> sg ‘b = b''’
                      >- (CCONTR_TAC >> ‘{a'; b''} ≠ {a'; b}’ by (pop_assum mp_tac >> SET_TAC [])
                          >> qpat_x_assum ‘matching G m’ (mp_tac o REWRITE_RULE [matching_def])
                          >> strip_tac >> pop_assum dxrule_all >> SET_TAC []
                         )
                      >> rw [] >> ‘{a'; b} ≠ {a; b}’ by (qpat_x_assum ‘a' ≠ a’ mp_tac >> SET_TAC [])
                      >> qpat_x_assum ‘matching G m'’ (mp_tac o REWRITE_RULE [matching_def])
                      >>  ‘{a; b} ∈ m'’ by simp [Abbr ‘m'’]
                      >> strip_tac >> pop_assum dxrule_all >> SET_TAC []
                     )
                  >> reverse conj_tac
                  >- (ORW [PAIR_SYM_lemma] >> qexists_tac ‘G’ >> art []
                      >> ASM_SET_TAC [matching_def] (* SLOW *)
                     )
                  >> CCONTR_TAC >> rw []
                  >> sg ‘(a,a'') ∈ R b’
                  >- (‘b ∈ V’ by ASM_SET_TAC [] (* SLOW *)
                      >> qpat_x_assum ‘preference _ _’ mp_tac
                      >> rw [preference_def, linear_order_def, transitive_def] >> pop_assum imp_res_tac
                     )
                  >> qpat_x_assum ‘_ m a b’ (mp_tac o BETA_RULE) >> strip_tac
                  >> pop_assum drule_all >> strip_tac
                  >> ‘antisym (R b)’ suffices_by PROVE_TAC [antisym_def]
                  >> ‘b ∈ V’ by ASM_SET_TAC []
                  >> qpat_x_assum ‘preference G R’ mp_tac >> rw [preference_def, linear_order_def]
                 )
              >> qpat_x_assum ‘acc m' _ _’ mp_tac >> simp [Abbr ‘acc’]
              >> ‘∀a. {a; b'} ∈ m' ⇔ {a; b'} ∈ m’ suffices_by PROVE_TAC []
              >> ‘b' ∈ B’ by (qpat_x_assum ‘∀n1 n2. _ ∈ E ⇒ _’ drule_all >> PROVE_TAC [DISJOINT_ALT])
              >> rw [Abbr ‘m'’] >> reverse iff_tac
              >- (strip_tac >> disj2_tac >> art []
                  >> ‘m ⊆ E’ by PROVE_TAC [matching_def] >> ‘{a'';b'} ∈ E’ by PROVE_TAC [SUBSET_DEF]
                  >> qpat_x_assum ‘∀n1 n2. _ ∈ E ⇒ _’ drule_all >> rw [] >> PROVE_TAC [DISJOINT_ALT]
                 )
              >> rw [] >> pop_assum mp_tac >> ‘b' ≠ a ∧ b' ≠ b’ suffices_by SET_TAC []
              >> art [] >> PROVE_TAC [DISJOINT_ALT]
             )
          >> qpat_x_assum ‘{a'; b''} ∈ m'’ mp_tac >> rw [Abbr ‘m'’]
          >- (pop_assum mp_tac
              >> qpat_x_assum ‘a ∈ A’ mp_tac
              >> qpat_x_assum ‘a' ∈ A’ mp_tac
              >> qpat_x_assum ‘a' ≠ a’ mp_tac
              >> qpat_x_assum ‘b ∈ B’ mp_tac
              >> qpat_x_assum ‘DISJOINT _ _’ mp_tac
              >> KILL_TAC >> SET_TAC []
             )
          >> CCONTR_TAC
          >> ‘{a'; b''} ≠ {a'; b'''}’ by (pop_assum mp_tac >> SET_TAC [])
          >> qpat_x_assum ‘matching G m’ (dxrule_all o CONJUNCT2 o REWRITE_RULE [matching_def])
          >> pop_assum mp_tac >> SET_TAC []
         )
      >> ‘b ≠ a'’ by PROVE_TAC [DISJOINT_ALT] >> simp []
      >> gen_tac >> reverse strip_tac
      >- (rw [] >> ‘a' ≠ a’ by (qpat_x_assum ‘{a'; b} ≠ {a; b}’ mp_tac >> SET_TAC [])
          >> simp [Abbr ‘acc’] >> qexists_tac ‘a’ >> conj_tac
          >- simp [Abbr ‘m'’]
          >> irule $ iffRL preference_notin2 >> ORW [PAIR_SYM_lemma] >> rw []
          >- (qpat_x_assum ‘_ m a b’ (mp_tac o BETA_RULE) >> strip_tac
              >> pop_assum drule >> art []
             )
          >> qexists_tac ‘G’ >> art []
          >> qpat_x_assum ‘_ = V’ (ORW o wrap o SYM) >> simp [SUBSET_UNION]
         )
      >> sg ‘b' ∈ B’
      >- (qpat_x_assum ‘∀n1 n2. _ ∈ E ⇒ _’ dxrule_all >> rw [] >> PROVE_TAC [DISJOINT_ALT]
         )
      >> ‘happy m a'’ by (qpat_x_assum ‘∀a. a ∈ A ⇒ _’ dxrule >> simp [])
      >> qpat_x_assum ‘∀a. a ∈ A ⇒ _’ (drule_all o REWRITE_RULE [PULL_FORALL, GSYM CONJ_ASSOC]) >> rw []
      >> pop_assum imp_res_tac
      >> pop_assum mp_tac >> rw [Abbr ‘acc’]
      >> Cases_on ‘b' = b’
      >- (qexists_tac ‘a’ >> rw [Abbr ‘m'’]
          >> irule $ iffRL preference_notin2 >> conj_tac
          >- (qpat_x_assum ‘ _ ≠ {a; b}’ mp_tac >> SET_TAC []
             )
          >> reverse conj_tac
          >- (qexists_tac ‘G’ >> rw [PAIR_SYM_lemma]
              >> qpat_x_assum ‘_ = V’ (ORW o wrap o SYM) >> simp [SUBSET_UNION]
             )
          >> Cases_on ‘a'' = a’
          >- (qpat_x_assum ‘{a; b} ∉ m’ mp_tac
              >> qpat_x_assum ‘{a''; b} ∈ m’ mp_tac
              >> rw []
             )
          >> sg ‘(a',a'') ∈ R b’
          >- (irule $ iffLR preference_notin2 >> rw [PAIR_SYM_lemma]
              >- (qpat_x_assum ‘{a'; b} ∉ m’ mp_tac
                  >> qpat_x_assum ‘{a''; b} ∈ m’ mp_tac
                  >> SET_TAC []
                 )
              >> qexists_tac ‘G’ >> rw []
              >- (qpat_x_assum ‘{a''; b} ∈ m’ mp_tac
                  >> qpat_x_assum ‘matching G m’ (mp_tac o CONJUNCT1 o (REWRITE_RULE [matching_def]))
                  >> SET_TAC []
                 )
              >> qpat_x_assum ‘_ = V’ (ORW o wrap o SYM) >> rw [UNION_DEF]
             )
          >> Suff ‘(a'',a) ∈ R b’
          >- (‘transitive (R b)’ suffices_by PROVE_TAC [transitive_def]
              >> ‘b ∈ V’ by (qpat_x_assum ‘_ = V’ (ORW o wrap o SYM) >> rw [UNION_DEF])
              >> qpat_x_assum ‘preference G R’ mp_tac >> rw [preference_def, linear_order_def]
             )
          >> qpat_x_assum ‘_ m a b’ (mp_tac o BETA_RULE) >> simp []
         )
      >> qexists_tac ‘a''’ >> rw [Abbr ‘m'’]
      >> PROVE_TAC [DISJOINT_ALT]
     )
  >> rw [HOARE_SPEC_DEF, Abbr ‘happy’]
  >> qabbrev_tac ‘es = FST $ WHILE Q h (E, ∅)’
  >> qabbrev_tac ‘M = SND $ WHILE Q h (E, ∅)’
  >> ‘WHILE Q h (E, ∅) = (es, M)’ by METIS_TAC [PAIR]
  >> qexists_tac ‘M’
  >> ‘Inv (E, ∅)’ by simp [Abbr ‘Inv’, EMPTY_is_matching] >> first_x_assum drule
  >> gvs [] >> rw []
  >> simp [stable_matching_def] >> STRONG_CONJ_TAC
  >- gvs [Abbr ‘Inv’]
  >> rw [] >> gvs [Abbr ‘Inv’]
  >> wlog_tac ‘v1 ∈ A’ [‘v1’, ‘v2’]
  >- (Suff ‘v2 ∈ A’
      >- (rw [] >> ‘{v2; v1} ∈ E ∧ {v2; v1} ∉ M’ by simp [PAIR_SYM_lemma]
          >> first_x_assum drule_all >> PROVE_TAC [PAIR_SYM_lemma]
         )
      >> qpat_x_assum ‘∀e. e ∈ E ⇒ ∃n1 n2. _’ drule >> ASM_SET_TAC []
     )
  >> rename [‘{a; b} ∉ M’]
  >> sg ‘b ∈ B’
  >- (qpat_x_assum ‘∀n1 n2. {n1; n2} ∈ E ⇒ _’ dxrule >> PROVE_TAC [DISJOINT_ALT]
     )
  >> Cases_on ‘{a; b} ∉ es’
  >- (first_x_assum drule >> rw [Abbr ‘acc’]
      >> pop_assum drule_all >> rw []
      >> disj2_tac >> qexists_tac ‘a'’ >> art []
      >> irule $ iffLR preference_notin2 >> reverse $ rw []
      >- (qexists_tac ‘G’ >> rw [PAIR_SYM_lemma]
          >- (qpat_x_assum ‘matching G _’ mp_tac >> qpat_x_assum ‘_ ∈ M’ mp_tac
              >> simp [matching_def] >> SET_TAC []
              )
          >> qpat_x_assum ‘_ = V’ (ORW o wrap o SYM) >> rw [UNION_DEF]
         )
      >> CCONTR_TAC >> fs []
     )
  >> sg ‘~(a ∉ BIGUNION M ∧ b ∉ BIGUNION M)’
  >- (CCONTR_TAC >> gvs []
      >> ‘a ∈ P es M’ suffices_by gvs [Abbr ‘Q’]
      >> rw [Abbr ‘P’] >> qexists_tac ‘b’
      >> simp [Abbr ‘acc’, Abbr ‘acc_set’, Abbr ‘Q’]
      >> ‘∀a. {a; b} ∉ M’ suffices_by SET_TAC [] >> rw []
      >> qabbrev_tac ‘s = {a'; b}’ >> ‘b ∈ s’ by ASM_SET_TAC []
      >> PROVE_TAC []
     )
  >> pop_assum mp_tac >> ORW [DECIDE “~(a ∧ b) ⇔ (~a ∧ b) ∨ (a ∧ ~b) ∨ (~a ∧ ~b)”] >> rw [] (* 3 *)
  >- (qpat_x_assum ‘∀a. a ∈ A ⇒ _’ drule
      >> Know ‘∃s. a ∈ s ∧ s ∈ M’
      >- PROVE_TAC []
      >> rw []
      >> disj1_tac >> qexists_tac ‘b'’ >> art []
      >> first_x_assum irule >> art [] >> rw [Abbr ‘acc’]
      >> CCONTR_TAC
      >> qpat_x_assum ‘{a'; b} ∈ M’ mp_tac
      >> qpat_x_assum ‘∀s. b ∉ s ∨ s ∉ M’ (mp_tac o Q.SPEC ‘{a'; b}’)
      >> SET_TAC []
     )
  >- (disj2_tac >> simp [Abbr ‘P’, Abbr ‘Q’]
      >> qpat_x_assum ‘~(_) (es, M)’ mp_tac >> rw [PAIR]
      >> qexists_tac ‘Aend s’ >> conj_asm1_tac
      >- (‘{Aend s; b} = s’ suffices_by simp []
          >> ‘s ∈ E’ by (qpat_x_assum ‘matching G M’ mp_tac >> rw [matching_def, SUBSET_DEF])
          >> qpat_x_assum ‘∀e. e ∈ E ⇒ _ ∧ _’ dxrule
          >> qpat_x_assum ‘b ∈ s’ mp_tac
          >> qpat_x_assum ‘b ∈ B’ mp_tac
          >> qpat_x_assum ‘DISJOINT _ _’ mp_tac
          >> SET_TAC []
         )
      >> qabbrev_tac ‘a' = Aend s’
      >> Suff ‘~acc M a b’
      >- (rw [Abbr ‘acc’]
          >> Suff ‘a'' = a'’
          >- (rw [] >> irule $ iffLR preference_notin2 >> rw []
              >- (qpat_x_assum ‘{a'; b} ∈ M’ mp_tac \\
                  qpat_x_assum ‘{a; b} ∉ M’ mp_tac \\
                  SET_TAC []
                 )
              >> qexists_tac ‘G’ >> rw [PAIR_SYM_lemma]
              >- (‘M ⊆ E’ suffices_by rw [SUBSET_DEF] \\
                  qpat_x_assum ‘matching G M’ mp_tac >> KILL_TAC >> rw [matching_def]
                 )
              >> qpat_x_assum ‘_ = V’ (ORW o wrap o SYM) >> rw [UNION_DEF]
             )
          >> CCONTR_TAC
          >> ‘{a'; b} ≠ {a''; b}’ by (pop_assum mp_tac >> SET_TAC [])
          >> qpat_x_assum ‘matching G M’ (dxrule_all o CONJUNCT2 o REWRITE_RULE [matching_def])
          >> SET_TAC []
         )
      >> Suff ‘∀b. b ∉ acc_set es M a’
      >- (rw [Abbr ‘acc_set’] >> METIS_TAC []
         )
      >> CCONTR_TAC >> fs []
      >> qpat_x_assum ‘_ = ∅’ mp_tac >> rw [Once EXTENSION, PULL_EXISTS]
      >> qexistsl_tac [‘a’, ‘b'’] >> rw []
     )
  >> ‘s ∈ E ∧ s' ∈ E’ by PROVE_TAC [matching_def, SUBSET_DEF]
  >> NTAC 2 (dxrule alledges_valid) >> rw []
  >> wlog_tac ‘a' ∈ A’ [‘a'’, ‘b'’]
  >- (first_x_assum irule >> qexistsl_tac [‘b'’, ‘a'’] >> rw [PAIR_SYM_lemma] >> ASM_SET_TAC [])
  >> wlog_tac ‘a'' ∈ A’ [‘a''’, ‘b''’]
  >- (first_x_assum irule >> qexistsl_tac [‘b''’, ‘a''’] >> reverse $ rw [PAIR_SYM_lemma]
      >- ASM_SET_TAC []
      >> ‘{a''; b''} ∈ E’ by PROVE_TAC [matching_def, SUBSET_DEF]
      >> qpat_x_assum ‘∀e. e ∈ E ⇒ ∃n1 n2. _’ drule >> ASM_SET_TAC []
     )
  >> Suff ‘a' = a ∧ b'' = b’
  >- (rw []
      >> reverse $ Cases_on ‘acc M a b’
      (* ¬acc M a b: use acc definition. *)
      >- (disj2_tac >> qexists_tac ‘a''’ >> art []
          >> pop_assum mp_tac >> rw [Abbr ‘acc’]
          >> Suff ‘a'' = a'’
          >- (rw [] >> irule $ iffLR preference_notin2 >> rw []
              >- (qpat_x_assum ‘{a'; b} ∈ M’ mp_tac \\
                  qpat_x_assum ‘{a; b} ∉ M’ mp_tac \\
                  SET_TAC []
                 )
              >> qexists_tac ‘G’ >> rw [PAIR_SYM_lemma]
              >- (‘M ⊆ E’ suffices_by rw [SUBSET_DEF] \\
                  qpat_x_assum ‘matching G M’ mp_tac >> KILL_TAC >> rw [matching_def]
                 )
              >> qpat_x_assum ‘_ = V’ (ORW o wrap o SYM) >> rw [UNION_DEF]
             )
          >> CCONTR_TAC
          >> ‘{a'; b} ≠ {a''; b}’ by (pop_assum mp_tac >> SET_TAC [])
          >> qpat_x_assum ‘matching G M’ (dxrule_all o CONJUNCT2 o REWRITE_RULE [matching_def])
          >> SET_TAC []
         )
      (* acc M a b: use fact that a is happy (expanded) with M. *)
      >> disj1_tac >> qexists_tac ‘b'’ >> art []
      >> qpat_x_assum ‘∀a. a ∈ A ⇒ _’ (mp_tac o Q.SPEC ‘a’) >> rw []
      >> qpat_x_assum ‘_ ⇒ ∃b. _’ mp_tac >> impl_tac
      >- (qexists_tac ‘{a; b'}’ >> rw []
         )
      >> rw []
      >> ‘b' = b''’ suffices_by PROVE_TAC []
      >> CCONTR_TAC >> ‘{a; b'} ≠ {a; b''}’ by (pop_assum mp_tac >> SET_TAC [])
      >> qpat_x_assum ‘matching G M’ (dxrule_all o CONJUNCT2 o REWRITE_RULE [matching_def])
      >> SET_TAC []
     )
  >> ‘{a'; b'} ∈ E ∧ {a''; b''} ∈ E’ by PROVE_TAC [matching_def, SUBSET_DEF]
  >> NTAC 2 $ qpat_assum ‘∀e. e ∈ E ⇒ ∃n1 n2. _’ dxrule >> rw []
  >- ASM_SET_TAC []
  >> qpat_assum ‘∀e. e ∈ E ⇒ ∃n1 n2. _’ drule >> rw []
  >> qpat_assum ‘∀e. e ∈ E ⇒ ∃n1 n2. _’ (mp_tac o Q.SPEC ‘{a; a''}’)
  >> ASM_SET_TAC []
QED


val _ = html_theory "matching";
