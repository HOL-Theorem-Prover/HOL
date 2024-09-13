(*---------------------------------------------------------------------------*
 * fsgraphTheory: Theory of Finite Simple Graphs                             *
 *---------------------------------------------------------------------------*)

open HolKernel Parse boolLib bossLib;

open arithmeticTheory pairTheory listTheory pred_setTheory sortingTheory
     hurdUtils

open genericGraphTheory;

val _ = new_theory "fsgraph";

Type fsgraph[pp] = “:(unit,finiteG,noSL) udulgraph”
Definition fsgedges_def:
  fsgedges (g: fsgraph) = { {m;n} | adjacent g m n}
End

Theorem adjacent_fsg:
  adjacent (g : fsgraph) a b ⇔ {a;b} ∈ fsgedges g
Proof
  dsimp[fsgedges_def, INSERT2_lemma] >>
  metis_tac[adjacent_SYM]
QED

Overload fsgAddNode = “λn g:fsgraph. addNode n () g”

Theorem nodes_fsgAddNode[simp] :
  nodes (fsgAddNode n g) = n INSERT nodes g
Proof
  rw []
QED

Definition fsgAddEdges_def:
  fsgAddEdges (es0: (unit + num) set set) (g:fsgraph) =
  let
    es = { (m,n) | m ≠ n ∧ m ∈ nodes g ∧ n ∈ nodes g ∧ {m;n} ∈ es0 }
  in
    ITSET (λ(m,n) g. addUDEdge {m; n} () g) es g
End

Definition valid_edges_def:
  valid_edges es s ⇔ ∀e. e ∈ es ⇒ e ⊆ s ∧ FINITE e ∧ CARD e = 2
End

Theorem fsgedges_emptyG[simp]:
  fsgedges emptyG = ∅
Proof
  simp[fsgedges_def]
QED

Theorem fsgedges_addNode[simp]:
  fsgedges (fsgAddNode n g) = fsgedges g
Proof
  simp[fsgedges_def]
QED

Theorem nodes_fsgAddEdges[simp]:
  nodes (fsgAddEdges es g) = nodes g
Proof
  simp[fsgAddEdges_def] >>
  qmatch_abbrev_tac ‘nodes (ITSET _ A g) = nodes g’ >>
  ‘FINITE A’
    by (irule SUBSET_FINITE >>
        qexists ‘nodes g × nodes g’ >>
        simp[Abbr‘A’, SUBSET_DEF, FORALL_PROD]) >>
  ‘∀m n. (m,n) ∈ A ⇒ m ∈ nodes g ∧ n ∈ nodes g’ by simp[Abbr‘A’] >>
  markerLib.RM_ABBREV_TAC "A" >> rpt (pop_assum mp_tac) >> qid_spec_tac ‘g’ >>
  Induct_on ‘FINITE’ >>
  simp[addUDEdge_udul_LCOMM, COMMUTING_ITSET_RECURSES, FORALL_PROD,
       DELETE_NON_ELEMENT_RWT] >>
  simp[DISJ_IMP_THM, FORALL_AND_THM] >> rw[] >>
  first_x_assum $ drule_then assume_tac >> simp[] >>
  ASM_SET_TAC[]
QED

Theorem fsgedges_fsgAddEdges:
  fsgedges (fsgAddEdges es g) =
    {{m;n} | m ∈ nodes g ∧ n ∈ nodes g ∧ {m;n} ∈ es ∧ m ≠ n} ∪
    fsgedges g
Proof
  simp[fsgAddEdges_def, fsgedges_def, adjacent_def] >>
  qabbrev_tac ‘A = {(m,n) | m ≠ n ∧ m ∈ nodes g ∧ n ∈ nodes g ∧ {m;n} ∈ es}’ >>
  ‘FINITE A’
    by (irule SUBSET_FINITE >> qexists ‘nodes g × nodes g’ >>
        simp[SUBSET_DEF, Abbr‘A’, PULL_EXISTS]) >>
  ‘∀m n. (m,n) ∈ A ⇒ m ≠ n’ by simp[Abbr‘A’, PULL_EXISTS] >>
  ‘∀m n. (m,n) ∈ A ⇒ m ∈ nodes g ∧ n ∈ nodes g’
    by (qunabbrev_tac ‘A’ >> simp_tac (srw_ss()) []) >>
  ‘∀n. (n,n) ∉ A’ by metis_tac[] >>
  drule_then drule edges_ITSET_addUDEdge_udul >> simp[edgebag_1udedge] >>
  disch_then kall_tac >>
  qunabbrev_tac ‘A’ >>
  simp_tac (srw_ss()) [Once EXTENSION, FORALL_PROD] >>
  rpt (pop_assum kall_tac) >> gen_tac >> iff_tac >> rw[] >>
  gvs[enodes_def, PULL_EXISTS] >> dsimp[] >> metis_tac[]
QED

Theorem fsgedges_fsgAddEdges_thm[simp]:
  valid_edges es (nodes g) ⇒
  fsgedges (fsgAddEdges es g) = es ∪ fsgedges g
Proof
  simp[fsgedges_fsgAddEdges] >>
  simp[valid_edges_def, Once EXTENSION] >> rw[] >> iff_tac >> rpt strip_tac >>
  simp[] >> first_x_assum drule >> simp[CARDEQ2, SF CONJ_ss, PULL_EXISTS] >>
  rw[] >> metis_tac[]
QED

Theorem adjacent_fsgEdges[simp]:
  adjacent (fsgAddEdges es g) m n ⇔
    adjacent g m n ∨
    m ≠ n ∧ m ∈ nodes g ∧ n ∈ nodes g ∧ {m;n} ∈ es
Proof
  simp[adjacent_fsg, fsgedges_fsgAddEdges] >> iff_tac >> rw[] >> simp[]
  >- gvs[INSERT2_lemma] >> metis_tac[]
QED

Theorem fsgincident_SUBSET_nodes:
  e ∈ fsgedges g ∧ n ∈ e ⇒ n ∈ nodes g
Proof
  simp[fsgedges_def, PULL_EXISTS, SF CONJ_ss] >>
  metis_tac[adjacent_members]
QED

Theorem FINITE_fsgedges[simp]:
  FINITE (fsgedges (g : fsgraph))
Proof
  irule SUBSET_FINITE >> qexists ‘POW (nodes g)’ >> simp[] >>
  rw[SUBSET_DEF, FORALL_PROD, IN_POW] >> metis_tac[fsgincident_SUBSET_nodes]
QED

Theorem fsgraph_decomposition:
  ∀g. g = emptyG ∨
      ∃n es g0 : fsgraph.
        n ∉ nodes g0 ∧ FINITE es ∧ g = fsgAddEdges es (addNode n () g0) ∧
        valid_edges es (n INSERT nodes g0) ∧
        (∀e. e ∈ es ⇒ n ∈ e) ∧
        order g = order g0 + 1
Proof
  gen_tac >> Cases_on ‘g = emptyG’ >> simp[gsize_def] >>
  ‘nodes g ≠ ∅’ by (strip_tac >> gs[]) >>
  gs[GSYM MEMBER_NOT_EMPTY] >> rename [‘n ∈ nodes g’] >>
  qexistsl [‘n’, ‘{{m;n} | m | adjacent g m n }’, ‘removeNode n g’] >>
  simp[] >> rpt strip_tac >> simp[] >~
  [‘FINITE _’]
  >- (irule SUBSET_FINITE >> qexists‘IMAGE (λm. {m;n}) (nodes g)’ >>
      simp[SUBSET_DEF, PULL_EXISTS] >> metis_tac[adjacent_members]) >~
  [‘g = fsgAddEdges _ _’]
  >- (simp[ulabgraph_component_equality, is_hypergraph_def] >>
      simp[adjacent_def] >> simp[EXISTS_PROD, INSERT2_lemma] >>
      rw[EQ_IMP_THM]>> gvs[enodesEQ] >> dsimp[] >> csimp[] >>
      rename [‘BAG_IN (UDE {m;n} ()) (edgebag g)’] >>
      ‘m ∈ nodes g ∧ n ∈ nodes g’
        by (drule $ SRULE[udedges_def]incident_udedges_SUBSET_nodes >>
            simp[]) >>
      ‘m ≠ n’ by (strip_tac >> gvs[] >>
                  ‘adjacent g m m’ by (simp[adjacent_def] >>
                                       first_assum $ irule_at Any >> simp[]) >>
                  drule adjacent_REFL_E >> simp[]) >>
      metis_tac[INSERT_COMM]) >~
  [‘valid_edges _ _’]
  >- (simp[valid_edges_def, PULL_EXISTS] >>
      metis_tac[adjacent_members, adjacent_irrefl]) >~
  [‘CARD _ = CARD _ - 1 + 1’]
  >- (‘0 < CARD (nodes g)’ suffices_by simp[] >>
      CCONTR_TAC >> gs[])
QED

Theorem fsg_induction:
  ∀P. P emptyG ∧
      (∀n es g0.
         P g0 ∧ FINITE es ∧ n ∉ nodes g0 ∧ valid_edges es (n INSERT nodes g0) ∧
         (∀e. e ∈ es ⇒ n ∈ e) ⇒
         P (fsgAddEdges es (addNode n () g0))) ⇒
      ∀g. P g
Proof
  rpt strip_tac >> Induct_on ‘order g’ >> simp[] >> rpt strip_tac >>
  qspec_then ‘g’ strip_assume_tac fsgraph_decomposition >> gs[]
QED

Theorem fsgedges_empty_edgebag:
  fsgedges g = ∅ ⇔ edgebag g = EMPTY_BAG
Proof
  simp[fsgedges_def, adjacent_def] >> transferLib.xfer_back_tac [] >>
  simp[Once EXTENSION, enodesEQ] >> simp[EQ_IMP_THM] >>
  rw[wfgraph_def, DISJ_EQ_IMP] >> gvs[dirhypcst_def, ITSELF_UNIQUE] >>
  CCONTR_TAC >>
  ‘∃e b0. g.edges = BAG_INSERT e b0’ by metis_tac[bagTheory.BAG_cases] >>
  gvs[] >> metis_tac[]
QED

Theorem fsgedges_udedges:
  fsgedges g = { {m;n} | undirected {m;n} () ∈ udedges g }
Proof
  simp[adjacent_undirected, fsgedges_def]
QED

Theorem fsg_decomposition1:
  ∀g:fsgraph.
    g = emptyG ∨
    (∃g0 n. g = fsgAddNode n g0 ∧ n ∉ nodes g0) ∨
    (∃g0 m n.
       g = fsgAddEdges {{m;n}} g0 ∧ m ∈ nodes g0 ∧ n ∈ nodes g0 ∧ m ≠ n ∧
       ¬adjacent g0 m n)
Proof
  gen_tac >> Cases_on ‘g = emptyG’ >> simp[] >>
  Cases_on ‘fsgedges g = {}’
  >- (‘nodes g ≠ {}’ by simp[] >>
      gs[GSYM MEMBER_NOT_EMPTY] >> rename [‘n ∈ nodes g’] >>
      disj1_tac >> qexistsl [‘removeNode n g’, ‘n’] >>
      simp[] >>
      ‘isolated g {n}’ suffices_by simp[isolated_addNode_removeNode] >>
      simp[isolated_def] >> ‘edgebag g = EMPTY_BAG’ suffices_by simp[] >>
      gvs[fsgedges_empty_edgebag]) >>
  disj2_tac >>
  gvs[GSYM MEMBER_NOT_EMPTY] >> rename [‘e ∈ fsgedges g’] >>
  gvs[fsgedges_def] >> rename [‘adjacent g m n’] >>
  qexistsl [‘removeEdge (UDE {m;n} ()) g’, ‘m’, ‘n’] >>
  simp[] >> drule_then strip_assume_tac adjacent_members >> simp[] >>
  rpt conj_tac >~
  [‘g = fsgAddEdges _ (removeEdge _ _)’]
  >- (simp[udul_component_equality, fsgAddEdges_def] >>
      qmatch_abbrev_tac ‘udedges g = udedges (ITSET _ A h)’ >>
      ‘FINITE A’
        by (irule SUBSET_FINITE >> qexists ‘nodes g × nodes g’ >>
            simp[Abbr‘A’, SUBSET_DEF, PULL_EXISTS]) >>
      ‘∀m n. (m,n) ∈ A ⇒ m ∈ nodes h ∧ n ∈ nodes h’ by simp[Abbr‘A’, Abbr‘h’]>>
      drule_then drule edges_ITSET_addUDEdge_udul >> simp[] >>
      ‘∀n. (n,n) ∉ A’ by simp[Abbr‘A’] >>
      simp[] >> disch_then kall_tac >> simp[Abbr‘h’, udedges_removeEdge] >>
      ‘m ≠ n’ by (strip_tac >> gvs[] >> drule adjacent_REFL_E >> simp[]) >>
      ‘{undirected {m;n} () | (m,n) ∈ A} = {undirected {m;n} ()}’
        by (simp[Once EXTENSION] >>
            simp[EQ_IMP_THM, PULL_EXISTS] >> simp[FORALL_AND_THM] >>
            simp[INSERT2_lemma, Abbr‘A’] >> dsimp[]) >>
      pop_assum SUBST1_TAC >>
      gvs[adjacent_fsg, fsgedges_udedges] >> gvs[INSERT2_lemma] >>
      ASM_SET_TAC[]) >~
  [‘adjacent g m n’, ‘m ≠ n’] >- (strip_tac >> gvs[]) >>
  gvs[adjacent_fsg, fsgedges_udedges] >>
  simp[udedges_removeEdge]
QED

Theorem order_fsgAddEdges[simp]:
  order (fsgAddEdges es g) = order g
Proof
  simp[gsize_def]
QED

Definition fsgsize_def:
  fsgsize (g : fsgraph) = CARD (fsgedges g)
End

Theorem fsgsize_empty[simp]:
  fsgsize emptyG = 0
Proof
  simp[fsgsize_def]
QED

Theorem fsg_induction1:
  ∀P. P emptyG ∧ (∀n g0. P g0 ∧ n ∉ nodes g0 ⇒ P (fsgAddNode n g0)) ∧
      (∀m n g0.
         P g0 ∧ m ∈ nodes g0 ∧ n ∈ nodes g0 ∧ ¬adjacent g0 m n ∧ m ≠ n ⇒
         P (fsgAddEdges {{m;n}} g0)) ⇒
      ∀g. P g
Proof
  gen_tac >> strip_tac >>
  ‘WF (inv_image ($< LEX $<) (λg:fsgraph. (gsize g, fsgsize g)))’
    by (irule relationTheory.WF_inv_image >>
        irule pairTheory.WF_LEX >> simp[]) >>
  drule_then irule relationTheory.WF_INDUCTION_THM >>
  qx_gen_tac ‘G’ >> simp[LEX_DEF] >> strip_tac >>
  qspec_then ‘G’ strip_assume_tac fsg_decomposition1 >> gvs[] >>
  last_x_assum irule >> simp[] >> first_x_assum irule >>
  simp[gsize_addNode, fsgedges_fsgAddEdges] >>
  simp[fsgsize_def] >>
  irule CARD_PSUBSET >> simp[PSUBSET_DEF, SUBSET_DEF, fsgedges_fsgAddEdges] >>
  simp[Once EXTENSION] >> qexists ‘{m;n}’ >> simp[] >>
  ‘{m;n} ∉ fsgedges g0’ by (simp[fsgedges_def, INSERT2_lemma] >>
                            metis_tac[adjacent_SYM]) >>
  simp[] >> metis_tac[]
QED

Theorem FINITE_sets_have_descending_measure_lists:
  ∀s. FINITE s ⇒
      ∃es. SORTED (inv $<=) (MAP f es) ∧ set es = s ∧
           ALL_DISTINCT es
Proof
  Induct_on ‘FINITE’ using FINITE_LEAST_MEASURE_INDUCTION >> qexists ‘f’ >>
  simp[PULL_EXISTS] >> rpt strip_tac >>
  rename [‘¬MEM a es’] >> qexists ‘es ++ [a]’ >>
  simp[EXTENSION, AC DISJ_ASSOC DISJ_COMM, ALL_DISTINCT_APPEND] >>
  simp[SORTED_APPEND, MEM_MAP, PULL_EXISTS]
QED

Theorem descending_measure_lists_unique:
  ∀es1 es2. SORTED (inv $<=) (MAP f es1) ∧ SORTED (inv $<=) (MAP f es2) ∧
            set es1 = set es2 ∧ ALL_DISTINCT es1 ∧ ALL_DISTINCT es2 ⇒
            MAP f es1 = MAP f es2
Proof
  Induct >> simp[SORTED_EQ, MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >> simp[MAP_EQ_CONS] >>
  Cases_on ‘es2’ >> gvs[SORTED_EQ, MEM_MAP, PULL_EXISTS] >>
  rename [‘h1 INSERT set es1 = h2 INSERT set es2’] >>
  Cases_on ‘h1 = h2’
  >- (gvs[] >> first_x_assum irule >> simp[] >>
      qpat_x_assum ‘_ INSERT _ = _ INSERT _’ mp_tac >>
      simp[EXTENSION] >> metis_tac[]) >>
  ‘MEM h1 es2 ∧ MEM h2 es1’ by (gs[EXTENSION] >> metis_tac[]) >>
  ‘f h1 = f h2’ by metis_tac[arithmeticTheory.EQ_LESS_EQ] >> simp[] >>
  ‘∃p2 s2. es2 = p2 ++ [h1] ++ s2’
    by metis_tac[MEM_SPLIT_APPEND_first] >>
  gvs[ALL_DISTINCT_APPEND, DISJ_IMP_THM, FORALL_AND_THM] >>
  first_x_assum $ qspec_then ‘p2 ++ [h2] ++ s2’ mp_tac >> simp[] >>
  disch_then irule >>
  simp[ALL_DISTINCT_APPEND, DISJ_IMP_THM, FORALL_AND_THM] >>
  qpat_x_assum ‘_ INSERT _ = _’ mp_tac >>
  simp[EXTENSION] >> metis_tac[]
QED

Theorem alledges_valid:
  ∀g : fsgraph. e ∈ fsgedges g ⇒
                ∃a b. e = {a;b} ∧ a ∈ nodes g ∧ b ∈ nodes g ∧ a ≠ b
Proof
  Induct_on ‘g’ using fsg_induction >> simp[] >> strip_tac
  >- (gs[valid_edges_def] >> rpt (first_x_assum $ drule_then strip_assume_tac)>>
      gvs[CARDEQ2] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem adjacent_removeEdge:
  adjacent (removeEdge (UDE {a;b} ())
               (g:(α,undirectedG,oneedgeG,unit,unhyperG,ε,ζ,noSL) graph)) m n ⇔
  (m ≠ a ∨ n ≠ b) ∧ (n ≠ a ∨ m ≠ b) ∧ adjacent g m n
Proof
  simp[adjacent_undirected, udedges_removeEdge, INSERT2_lemma] >>
  metis_tac[]
QED

Overload remove_fsgedge = “λns g. removeEdge (UDE ns ()) (g:fsgraph)”

Theorem fsgedges_remove_fsedge[simp]:
  fsgedges (remove_fsgedge e g) = fsgedges g DELETE e
Proof
  simp[Once EXTENSION] >> qx_gen_tac ‘e0’ >>
  simp[fsgedges_def, adjacent_undirected, udedges_removeEdge] >>
  iff_tac >> rw[] >> simp[] >> metis_tac[]
QED

Theorem fsgraph_component_equality:
  (g1 : fsgraph = g2) ⇔ nodes g1 = nodes g2 ∧ fsgedges g1 = fsgedges g2
Proof
  simp[gengraph_component_equality,fsgedges_def] >> iff_tac >> rw[] >>
  gvs[edgebag_1udedge, adjacent_undirected]
  >- (qpat_x_assum ‘GSPEC _ = GSPEC _’ mp_tac >> ONCE_REWRITE_TAC[EXTENSION] >>
      simp[EXISTS_UNDIREDGE] >>
      simp[EQ_IMP_THM, FORALL_AND_THM, PULL_EXISTS] >> metis_tac[])
  >- (qpat_x_assum ‘GSPEC _ = GSPEC _’ mp_tac >> ONCE_REWRITE_TAC[EXTENSION] >>
      simp[EXISTS_UNDIREDGE] >>
      simp[EQ_IMP_THM, FORALL_AND_THM, PULL_EXISTS] >> rpt strip_tac >>
      drule_then strip_assume_tac IN_udedges_E>> gvs[] >> metis_tac[]) >>
  simp[FUN_EQ_THM]
QED

Theorem fsgsize_remove_fsgedge[simp] :
  e IN fsgedges g ==> fsgsize (remove_fsgedge e g) = fsgsize g - 1
Proof
  rw [fsgsize_def, CARD_DELETE]
QED

Theorem fsgedges_members :
  !g x y. {x;y} IN fsgedges g ==> x <> y /\ x IN nodes g /\ y IN nodes g
Proof
  rpt GEN_TAC >> STRIP_TAC >> dxrule alledges_valid >>
  dsimp [INSERT2_lemma, PULL_EXISTS]
QED

Theorem fsgAddEdges_remove_fsgedge[simp] :
  e IN fsgedges g ==> fsgAddEdges {e} (remove_fsgedge e g) = g
Proof
  rpt STRIP_TAC
 >> Suff ‘valid_edges {e} (nodes g)’
 >- (rw [fsgraph_component_equality] \\
     ASM_SET_TAC [])
 >> ‘?a b. e = {a; b} /\ a IN nodes g /\ b IN nodes g /\ a <> b’
       by METIS_TAC [alledges_valid]
 >> rw [valid_edges_def]
QED

Definition fsgAddNodes_def :
  fsgAddNodes N g = ITSET fsgAddNode N g
End

Theorem fsgAddNode_commutes:
  fsgAddNode m (fsgAddNode n g) = fsgAddNode n (fsgAddNode m g)
Proof
  simp[fsgraph_component_equality] >> SET_TAC[]
QED

Theorem fsgAddNodes_EMPTY[simp]:
  fsgAddNodes {} g = g
Proof
  simp[fsgAddNodes_def]
QED

Theorem fsgAddNodes_INSERT:
  FINITE ns ⇒
  fsgAddNodes (n INSERT ns) g = fsgAddNode n (fsgAddNodes (ns DELETE n) g)
Proof
  simp[fsgAddNodes_def, COMMUTING_ITSET_RECURSES, fsgAddNode_commutes]
QED

Theorem nodes_fsgAddNodes[simp] :
  !g N. FINITE N ==> nodes (fsgAddNodes N g) = N UNION nodes g
Proof
  Induct_on ‘FINITE’ >> simp[fsgAddNodes_INSERT, DELETE_NON_ELEMENT_RWT] >>
  rpt strip_tac >> SET_TAC[]
QED

Theorem fsgedges_fsgAddNodes[simp] :
  !g N. FINITE N ==> fsgedges (fsgAddNodes N g) = fsgedges g
Proof
  Induct_on ‘FINITE’  >> simp [fsgAddNodes_INSERT, DELETE_NON_ELEMENT_RWT]
QED

Theorem fsgraph_edge_decomposition:
  !g. fsgsize (g: fsgraph) = 0 \/
      ?e g0. valid_edges {e} (nodes g0) /\ e NOTIN fsgedges g0 /\
             g = fsgAddEdges {e} g0 /\ fsgsize g = fsgsize g0 + 1
Proof
    rpt STRIP_TAC
 >> Cases_on ‘fsgsize g = 0’ >- rw []
 >> DISJ2_TAC
 >> ‘0 < fsgsize g’ by rw []
 >> ‘fsgedges g <> {}’ by fs [CARD_EQ_0, fsgsize_def]
 >> ‘?e. e IN fsgedges g’ by METIS_TAC [MEMBER_NOT_EMPTY]
 >> qexistsl_tac [‘e’, ‘remove_fsgedge e g’]
 >> fs [valid_edges_def]
 >> qspec_then ‘g’ strip_assume_tac alledges_valid >> gs []
QED

Theorem fsg_edge_induction :
  ∀g P.
    P (fsgAddNodes (nodes g) emptyG) /\
    (!e g0. nodes g0 = nodes g /\
            valid_edges {e} (nodes g0) /\ e NOTIN fsgedges g0 /\
            P g0 ==> P (fsgAddEdges {e} g0)) ==>
    P g
Proof
    rpt STRIP_TAC
 >> Induct_on ‘fsgsize g’
 >- (rw [] \\
     Suff ‘fsgAddNodes (nodes g) emptyG = g’ >- DISCH_THEN (fs o wrap) \\
     rw [fsgraph_component_equality] >> gvs[fsgsize_def])
 >> rpt strip_tac
 >> qspec_then ‘g’ strip_assume_tac fsgraph_edge_decomposition
 >> fs []
QED

(* vertices not even in the graph at all have degree 0 *)
Definition degree_def:
  degree (g: fsgraph) v = CARD { e | e ∈ fsgedges g ∧ v ∈ e }
End

Definition maxdegree_def:
  maxdegree (g : fsgraph) = MAX_SET (IMAGE (degree g) (nodes g))
End

Overload "Δ" = “maxdegree”

Definition mindegree_def:
  mindegree (g : fsgraph) = MIN_SET (IMAGE (degree g) (nodes g))
End
Overload "δ" = “mindegree”

Theorem degree_sequence_exists:
  ∀g : fsgraph.
    ∃ds. SORTED (inv $<=) ds ∧
         ∃ns. ds = MAP (degree g) ns ∧ set ns = nodes g ∧ ALL_DISTINCT ns
Proof
  simp[PULL_EXISTS] >> gen_tac >>
  irule FINITE_sets_have_descending_measure_lists >> simp[]
QED

val degree_sequence_def =
new_specification ("degree_sequence_def", ["degree_sequence"],
                   SRULE [Once SKOLEM_THM] degree_sequence_exists);

Theorem degree_sequence_emptyG[simp]:
  degree_sequence emptyG = []
Proof
  qspec_then ‘emptyG’ mp_tac degree_sequence_def >> simp[]
QED

Theorem degree_sequence_unique:
  ∀ns g. SORTED (inv $<=) $ MAP (degree g) ns ∧ set ns = nodes g ∧
         ALL_DISTINCT ns ⇒
         degree_sequence g = MAP (degree g) ns
Proof
  rpt strip_tac >> qspec_then ‘g’ strip_assume_tac degree_sequence_def >>
  simp[] >> irule descending_measure_lists_unique >> gvs[]
QED

val _ = temp_clear_overloads_on "equiv_class"
Theorem degree_fsgAddEdges:
  valid_edges es (nodes g) ⇒
  degree (fsgAddEdges es g) =
  λn. CARD ({ ed | ed ∈ es ∧ n ∈ ed } ∪ { ed | ed ∈ fsgedges g ∧ n ∈ ed})
Proof
  dsimp[degree_def, fsgedges_fsgAddEdges_thm, GSPEC_OR, FUN_EQ_THM]
QED

Theorem valid_edges_INSERT:
  valid_edges (e INSERT es) s ⇔ valid_edges es s ∧ e ⊆ s ∧ FINITE e ∧ CARD e = 2
Proof
  simp[valid_edges_def]>> metis_tac[]
QED

Theorem SUM_IMAGE_EQ1:
  FINITE A ⇒
  (SUM_IMAGE f A = 1 ⇔ ∃a. a ∈ A ∧ f a = 1 ∧ SUM_IMAGE f (A DELETE a) = 0)
Proof
  simp[SUM_IMAGE_ZERO] >> Induct_on ‘FINITE’ >> simp[SUM_IMAGE_THM] >> rw[] >>
  simp[arithmeticTheory.ADD_EQ_1, DELETE_NON_ELEMENT_RWT] >> iff_tac >> rw[]
  >- (dsimp[] >> gs[SUM_IMAGE_ZERO])
  >- (dsimp[] >> metis_tac[])
  >- (simp[SUM_IMAGE_ZERO] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem sumdegrees:
  ∀g. SUM_IMAGE (degree g) (nodes g) = 2 * fsgsize g
Proof
  simp[fsgsize_def] >> Induct using fsg_induction>>
  simp[pred_setTheory.SUM_IMAGE_THM, pred_setTheory.DELETE_NON_ELEMENT_RWT,
       fsgedges_fsgAddEdges_thm] >>
  ‘degree (fsgAddEdges es (addNode n () g)) n = CARD es’
    by (‘∀e. e ∈ fsgedges g ⇒ n ∉ e’
          by (simp[fsgedges_def, PULL_EXISTS] >>
              metis_tac[adjacent_members]) >>
        dsimp[degree_def, fsgedges_fsgAddEdges_thm, SF CONJ_ss]) >>
  simp[degree_fsgAddEdges] >>
  ‘(∀n. FINITE { ed | ed ∈ es ∧ n ∈ ed}) ∧
   ∀n. FINITE {ed | ed ∈ fsgedges g ∧ n ∈ ed}’
    by (conj_tac >> gen_tac >> irule SUBSET_FINITE
        >- (qexists ‘es’ >> simp[SUBSET_DEF])
        >- (qexists ‘fsgedges g’ >> simp[SUBSET_DEF])) >>
  simp[pred_setTheory.CARD_UNION_EQN] >>
  ‘∀n. {ed | ed ∈ es ∧ n ∈ ed} ∩ {ed | ed ∈ fsgedges g ∧ n ∈ ed} = ∅’
    by (simp[EXTENSION] >> rpt gen_tac >> CCONTR_TAC >> gs[] >>
        gs[fsgedges_def] >> first_x_assum drule >> strip_tac >> gvs[] >>
        metis_tac[adjacent_members]) >>
  simp[SUM_IMAGE_ADD] >>
  ‘es ∩ fsgedges g = ∅’ by (simp[fsgedges_def, Once EXTENSION] >>
                            CCONTR_TAC >> gvs[] >> first_x_assum drule >>
                            strip_tac >> gvs[] >> metis_tac[adjacent_members])>>
  simp[GSYM degree_def, SF ETA_ss] >>
  ‘SUM_IMAGE (λm. CARD { ed | ed ∈ es ∧ m ∈ ed}) (nodes g) = CARD es’
    suffices_by simp[] >>
  map_every (C qpat_x_assum mp_tac)
            [‘valid_edges es _’, ‘FINITE es’, ‘n ∉ nodes g’,
             ‘∀e. e ∈ es ⇒ n ∈ e’] >>
  qid_spec_tac ‘n’ >> rpt (pop_assum kall_tac) >> Induct_on ‘FINITE’ >>
  simp[] >> rw[] >> gvs[DISJ_IMP_THM, FORALL_AND_THM]
  >- simp[SUM_IMAGE_ZERO] >>
  dsimp[GSPEC_OR] >>
  ‘(∀n. FINITE {ed | ed = e ∧ n ∈ ed}) ∧ (∀n. FINITE {ed | ed ∈ es ∧ n ∈ ed})’
    by (conj_tac >> gen_tac >> irule SUBSET_FINITE
        >- (qexists ‘{e}’ >> simp[SUBSET_DEF])
        >- (qexists ‘es’ >> simp[SUBSET_DEF])) >>
  ‘∀n. {ed | ed = e ∧ n ∈ ed} ∩ {ed | ed ∈ es ∧ n ∈ ed} = ∅’
    by simp[Once EXTENSION] >>
  simp[CARD_UNION_EQN, SUM_IMAGE_ADD] >>
  gs[valid_edges_INSERT] >> first_x_assum $ drule_all >> simp[] >> strip_tac >>
  simp[DECIDE “x + y = SUC x ⇔ y = 1”] >>
  simp[SUM_IMAGE_EQ1] >>
  gvs[CARDEQ2] >> simp[SUM_IMAGE_ZERO] >>
  first_assum $ irule_at Any >> csimp[] >>
  simp[Once EXTENSION]
QED

Theorem ODD_SUMIMAGE:
  FINITE A ⇒
  (ODD (SUM_IMAGE f A) ⇔ ODD (CARD { a | a ∈ A ∧ ODD (f a) }))
Proof
  Induct_on ‘FINITE’ >>
  simp[SUM_IMAGE_THM, arithmeticTheory.ODD_ADD, DELETE_NON_ELEMENT_RWT,
       SF DNF_ss, GSPEC_OR] >>
  rw[] >> rename [‘a ∉ A’] >>
  ‘(∀P. FINITE { e | e = a ∧ P e }) ∧ (∀P. FINITE { e | e ∈ A ∧ P e })’
    by (rpt strip_tac >> irule SUBSET_FINITE >>
        simp[GSPEC_AND] >> irule_at Any $ cj 1 INTER_SUBSET >> simp[]) >>
  simp[CARD_UNION_EQN] >>
  ‘∀P Q. {e | e = a ∧ P e} ∩ {e | e ∈ A ∧ Q e} = ∅’
    by simp[EXTENSION] >>
  simp[arithmeticTheory.ODD_ADD] >>
  ‘ODD (CARD {e | e = a ∧ ODD (f e)}) = ODD (f a)’ suffices_by simp[] >>
  Cases_on ‘ODD (f a)’ >> simp[SF CONJ_ss]
QED

(* "number of nodes with odd degree is even" *)
Theorem EVEN_odddegree_nodes:
  ∀g:fsgraph. EVEN (CARD { n | ODD (degree g n) })
Proof
  gen_tac >> simp[arithmeticTheory.EVEN_ODD] >>
  ‘{n | ODD (degree g n) } = {n | n ∈ nodes g ∧ ODD (degree g n)}’
    by (simp[EXTENSION] >> qx_gen_tac ‘n’ >> iff_tac >> simp[]>>
        simp[degree_def] >> CCONTR_TAC >> gvs[] >>
        ‘{ e | e ∈ fsgedges g ∧ n ∈ e} = ∅’
          suffices_by (strip_tac >> gvs[]) >>
        simp[EXTENSION] >> qx_gen_tac ‘e’ >> simp[fsgedges_def] >>
        CCONTR_TAC >> gvs[] >> metis_tac[adjacent_members]) >>
  simp[GSYM ODD_SUMIMAGE, sumdegrees, SF ETA_ss, arithmeticTheory.ODD_MULT]
QED

(* ----------------------------------------------------------------------
    Perambulations
   ---------------------------------------------------------------------- *)

(* NOTE: added ‘!v. v IN nodes g’ to make sure vertices of single-vertex
   walks are indeed vertices in the graph.

   The existing ‘adjacent vs v1 v2 ==> adjacent g v1 v2’ can only guarantee
   it for walks of two or more vectices.  -- Chun Tian, August 10, 2023.
 *)
Definition walk_def:
  walk g vs <=> vs <> [] /\ (!v. MEM v vs ==> v IN nodes g) /\
               !v1 v2. adjacent vs v1 v2 ==> adjacent g v1 v2
End

Theorem trivial_walk[simp] :
  !g v. walk g [v] ⇔ v IN nodes g
Proof
    rw [walk_def]
QED

(* NOTE: A path is a walk without duplicated nodes/vertices. *)
Definition path_def:
  path g vs ⇔ walk g vs ∧ ALL_DISTINCT vs
End

Theorem trivial_path[simp] :
  !g v. path g [v] ⇔ v IN nodes g
Proof
    rw [path_def]
QED

Definition adjpairs_def[simp]:
  adjpairs [] = [] ∧
  adjpairs [x] = [] ∧
  adjpairs (x::y::xs) = {x;y} :: adjpairs (y::xs)
End

Theorem LENGTH_adjpairs:
  ∀vs. vs ≠ [] ⇒ LENGTH (adjpairs vs) = LENGTH vs - 1
Proof
  recInduct adjpairs_ind >> simp[]
QED

(* NOTE: A trail may go through some vertices more than once but only traverses
         each edge of the graph at most once. *)
Definition trail_def:
  trail g vs ⇔ walk g vs ∧ ALL_DISTINCT (adjpairs vs)
End

Definition cycle_def:
  cycle g vs ⇔ walk g vs ∧ ALL_DISTINCT (TL vs) ∧ 3 ≤ LENGTH vs ∧
               HD vs = LAST vs
End

Definition circuit_def:
  circuit g vs ⇔ 3 ≤ LENGTH vs ∧ trail g vs ∧ HD vs = LAST vs
End

Definition walklen_def:
  walklen vs = LENGTH (adjpairs vs)
End

Theorem adjacent_append2:
  adjacent ys a b ⇒ adjacent (xs ++ ys) a b
Proof
  Induct_on ‘xs’ >> simp[] >> Cases_on ‘xs’ >>
  gs[adjacent_iff, adjacent_rules]
QED

Theorem walks_contain_paths:
  ∀g vs. walk g vs ⇒
         ∃vs'. path g vs' ∧ HD vs' = HD vs ∧ LAST vs' = LAST vs ∧
               LENGTH vs' ≤ LENGTH vs
Proof
  simp[walk_def, path_def] >> Induct_on ‘vs’ >> simp[] >> rpt strip_tac >>
  rename [‘LAST (v1::vs)’] >> Cases_on ‘vs’ >> gs[]
  >- (qexists‘[v1]’ >> simp[]) >>
  gs[adjacent_iff, DISJ_IMP_THM, FORALL_AND_THM] >>
  rename [‘LAST _ = LAST (v2::vs)’] >>
 (* stage work *)
  rpt (first_x_assum $ drule_then strip_assume_tac) >>
  rename [‘ALL_DISTINCT vs'’] >>
  reverse $ Cases_on ‘MEM v1 vs'’
  >- (qexists ‘v1::vs'’ >> gvs[] >> rpt strip_tac >~
      [‘adjacent (v1::vs') a b’, ‘adjacent g a b’]
      >- (Cases_on ‘vs'’ >> gvs[adjacent_iff])
      >- PROVE_TAC [] (* v IN nodes g *)
      >- PROVE_TAC [] (* v IN nodes g *) >>
      rename [‘LAST (v1::vs') = LAST (HD vs'::vs)’] >>
      ‘LAST (v1::vs') = LAST vs'’ suffices_by simp[] >>
      qpat_x_assum ‘LAST vs' = LAST (_ :: _)’ kall_tac >>
      Cases_on ‘vs'’ >> gs[]) >>
  drule_then strip_assume_tac (iffLR MEM_SPLIT_APPEND_last) >>
  rename [‘vs' = p ++ [v1] ++ s’] >>
  gvs[ALL_DISTINCT_APPEND, DISJ_IMP_THM, FORALL_AND_THM] >>
  qexists ‘v1::s’ >> simp[] >>
  qpat_x_assum ‘LAST (_ ++ _ ++ _) = LAST _’ (assume_tac o SYM) >>
  simp[] >> rpt strip_tac >~
  [‘LAST (HD _ :: _) = LAST (p ++ [v1] ++ s)’,
   ‘LAST (v1 :: s) = LAST (p ++ [v1] ++ s)’]
  >- (simp[Excl "APPEND_ASSOC", GSYM APPEND_ASSOC])
  >- PROVE_TAC [] (* v IN nodes g *)
  >- PROVE_TAC [] (* v IN nodes g *) >>
  first_x_assum irule >> REWRITE_TAC[GSYM APPEND_ASSOC] >>
  irule adjacent_append2 >> simp[]
QED

(* ----------------------------------------------------------------------
    r-partite graphs and (in particular) bipartite graphs [2, p.17]
   ---------------------------------------------------------------------- *)

Overload V[local] = “nodes (g :fsgraph)”
Overload E[local] = “fsgedges (g :fsgraph)”

Theorem fsgraph_valid :
    !g n1 n2. {n1;n2} IN E ==> n1 IN V /\ n2 IN V /\ n1 <> n2
Proof
    rpt GEN_TAC
 >> DISCH_THEN (STRIP_ASSUME_TAC o MATCH_MP alledges_valid)
 >> ASM_SET_TAC []
QED

(* r-partite graphs [2, p.17]

   NOTE: ‘partitions’ requires that each partiton must be non-empty. This is not
   explicitly mentioned in the textbook but seems reasonable.
 *)
Definition partite_def :
    partite r (g :fsgraph) <=>
      ?v. v partitions (nodes g) /\ CARD v = r /\
          !n1 n2. {n1;n2} IN fsgedges g ==> part v n1 <> part v n2
End

(* "Instead of '2-partite' one usually says bipartite." *)
Overload bipartite = “partite 2”

Theorem bipartite_def :
    !g. bipartite (g :fsgraph) <=>
        ?A B. DISJOINT A B /\ A <> {} /\ B <> {} /\ A UNION B = nodes g /\
              !n1 n2. {n1;n2} IN fsgedges g ==>
                      (n1 IN A /\ n2 IN B) \/ (n1 IN B /\ n2 IN A)
Proof
    rw [partite_def]
 >> EQ_TAC >> simp []
 >- (STRIP_TAC \\
    ‘FINITE V’ by rw [] \\
    ‘FINITE v’ by PROVE_TAC [partitions_FINITE] \\
     fs [CARDEQ2] >> rename1 ‘v = {A; B}’ >> gvs [] \\
     qexistsl_tac [‘A’, ‘B’] \\
     CONJ_ASM1_TAC (* DISJOINT A B *)
     >- (MATCH_MP_TAC partitions_DISJOINT \\
         qexistsl_tac [‘{A;B}’, ‘V’] >> rw []) \\
     CONJ_TAC (* A <> {} *) >- fs [partitions_PAIR_DISJOINT] \\
     CONJ_TAC (* B <> {} *) >- fs [partitions_PAIR_DISJOINT] \\
     CONJ_ASM1_TAC (* A UNION B = V *)
     >- (Q.PAT_X_ASSUM ‘{A;B} partitions V’ (MP_TAC o MATCH_MP partitions_covers) \\
         SET_TAC []) \\
     rpt STRIP_TAC \\
    ‘n1 IN V /\ n2 IN V /\ n1 <> n2’ by PROVE_TAC [fsgraph_valid] \\
     Q.PAT_X_ASSUM ‘!n1 n2. P’ (MP_TAC o Q.SPECL [‘n1’, ‘n2’]) >> rw [] \\
     Cases_on ‘n1 IN A’
     >- (DISJ1_TAC >> rw [] (* goal: n2 IN B *) \\
         Know ‘A = part {A; B} n1’
         >- (MATCH_MP_TAC part_unique \\
             Q.EXISTS_TAC ‘V’ >> rw []) \\
         DISCH_THEN (fs o wrap o SYM) \\
         Cases_on ‘n2 IN A’
         >- (Know ‘A = part {A; B} n2’
             >- (MATCH_MP_TAC part_unique \\
                 Q.EXISTS_TAC ‘V’ >> rw []) \\
             DISCH_THEN (fs o wrap o SYM)) \\
         ASM_SET_TAC []) \\
     simp [] \\
     CONJ_ASM1_TAC >- ASM_SET_TAC [] \\
     Know ‘B = part {A; B} n1’
     >- (MATCH_MP_TAC part_unique \\
         Q.EXISTS_TAC ‘V’ >> rw []) \\
     DISCH_THEN (fs o wrap o SYM) \\
     Cases_on ‘n2 IN B’
     >- (Know ‘B = part {A; B} n2’
         >- (MATCH_MP_TAC part_unique \\
             Q.EXISTS_TAC ‘V’ >> rw []) \\
         DISCH_THEN (fs o wrap o SYM)) \\
     ASM_SET_TAC [])
 >> STRIP_TAC
 >> Q.EXISTS_TAC ‘{A; B}’
 >> CONJ_ASM1_TAC (* {A; B} partitions V *)
 >- (rw [partitions_PAIR_DISJOINT] >- art [] \\
     rw [Once DISJOINT_SYM])
 >> CONJ_TAC
 >- (rw [CARDEQ2] \\
     qexistsl_tac [‘A’, ‘B’] >> art [] \\
     CCONTR_TAC >> fs [DISJOINT_EMPTY_REFL_RWT])
 >> rpt STRIP_TAC
 >> ‘n1 IN V /\ n2 IN V /\ n1 <> n2’ by PROVE_TAC [fsgraph_valid]
 >> Q.PAT_X_ASSUM ‘!n1 n2. P’ (MP_TAC o Q.SPECL [‘n1’, ‘n2’]) >> rw []
 >| [ (* goal 1 (of 2) *)
      CCONTR_TAC >> fs [] \\
      Know ‘A = part {A; B} n1’
      >- (MATCH_MP_TAC part_unique \\
          Q.EXISTS_TAC ‘V’ >> rw []) \\
      DISCH_THEN (fs o wrap o SYM) \\
      Know ‘B = part {A; B} n2’
      >- (MATCH_MP_TAC part_unique \\
          Q.EXISTS_TAC ‘V’ >> rw []) \\
      DISCH_THEN (fs o wrap o SYM),
      (* goal 2 (of 2) *)
      CCONTR_TAC >> fs [] \\
      Know ‘B = part {A; B} n1’
      >- (MATCH_MP_TAC part_unique \\
          Q.EXISTS_TAC ‘V’ >> rw []) \\
      DISCH_THEN (fs o wrap o SYM) \\
      Know ‘A = part {A; B} n2’
      >- (MATCH_MP_TAC part_unique \\
          Q.EXISTS_TAC ‘V’ >> rw []) \\
      DISCH_THEN (fs o wrap o SYM) ]
QED

Theorem bipartite_alt :
    !g. bipartite (g :fsgraph) <=>
        ?A B. DISJOINT A B /\ A <> {} /\ B <> {} /\ A UNION B = nodes g /\
              !e. e IN fsgedges g ==> ?n1 n2. e = {n1; n2} /\ n1 IN A /\ n2 IN B
Proof
    rw [bipartite_def]
 >> EQ_TAC >> STRIP_TAC
 >| [ (* goal 1 (of 2) *)
      qexistsl_tac [‘A’, ‘B’] >> rw [] \\
      MP_TAC (Q.SPEC ‘g’ alledges_valid) >> rw [] \\
      Q.PAT_X_ASSUM ‘!n1 n2. P’ (MP_TAC o Q.SPECL [‘a’, ‘b’]) >> rw []
      >- (qexistsl_tac [‘a’, ‘b’] >> art []) \\
      qexistsl_tac [‘b’, ‘a’] >> art [] \\
      rw [INSERT2_lemma],
      (* goal 2 (of 2) *)
      qexistsl_tac [‘A’, ‘B’] >> rw [] \\
      Q.PAT_X_ASSUM ‘!e. P’ (MP_TAC o Q.SPEC ‘{n1; n2}’) >> rw [] \\
      gvs [INSERT2_lemma] ]
QED

val _ = export_theory();
val _ = html_theory "fsgraph";

(* References:

   [1] Harris, J., Hirst, J.L., Mossinghoff, M.: Combinatorics and Graph Theory.
       2nd Edition. Springer Science & Business Media (2008).
   [2] Diestel, R.: Graph Theory, 5th Electronic Edition. Springer-Verlag, Berlin (2017).
 *)
