open HolKernel Parse boolLib bossLib;

open arithmeticTheory pairTheory listTheory pred_setTheory sortingTheory hurdUtils
     topologyTheory;

open genericGraphTheory;

val _ = new_theory "fsgraph";

Type fsgraph[pp] = “:(α,finiteG,noSL) udulgraph”
Overload fsgedges = “udedges : α fsgraph -> α set set”

Theorem adjacent_fsg:
  adjacent (g : α fsgraph) a b ⇔ {a;b} ∈ fsgedges g
Proof
  simp[udedges_thm] >> iff_tac >> rw[] >> gvs[INSERT2_lemma] >>
  metis_tac[adjacent_SYM]
QED

Definition fsgAddNode_def :
  fsgAddNode n (g :'a fsgraph) = addNode n () g
End

Theorem nodes_fsgAddNode[simp] :
    nodes (fsgAddNode n g) = n INSERT nodes g
Proof
    rw [fsgAddNode_def]
QED

Definition fsgAddEdge_def :
  fsgAddEdge x y (g :'a fsgraph) = addUDEdge x y () g
End

Theorem nodes_fsgAddEdge[simp] :
    !x y g. x IN nodes g /\ y IN nodes g ==> nodes (fsgAddEdge x y g) = nodes g
Proof
    rw [fsgAddEdge_def]
 >> ASM_SET_TAC []
QED

Definition fsgAddEdges_def:
  fsgAddEdges (es0: α set set) (g:α fsgraph) =
  let
    es = { (m,n) | m ≠ n ∧ m ∈ nodes g ∧ n ∈ nodes g ∧ {m;n} ∈ es0 }
  in
    ITSET (λ(m,n) g. addUDEdge m n () g) es g
End

Definition valid_edges_def:
  valid_edges es s ⇔ ∀e. e ∈ es ⇒ e ⊆ s ∧ FINITE e ∧ CARD e = 2
End

Theorem fsgedges_emptyG[simp]:
  fsgedges emptyG = ∅
Proof
  simp[udedges_def]
QED

Theorem fsgedges_addNode[simp]:
  fsgedges (addNode n u g) = fsgedges g
Proof
  simp[]
QED

Theorem fsgedges_fsgAddNode[simp]:
  fsgedges (fsgAddNode n g) = fsgedges g
Proof
  simp[fsgAddNode_def]
QED

Theorem nodes_fsgAddEdges[simp]:
  nodes (fsgAddEdges es g) = nodes g
Proof
  simp[fsgAddEdges_def] >>
  qmatch_abbrev_tac ‘nodes (ITSET _ A g) = nodes g’ >>
  ‘FINITE A’
    by (irule SUBSET_FINITE >> qexists ‘nodes g × nodes g’ >>
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
  {{m;n} | m ∈ nodes g ∧ n ∈ nodes g ∧ {m;n} ∈ es ∧ m ≠ n} ∪ fsgedges g
Proof
  simp[fsgAddEdges_def, udedges_thm, adjacent_def] >>
  qabbrev_tac ‘A = {(m,n) | m ≠ n ∧ m ∈ nodes g ∧ n ∈ nodes g ∧ {m;n} ∈ es}’ >>
  ‘FINITE A’
    by (irule SUBSET_FINITE >> qexists ‘nodes g × nodes g’ >>
        simp[SUBSET_DEF, Abbr‘A’, PULL_EXISTS]) >>
  ‘∀m n. (m,n) ∈ A ⇒ m ≠ n’ by simp[Abbr‘A’, PULL_EXISTS] >>
  ‘∀m n. (m,n) ∈ A ⇒ m ∈ nodes g ∧ n ∈ nodes g’
    by (qunabbrev_tac ‘A’ >> simp_tac (srw_ss()) []) >>
  drule_then drule edges_ITSET_addUDEdge_udul >> simp[] >> gvs[] >>
  disch_then kall_tac >>
  qunabbrev_tac ‘A’ >>
  simp_tac (srw_ss()) [Once EXTENSION, FORALL_PROD] >>
  rpt (pop_assum kall_tac) >> gen_tac >> iff_tac >> rw[] >>~-
  ([‘{a;b} ∈ es’], dsimp[] >> rpt disj1_tac >>
                   first_assum $ irule_at (Pat ‘{_; _} ∈ es’) >> simp[] >>
                   simp[INSERT2_lemma]) >>
  metis_tac[]
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
  simp[udedges_thm, adjacent_def, PULL_EXISTS, SF CONJ_ss] >> rw[] >>
  irule incident_SUBSET_nodes >> first_assum $ irule_at Any >> simp[]
QED

Theorem FINITE_fsgedges[simp]:
  FINITE (fsgedges (g : α fsgraph))
Proof
  irule SUBSET_FINITE >> qexists ‘POW (nodes g)’ >> simp[] >>
  rw[SUBSET_DEF, FORALL_PROD, IN_POW] >> metis_tac[fsgincident_SUBSET_nodes]
QED

Theorem fsgraph_decomposition:
  ∀g. g = emptyG ∨
      ∃n es g0 : α fsgraph.
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
  >- (simp[ulabgraph_component_equality] >>
      simp[adjacent_def] >> simp[EXISTS_PROD, INSERT2_lemma] >>
      rw[EQ_IMP_THM]>>
      rename [‘(m,p,()) ∈ edges g’] >>
      ‘m ≠ p’ by (strip_tac >> gvs[]) >>
      ‘m ∈ nodes g ∧ p ∈ nodes g’
        by (strip_tac >> irule incident_SUBSET_nodes >> simp[EXISTS_PROD] >>
            metis_tac[edges_SYM]) >> simp[] >>
      metis_tac[edges_SYM]) >~
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

Definition remove_fsedge_def:
  remove_fsedge e (g:α fsgraph) =
  let es = { (m,n,()) | e = {m;n} ∧ m ≠ n }
  in
    ITSET removeEdge es g
End

Theorem nodes_remove_fsedge[simp]:
  nodes (remove_fsedge e g) = nodes g
Proof
  simp[remove_fsedge_def] >>
  reverse $ Cases_on ‘FINITE e’
  >- (‘∀a b. e ≠ {a;b}’ by (rpt strip_tac >> gvs[]) >> simp[]) >>
  Cases_on ‘CARD e = 2’ >> gvs[CARDEQ2]
  >- (rename [‘{a;b} = {_; _}’] >>
      ‘{(m,n,()) | {a;b} = {m;n} ∧ m ≠ n} = {(a,b,()); (b,a,())}’
        by (simp[Once EXTENSION, FORALL_PROD] >> simp[INSERT2_lemma] >>
            metis_tac[]) >>
      simp[removeEdge_LCOMM, COMMUTING_ITSET_RECURSES,
           DELETE_NON_ELEMENT_RWT])>>
  ‘{(m,n,()) | e = {m;n} ∧ m ≠ n} = ∅’ by ASM_SET_TAC[] >>
  simp[]
QED

Theorem alledges_valid:
  ∀g : α fsgraph. e ∈ fsgedges g ⇒
                  ∃a b. e = {a;b} ∧ a ∈ nodes g ∧ b ∈ nodes g ∧ a ≠ b
Proof
  Induct_on ‘g’ using fsg_induction >> simp[] >> strip_tac
  >- (gs[valid_edges_def] >> rpt (first_x_assum $ drule_then strip_assume_tac)>>
      gvs[CARDEQ2] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem fsgedges_remove_fsedge[simp]:
  fsgedges (remove_fsedge e g) = fsgedges g DELETE e
Proof
  simp[remove_fsedge_def] >>
  reverse $ Cases_on ‘FINITE e’
  >- (‘∀a b. e ≠ {a;b}’ by (rpt strip_tac >> gvs[]) >> simp[] >>
      irule (GSYM $ iffLR DELETE_NON_ELEMENT) >> strip_tac >>
      drule alledges_valid >> simp[]) >>
  Cases_on ‘CARD e = 2’ >> gvs[CARDEQ2]
  >- (rename [‘a ≠ b’, ‘{a;b} = {_; _}’] >>
      ‘{(m,n,()) | {a;b} = {m;n} ∧ m ≠ n} = {(a,b,()); (b,a,())}’
        by (simp[Once EXTENSION, INSERT2_lemma] >> metis_tac[]) >>
      simp[COMMUTING_ITSET_RECURSES, removeEdge_LCOMM, DELETE_NON_ELEMENT_RWT]>>
      simp[udedges_def, edges_removeEdge] >>
      simp[Once EXTENSION] >> gen_tac >> iff_tac >>
      simp[PULL_EXISTS, INSERT2_lemma, SF CONJ_ss] >> metis_tac[]) >>
  ‘{(m,n,()) | e = {m;n} ∧ m ≠ n} = ∅’ by ASM_SET_TAC[] >> simp[] >>
  irule (GSYM $ iffLR DELETE_NON_ELEMENT) >> strip_tac>>
  drule alledges_valid >> simp[]
QED

Theorem fsgraph_component_equality:
  (g1 : α fsgraph = g2) ⇔ nodes g1 = nodes g2 ∧ fsgedges g1 = fsgedges g2
Proof
  simp[gengraph_component_equality,udedges_def]>> iff_tac >> rw[] >~
  [‘nlabelfun _ = nlabelfun _’] >- simp[FUN_EQ_THM] >>
  qpat_x_assum ‘GSPEC _ = GSPEC _’ mp_tac >>
  ONCE_REWRITE_TAC [EXTENSION] >> simp[FORALL_PROD] >>
  rw[EQ_IMP_THM, PULL_EXISTS, FORALL_AND_THM] >>
  first_x_assum drule >> simp[INSERT2_lemma] >> rw[] >> simp[] >>
  metis_tac[edges_SYM]
QED

Definition fsgsize_def:
  fsgsize (g : α fsgraph) = CARD (fsgedges g)
End

Theorem fsgsize_empty[simp]:
  fsgsize emptyG = 0
Proof
  simp[fsgsize_def]
QED

Theorem fsgsize_remove_fsedge[simp] :
    e IN fsgedges g ==> fsgsize (remove_fsedge e g) = fsgsize g - 1
Proof
    rw [fsgsize_def, CARD_DELETE]
QED

Theorem fsgedges_members :
    !g x y. {x;y} IN fsgedges g ==> x <> y /\ x IN nodes g /\ y IN nodes g
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> POP_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP alledges_valid))
 >> Cases_on ‘x = a’
 >- (Q.PAT_X_ASSUM ‘{x;y} = {a;b}’ MP_TAC \\
     rw [Once EXTENSION] >> METIS_TAC [])
 >> Cases_on ‘x = b’
 >- (Q.PAT_X_ASSUM ‘{x;y} = {a;b}’ MP_TAC \\
     rw [Once EXTENSION] >> METIS_TAC [])
 >> Q.PAT_X_ASSUM ‘{x;y} = {a;b}’ MP_TAC
 >> rw [Once EXTENSION]
 >> METIS_TAC []
QED

Theorem fsgedges_fsgAddEdge[simp] :
    a <> b /\ a IN nodes g /\ b IN nodes g ==>
    fsgedges (fsgAddEdge a b g) = {a;b} INSERT fsgedges g
Proof
    rw [fsgAddEdge_def, udedges_thm]
 >> rw [Once EXTENSION]
 >> METIS_TAC []
QED

Theorem fsgAddEdge_remove_fsedge[simp] :
    {x; y} IN fsgedges g ==> fsgAddEdge x y (remove_fsedge {x;y} g) = g
Proof
    STRIP_TAC
 >> ‘x <> y /\ x IN nodes g /\ y IN nodes g’ by PROVE_TAC [fsgedges_members]
 >> rw [fsgraph_component_equality]
QED

Definition fsgAddNodes_def :
  fsgAddNodes N g = ITSET fsgAddNode N g
End

Theorem nodes_fsgAddNodes[simp] :
    !g N. FINITE N ==> nodes (fsgAddNodes N g) = N UNION nodes g
Proof
    Q.X_GEN_TAC ‘g’
 >> simp [fsgAddNodes_def]
 >> Induct using FINITE_INDUCT >> simp [fsgAddNode_def]
 >> rpt STRIP_TAC
 >> Suff ‘ITSET fsgAddNode (e INSERT N) g =
          fsgAddNode e (ITSET fsgAddNode (N DELETE e) g)’
 >- (‘N DELETE e = N’ by PROVE_TAC [DELETE_NON_ELEMENT] >> POP_ORW \\
     rw [] >> SET_TAC [])
 >> MATCH_MP_TAC COMMUTING_ITSET_RECURSES
 >> rw [fsgraph_component_equality] >> SET_TAC []
QED

Theorem fsgedges_fsgAddNodes[simp] :
    !g N. FINITE N ==> fsgedges (fsgAddNodes N g) = fsgedges g
Proof
    Q.X_GEN_TAC ‘g’
 >> simp [fsgAddNodes_def]
 >> Induct using FINITE_INDUCT >> simp [fsgAddNode_def]
 >> rpt STRIP_TAC
 >> Suff ‘ITSET fsgAddNode (e INSERT N) g =
          fsgAddNode e (ITSET fsgAddNode (N DELETE e) g)’
 >- (‘N DELETE e = N’ by PROVE_TAC [DELETE_NON_ELEMENT] >> POP_ORW \\
     rw [])
 >> MATCH_MP_TAC COMMUTING_ITSET_RECURSES
 >> rw [fsgraph_component_equality] >> SET_TAC []
QED

Theorem fsgraph_edge_decomposition:
  !g. fsgsize (g :'a fsgraph) = 0 \/
      ?x y g0.
        x <> y /\ {x; y} SUBSET nodes g0 /\
        {x; y} NOTIN fsgedges g0 /\ g = fsgAddEdge x y g0 /\
        fsgsize g = fsgsize g0 + 1
Proof
    rpt STRIP_TAC
 >> Cases_on ‘fsgsize g = 0’ >- rw []
 >> DISJ2_TAC
 >> ‘0 < fsgsize g’ by rw []
 >> ‘fsgedges g <> {}’ by fs [CARD_EQ_0, fsgsize_def]
 >> ‘?e. e IN fsgedges g’ by METIS_TAC [MEMBER_NOT_EMPTY]
 >> ‘?a b. e = {a; b} /\ a IN nodes g /\ b IN nodes g /\ a <> b’
      by METIS_TAC [alledges_valid]
 >> qexistsl_tac [‘a’, ‘b’, ‘remove_fsedge {a;b} g’] >> fs []
QED

Theorem fsg_edge_induction :
  !g P. P (fsgAddNodes (nodes g) emptyG) /\
        (!g0 x y. nodes g0 = nodes g /\
                  x <> y /\ {x; y} SUBSET nodes g /\ {x; y} NOTIN fsgedges g0 /\
                  P g0 ==> P (fsgAddEdge x y g0)) ==> P g
Proof
    rpt STRIP_TAC
 >> Induct_on ‘fsgsize g’
 >- (rw [] \\
     Suff ‘fsgAddNodes (nodes g) emptyG = g’ >- DISCH_THEN (fs o wrap) \\
     Q.PAT_X_ASSUM ‘fsgsize g = 0’ MP_TAC >> KILL_TAC \\
     rw [fsgsize_def, udul_component_equality])
 >> rpt STRIP_TAC
 >> qspec_then ‘g’ strip_assume_tac fsgraph_edge_decomposition
 >> fs []
QED

(* vertices not even in the graph at all have degree 0 *)
Definition degree_def:
  degree (g: α fsgraph) v = CARD { e | e ∈ fsgedges g ∧ v ∈ e }
End

Definition maxdegree_def:
  maxdegree (g : α fsgraph) = MAX_SET (IMAGE (degree g) (nodes g))
End

Overload "Δ" = “maxdegree”

Definition mindegree_def:
  mindegree (g : α fsgraph) = MIN_SET (IMAGE (degree g) (nodes g))
End
Overload "δ" = “mindegree”

Theorem degree_sequence_exists:
  ∀g : α fsgraph.
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
          by (simp[udedges_thm, PULL_EXISTS] >>
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
        gs[udedges_thm] >> first_x_assum drule >> strip_tac >> gvs[] >>
        metis_tac[adjacent_members]) >>
  simp[SUM_IMAGE_ADD] >>
  ‘es ∩ fsgedges g = ∅’ by (simp[udedges_thm, Once EXTENSION] >>
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
  ∀g: α fsgraph. EVEN (CARD { n | ODD (degree g n) })
Proof
  gen_tac >> simp[arithmeticTheory.EVEN_ODD] >>
  ‘{n | ODD (degree g n) } = {n | n ∈ nodes g ∧ ODD (degree g n)}’
    by (simp[EXTENSION] >> qx_gen_tac ‘n’ >> iff_tac >> simp[]>>
        simp[degree_def] >> CCONTR_TAC >> gvs[] >>
        ‘{ e | e ∈ fsgedges g ∧ n ∈ e} = ∅’
          suffices_by (strip_tac >> gvs[]) >>
        simp[EXTENSION] >> qx_gen_tac ‘e’ >> simp[udedges_thm] >>
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

val _ = export_theory();
