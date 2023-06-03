open HolKernel Parse boolLib bossLib;

open gfgTheory genericGraphTheory
open transferTheory sptreeTheory
open pairTheory pred_setTheory listTheory

val _ = new_theory "graphTransfer";

Definition fromConcrete_def:
  fromConcrete (g:('nodei,'edgei) gfg): (num, 'nodei, 'edgei) fdirgraph =
  foldi (λn edges G. FOLDL (λG (ei, dest). genericGraph$addEdge n dest ei G)
                           G
                           edges)
        0
        (foldi genericGraph$addNode 0 emptyG g.nodeInfo)
        g.followers
End

Definition CGR_def:
  CGR c a <=> a = fromConcrete c /\ wfg c
End

Theorem CGR_runique:
  right_unique CGR
Proof
  simp[right_unique_def, CGR_def]
QED

Theorem RDOM_CGR[simp]:
  RDOM CGR = wfg
Proof
  simp[relationTheory.RDOM_DEF, FUN_EQ_THM, CGR_def]
QED

Theorem domain_toAList:
  domain m = set $ MAP FST (toAList m)
Proof
  simp[EXTENSION, MEM_MAP, EXISTS_PROD, MEM_toAList,
       domain_lookup]
QED

Theorem FOLDL_addEdge:
  ∀G0.
    FOLDL (λG (ei,dest). addEdge src dest ei G) (G0:(num,α,β)fdirgraph) eil =
    addEdges {(src,dest,ei) | MEM (ei,dest) eil} G0
Proof
  Induct_on ‘eil’ >> simp[FORALL_PROD] >> rw[] >>
  ‘{(src,dest,ei) | MEM (ei,dest) eil} = IMAGE (λ(ei,d). (src,d,ei)) (set eil)’
    by (simp[EXTENSION, EXISTS_PROD] >> metis_tac[]) >>
  simp[addEdges_addEdge_fdirG] >> AP_THM_TAC >> AP_TERM_TAC >>
  simp[EXTENSION, EXISTS_PROD, PULL_EXISTS] >> metis_tac[]
QED

Definition emap_edges_def:
  emap_edges emap =
  { (m,n,l) | ∃eil. lookup m emap = SOME eil ∧ MEM (l,n) eil }
End

Theorem FINITE_emap_edges[simp]:
  FINITE (emap_edges emap)
Proof
  simp[emap_edges_def, domain_toAList, GSYM ALOOKUP_toAList] >>
  Q.SPEC_TAC (‘toAList emap’, ‘eal’) >> gen_tac >>
  irule SUBSET_FINITE >>
  qexists‘set (MAP FST eal) × set (MAP (λ(x,y). (y,x)) (FLAT (MAP SND eal)))’ >>
  simp[SUBSET_DEF, MEM_MAP, MEM_FLAT, PULL_EXISTS, FORALL_PROD, EXISTS_PROD] >>
  metis_tac[alistTheory.ALOOKUP_MEM]
QED

Theorem emap_edges_INSERT_NIL[simp]:
  emap_edges (insert n [] emap) = emap_edges (delete n emap)
Proof
  simp[emap_edges_def, lookup_insert, AllCaseEqs(), SF DNF_ss, lookup_delete]
QED

Theorem emap_edges_toAList:
  emap_edges emap =
  { (m,n,l) | ∃ei. ALOOKUP (toAList emap) m = SOME ei ∧ MEM (l,n) ei }
Proof
  simp[emap_edges_def, domain_toAList, GSYM ALOOKUP_toAList,
       MEM_MAP]
QED

Theorem foldi_addEdges:
  foldi (λn edges G.
           FOLDL (λG (ei,dest). genericGraph$addEdge n dest ei G) G edges) 0
        (G0  : (num,β,γ) fdirgraph) emap =
  addEdges (emap_edges emap) G0
Proof
  simp[foldi_FOLDR_toAList, emap_edges_toAList] >>
  ‘ALL_DISTINCT (MAP FST (toAList emap))’
    by simp[sptreeTheory.ALL_DISTINCT_MAP_FST_toAList] >> pop_assum mp_tac >>
  Q.SPEC_TAC (‘toAList emap’, ‘eal’) >>
  Induct >>
  simp[FORALL_PROD, MEM_MAP, PULL_EXISTS, EXISTS_PROD, AllCaseEqs()] >>
  simp[SF DNF_ss, SF CONJ_ss] >> qx_genl_tac [‘src’, ‘ei’] >>
  simp[FOLDL_addEdge] >> pop_assum kall_tac >> strip_tac >>
  qmatch_abbrev_tac ‘addEdges es1 (addEdges es2 _) = _’ >>
  ‘FINITE es1 ∧ FINITE es2’
    by (simp[Abbr‘es1’, Abbr‘es2’] >> conj_tac >~
        [‘ALOOKUP eal _ = SOME _’]
        >- (irule SUBSET_FINITE >>
            qexists ‘set (MAP FST eal) ×
                     set (MAP (λ(x,y). (y,x)) (FLAT (MAP SND eal)))’ >>
            simp[SUBSET_DEF, MEM_MAP, PULL_EXISTS, EXISTS_PROD, MEM_FLAT] >>
            rw[] >> drule alistTheory.ALOOKUP_MEM >> metis_tac[]) >>
        rename [‘MEM _ eil’, ‘(src,_,_)’] >>
        ‘{(src,dest,ei) | MEM (ei,dest) eil} =
         IMAGE (λ(ei,d). (src,d,ei)) (set eil)’
          by (simp[EXTENSION, EXISTS_PROD] >> metis_tac[]) >>
        simp[]) >>
  simp[addEdges_addEdges_fdirG] >> AP_THM_TAC >> AP_TERM_TAC >>
  simp[EXTENSION, Abbr‘es1’, Abbr‘es2’, PULL_EXISTS, EXISTS_PROD] >>
  qx_gen_tac ‘a’ >> eq_tac >> rw[] >>
  drule alistTheory.ALOOKUP_MEM >> metis_tac[]
QED

Theorem nodes_foldi_addNode:
  nodes (foldi addNode 0 G0 nmap) = nodes G0 ∪ domain nmap
Proof
  simp[foldi_FOLDR_toAList, domain_toAList] >>
  Q.SPEC_TAC (‘toAList nmap’, ‘nal’) >> Induct >> simp[FORALL_PROD] >>
  simp[EXTENSION, AC DISJ_COMM DISJ_ASSOC]
QED

Theorem nlabelfun_foldi_addNode:
  nlabelfun (foldi addNode 0 G0 nmap) = λn. case lookup n nmap of
                                              NONE => nlabelfun G0 n
                                            | SOME l => l
Proof
  simp[foldi_FOLDR_toAList, GSYM ALOOKUP_toAList] >>
  Q.SPEC_TAC (‘toAList nmap’, ‘nal’) >> Induct >>
  simp[SF ETA_ss, FORALL_PROD] >>
  rw[FUN_EQ_THM, AllCaseEqs(), SF CONJ_ss, combinTheory.APPLY_UPDATE_THM] >>
  rename [‘_ ∨ m = n ∨ _’] >> Cases_on ‘m = n’ >> simp[] >>
  Cases_on ‘ALOOKUP nal n’ >> simp[]
QED

Theorem edges_foldi_addNode[simp]:
  ∀n G0. edges (foldi addNode n G0 nmap) = edges G0
Proof
  Induct_on ‘nmap’ >> simp[foldi_def]
QED

Theorem nodes_fromConcrete:
  wfg cg ⇒
  nodes (fromConcrete cg) = domain cg.nodeInfo
Proof
  simp[fromConcrete_def, wfg_def, foldi_addEdges, nodes_foldi_addNode,
       nodes_addEdges_fdirg] >>
  strip_tac >> simp[Once EXTENSION, PULL_EXISTS] >> qx_gen_tac ‘n’ >>
  simp[EQ_IMP_THM, DISJ_IMP_THM, EXISTS_PROD] >>
  gs[emap_edges_def, wfAdjacency_def] >> rw[] >>
  metis_tac[domain_lookup]
QED

Theorem fromConcrete_addNodeN[simp]:
  wfg cg ⇒
  fromConcrete (addNodeN n l cg) = addNode n l (fromConcrete cg)
Proof
  rw[addNodeN_def, fromConcrete_def, foldi_addEdges, wfg_def] >>
  simp[gengraph_component_equality, nodes_addEdges_fdirg, nodes_foldi_addNode,
       nlabelfun_foldi_addNode, INSERT_UNION_EQ, edges_addEdges_fdirgraph,
       iffLR delete_fail] >>
  simp[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM, AllCaseEqs(), lookup_insert,
       SF CONJ_ss] >>
  rw[] >> BasicProvers.EVERY_CASE_TAC
QED

Theorem addNodeN_transfer:
  ((=) |==> (=) |==> CGR |==> CGR) addNodeN addNode
Proof
  simp[FUN_REL_def, CGR_def, addNodeN_preserves_wfg]
QED

Definition optAddEdge_def:
  optAddEdge src (ei,tgt) g0 =
  if src ∉ nodes g0 \/ tgt ∉ nodes g0 then NONE
  else
    SOME $ addEdge src tgt ei g0
End

Theorem nlabelfun_FOLDL_addEdge[local,simp]:
  ∀abG. nlabelfun (FOLDL (λG (ei,dest). addEdge src dest ei G) abG eis) =
        nlabelfun abG
Proof
  Induct_on ‘eis’ >> simp[FORALL_PROD]
QED

Theorem nlabelfun_foldi_addEdge[local,simp]:
  ∀i abG.
    nlabelfun
    (foldi
     (λn edges G. FOLDL (λG (ei,dest). addEdge n dest ei G) G edges)
     i
     abG
     spmap) = nlabelfun abG
Proof
  Induct_on ‘spmap’ >> simp[foldi_def]
QED


Theorem nlabelfun_fromConcrete:
  nlabelfun (fromConcrete G) =
  λn. if n ∈ domain G.nodeInfo then THE $ lookup n G.nodeInfo else ARB
Proof
  simp[fromConcrete_def] >>
  simp[foldi_FOLDR_toAList, GSYM ALOOKUP_toAList, domain_toAList, MEM_MAP,
       EXISTS_PROD] >>
  qspec_then ‘G.nodeInfo’ mp_tac ALL_DISTINCT_MAP_FST_toAList >>
  qspec_tac (‘toAList G.nodeInfo’, ‘al’) >> Induct >> simp[] >>
  simp[MEM_MAP, FORALL_PROD] >>
  rw[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >> rw[] >> metis_tac[]
QED

Theorem edges_FOLDL_src:
  ∀eil G0 : (α,β,γ)fdirgraph.
    edges (FOLDL (λG (ei,dest). addEdge src dest ei G) G0 eil) =
    {(src,tgt,ei) | tgt, ei | MEM (ei,tgt) eil } ∪ edges G0
Proof
  Induct >> simp[FORALL_PROD, edges_addEdge] >>
  simp[EXTENSION] >> metis_tac[]
QED

Theorem edges_FOLDR_alist:
  ∀alist (G0 : (α,β,γ)fdirgraph).
    ALL_DISTINCT (MAP FST alist) ⇒
    edges (FOLDR
             (λ(n,edges) G. FOLDL (λG (ei,dest). addEdge n dest ei G) G edges)
             G0
             alist) =
    edges G0 ∪
    {(src,tgt,ei) | ∃eil. ALOOKUP alist src = SOME eil ∧ MEM (ei,tgt) eil }
Proof
  Induct >> simp[FORALL_PROD, MEM_MAP, edges_FOLDL_src] >> rw[] >>
  simp[EXTENSION, AllCaseEqs()] >> simp[FORALL_PROD] >>
  rpt gen_tac >> eq_tac >> rw[] >> simp[] >>
  drule alistTheory.ALOOKUP_MEM >> metis_tac[]
QED

Theorem edges_foldi_addNode[local]:
  ∀i g spmap. edges (foldi addNode i g spmap) = edges g
Proof
  Induct_on ‘spmap’ >> simp[]
QED

Theorem edges_fromConcrete:
  wfg cg ⇒
  edges (fromConcrete cg) = emap_edges cg.followers
Proof
  strip_tac >> simp[fromConcrete_def, emap_edges_toAList] >>
  qmatch_abbrev_tac ‘edges (foldi _ _ G0 _) = _’ >>
  simp[foldi_FOLDR_toAList, MEM_MAP, EXISTS_PROD] >>
  qspec_then ‘cg.followers’ mp_tac ALL_DISTINCT_MAP_FST_toAList >>
  qspec_tac (‘toAList cg.followers’, ‘al’) >>
  simp[edges_FOLDR_alist] >>
  simp[Abbr‘G0’, edges_foldi_addNode]
QED

Theorem emap_edges_insert_cons:
  lookup src m = SOME eis ⇒
  emap_edges (insert src ((l,tgt) :: eis) m) =
  (src,tgt,l) INSERT emap_edges m
Proof
  simp[emap_edges_def, lookup_insert, EXTENSION, AllCaseEqs(), FORALL_PROD,
       RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> rw[] >>
  rename [‘s ≠ src’, ‘MEM (lab,t) _’] >> Cases_on ‘src = s’ >> simp[] >>
  Cases_on ‘t = tgt’ >> rw[] >> metis_tac[optionTheory.SOME_11]
QED

Theorem addEdge_fromConcrete:
  src ∈ domain G.nodeInfo ∧ tgt ∈ domain G.nodeInfo ∧ wfg G ⇒
  addEdge src tgt elab (fromConcrete G) =
  fromConcrete (THE $ addEdge src (elab,tgt) G)
Proof
  simp[gengraph_component_equality, nodes_fromConcrete, edges_addEdge] >>
  Cases_on ‘addEdge src (elab,tgt) G’
  >- (gs[addEdge_EQ_NONE] >> Cases_on ‘wfg G’ >> simp[] >>
      gs[wfg_def]) >>
  rename [‘addEdge _ (_,_) G0 = SOME G’] >> simp[] >> strip_tac >>
  ‘wfg G’ by metis_tac[addEdge_preserves_wfg] >>
  ‘domain G0.nodeInfo ∪ {src;tgt} = domain G0.nodeInfo’
    by (simp[EXTENSION] >> metis_tac[]) >>
  simp[nodes_fromConcrete] >>
  drule_then assume_tac addEdge_preserves_nodeInfo >>
  simp[nlabelfun_fromConcrete] >>
  simp[edges_fromConcrete] >>
  qpat_x_assum ‘addEdge src _ _ = SOME G’ mp_tac >>
  REWRITE_TAC[gfgTheory.addEdge_def] >> simp[AllCaseEqs()] >> rw[] >>
  simp[emap_edges_insert_cons, EXTENSION] >> metis_tac[]
QED

Theorem addEdgeN'_transfer:
  ((=) |==> (=) |==> CGR |==> OPTREL CGR) addEdge optAddEdge
Proof
  simp[FUN_REL_def, CGR_def, gfgTheory.addEdge_def, optAddEdge_def,
       FORALL_PROD, nodes_fromConcrete] >> rw[] >> gvs[] >>
  rename [‘lookup src g0.followers’, ‘lookup tgt g0.preds’] >>
  Cases_on ‘lookup src g0.followers’
  >- gs[wfg_def, lookup_NONE_domain] >>
  Cases_on ‘lookup tgt g0.preds’
  >- gs[wfg_def, lookup_NONE_domain] >>
  simp[CGR_def] >> rename [‘addEdge src tgt elab (fromConcrete G)’] >>
  qmatch_abbrev_tac ‘_ = fromConcrete G' /\ wfg G'’ >>
  ‘addEdge src (elab, tgt) G = SOME G'’
    by simp[gfgTheory.addEdge_def] >>
  drule_all_then assume_tac addEdge_preserves_wfg >> simp[] >>
  simp[addEdge_fromConcrete]
QED

Theorem addEdge_has_src_in_followers:
  addEdge s (l,t) G0 = SOME G ⇒
  ∃ei. lookup s G0.followers = SOME ei
Proof
  simp[gfgTheory.addEdge_def, AllCaseEqs(), PULL_EXISTS]
QED


Theorem FOLDR_addEdge:
  ∀G el.
    wfg G0 ∧ (∀e m. MEM e el ∧ m ∈ incident e ⇒ m ∈ nodes (fromConcrete G0)) ∧
    Abbrev(G = FOLDR (λ(m,n,l) g. THE (addEdge m (l,n) g)) G0 el) ⇒
    wfg G ∧ nodes (fromConcrete G) = nodes (fromConcrete G0) ∧
    edges (fromConcrete G) = set el ∪ edges (fromConcrete G0) ∧
    nlabelfun (fromConcrete G) = nlabelfun (fromConcrete G0)
Proof
  simp[markerTheory.Abbrev_def] >> Induct_on ‘el’ >> simp[] >>
  simp[Once FORALL_PROD, RIGHT_AND_OVER_OR, DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[Once FORALL_PROD, DISJ_IMP_THM, FORALL_AND_THM] >>
  rpt gen_tac >> strip_tac >>
  rename [‘addEdge src (l, tgt) _’] >> gvs[] >>
  first_x_assum $ drule_then strip_assume_tac >>
  qmatch_abbrev_tac ‘wfg (THE (addEdge src (l,tgt) G')) ∧ _’ >>
  Cases_on ‘addEdge src (l,tgt) G'’
  >- gs[addEdge_EQ_NONE, nodes_fromConcrete, wfg_def] >>
  rename [‘addEdge _ _ G' = SOME G’] >> simp[] >>
  ‘wfg G’ by metis_tac[addEdge_preserves_wfg] >>
  drule_then assume_tac addEdge_preserves_nodeInfo >>
  gs[nodes_fromConcrete] >>
  conj_tac
  >- (drule_then assume_tac addEdge_extends_followers >>
      drule_then strip_assume_tac addEdge_has_src_in_followers >>
      qabbrev_tac ‘OLDEDGES = edges (fromConcrete G0)’ >>
      gs[edges_fromConcrete, emap_edges_insert_cons, INSERT_UNION_EQ]) >>
  gs[nlabelfun_fromConcrete]
QED

Theorem CGR_surj:
  surj CGR
Proof
  simp[surj_def, CGR_def] >> ho_match_mp_tac fdirG_induction >> rw[]
  >- (qexists‘empty’ >>
      simp[fromConcrete_def, empty_def, sptreeTheory.foldi_def]) >>
  rename [‘fromConcrete cg’] >>
  ‘∃el. set el = es ∧ ALL_DISTINCT el’
    by metis_tac[SET_TO_LIST_INV, ALL_DISTINCT_SET_TO_LIST] >>
  qexists
    ‘FOLDR (λ(m,n,l) g. THE $ gfg$addEdge m (l,n) g) (addNodeN n l cg) el’ >>
  gvs[] >>
  qmatch_abbrev_tac ‘_ = _ ∧ wfg G’ >>
  simp[gengraph_component_equality, nodes_addEdges_fdirg,
       edges_addEdges_fdirgraph] >>
  qabbrev_tac ‘G1 = addNodeN n l cg’ >>
  ‘wfg G1’ by simp[addNodeN_preserves_wfg, Abbr‘G1’] >>
  ‘nodes (fromConcrete G1) = n INSERT nodes (fromConcrete cg) ∧
   edges (fromConcrete G1) = edges (fromConcrete cg) ∧
   nlabelfun (fromConcrete G1) = (nlabelfun (fromConcrete cg))⦇n ↦ l⦈’
    by simp[fromConcrete_addNodeN, Abbr‘G1’] >>
  drule_at (Pat ‘Abbrev _’) FOLDR_addEdge >> impl_tac
  >- (rw[] >> metis_tac[]) >> rw[] >>
  simp[Once EXTENSION, PULL_EXISTS] >> metis_tac[]
QED

val _ = export_theory();
