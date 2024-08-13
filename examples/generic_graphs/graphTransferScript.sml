open HolKernel Parse boolLib bossLib;

open gfgTheory genericGraphTheory
open transferTheory sptreeTheory
open pairTheory pred_setTheory listTheory
open bagTheory

val _ = new_theory "graphTransfer";

Definition emap_edges_def:
  emap_edges emap =
  λ(m,n,l). LENGTH
            (FILTER (λe. e = (l,n))
                    (case lookup m emap of SOME eil => eil | NONE => []))
End

Theorem domain_toAList = GSYM set_MAP_FST_toAList_domain

Theorem emap_edges_foldi:
  emap_edges emap =
  foldi (λn ins B. FOLDR (λ(i,tgt). BAG_INSERT (n, tgt, i)) B ins)
        0
        EMPTY_BAG
        emap
Proof
  simp[foldi_FOLDR_toAList, domain_toAList, emap_edges_def,
       GSYM ALOOKUP_toAList, FUN_EQ_THM, FORALL_PROD, EMPTY_BAG] >>
  ‘ALL_DISTINCT (MAP FST (toAList emap))’
    by simp[sptreeTheory.ALL_DISTINCT_MAP_FST_toAList] >> pop_assum mp_tac >>
  qspec_tac (‘toAList emap’, ‘eal’) >> Induct >>
  simp[EMPTY_BAG, FORALL_PROD, MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
  gvs[] >> rw[] >~
  [‘FILTER (λe. e = (i,tgt)) ins’, ‘FOLDR _ _ ins (src,tgt,i)’]
  >- (Induct_on ‘ins’ >> simp[]
      >- (last_x_assum (assume_tac o GSYM) >> simp[] >>
          gvs[SYM $ SRULE[]alistTheory.ALOOKUP_FAILS]) >>
      simp[FORALL_PROD] >> rw[]
      >- simp[BAG_INSERT] >>
      simp[BAG_INSERT] >> rw[]) >~
  [‘FOLDR _ (FOLDR _ (K 0) eal) ins' (src,tgt,i)’, ‘src' <> src’] >>
  Induct_on ‘ins'’ >> simp[FORALL_PROD, BAG_INSERT]
QED

Definition nfn_def[simp]:
  nfn 0 = INL () ∧
  nfn (SUC n) = INR n
End

Theorem nfn11[simp]:
  nfn x = nfn y ⇔ x = y
Proof
  Cases_on ‘x’ >> Cases_on ‘y’ >> simp[]
QED

Theorem nfn_ONTO:
  ∀un. ∃n. nfn n = un
Proof
  Cases >- (simp[] >> irule_at Any (cj 1 nfn_def)) >>
  irule_at Any $ cj 2 nfn_def
QED

Definition unfn_def[simp]:
  unfn (INL (u:unit)) = 0 ∧
  unfn (INR n) = SUC n
End

Theorem unfn_nfn[simp]:
  unfn (nfn n) = n ∧ nfn (unfn un) = un
Proof
  Cases_on ‘n’ >> Cases_on ‘un’ >> simp[]
QED

Theorem unfn_EQ[simp]:
  (unfn un = 0 ⇔ un = INL ()) ∧
  (unfn un = SUC m ⇔ un = INR m) ∧
  (nfn n = INL () ⇔ n = 0) ∧
  (nfn n = INR m ⇔ n = SUC m)
Proof
  Cases_on ‘n’ >> Cases_on ‘un’ >> simp[]
QED

Overload cAddEdges =
  “ITBAG (λ(src,tgt,i). genericGraph$addEdge (nfn src) (nfn tgt) i)”

Definition fromConcrete_def:
  fromConcrete (g:('nodei,'edgei) gfg): (unit, 'nodei, 'edgei) fdirgraph =
  cAddEdges (emap_edges g.followers)
            (foldi (genericGraph$addNode o nfn) 0 emptyG g.nodeInfo)
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

Theorem BAG_FILTER_UNION:
  BAG_FILTER (A ∪ B) b = BAG_MERGE (BAG_FILTER A b) (BAG_FILTER B b)
Proof
  simp[FUN_EQ_THM, BAG_FILTER_DEF, BAG_MERGE, IN_DEF] >> rw[] >> gvs[]
QED

Theorem BAG_FILTER_EMPTY[simp]:
  BAG_FILTER {} b = EMPTY_BAG
Proof
  simp[FUN_EQ_THM, BAG_FILTER_DEF, EMPTY_BAG]
QED

Definition nBAG_def[simp]:
  nBAG 0 e = EMPTY_BAG ∧
  nBAG (SUC n) e = BAG_INSERT e (nBAG n e)
End

Theorem nBAG_EQ_EMPTY[simp]:
  nBAG n e = EMPTY_BAG <=> n = 0
Proof
  Cases_on ‘n’ >> simp[]
QED

Theorem BAG_FILTER_SING:
  BAG_FILTER {e} b = nBAG (b e) e
Proof
  Induct_on ‘b e’ >> rw[]
  >- simp[BAG_FILTER_DEF, FUN_EQ_THM, EMPTY_BAG] >>
  qabbrev_tac ‘b0 = b - {| e |}’ >>
  qpat_x_assum ‘SUC _ = b e’ (assume_tac o SYM) >> simp[] >>
  ‘v = b0 e’ by simp[Abbr‘b0’, BAG_DIFF, BAG_INSERT, EMPTY_BAG] >>
  first_x_assum $ drule_then strip_assume_tac >>
  ‘b = BAG_UNION b0 {| e |}’
    by (simp[FUN_EQ_THM, Abbr‘b0’, BAG_UNION, BAG_DIFF, BAG_INSERT, EMPTY_BAG]>>
        rw[]) >>
  simp[BAG_FILTER_BAG_UNION, BAG_UNION_INSERT]
QED

Theorem FINITE_BAG_nBAG[simp]:
  FINITE_BAG (nBAG n e)
Proof
  Induct_on ‘n’ >> simp[]
QED

Theorem nBAG_APPLIED[simp]:
  nBAG n d e = if d = e then n else 0
Proof
  Induct_on ‘n’ >> simp[BAG_INSERT, EMPTY_BAG] >>
  Cases_on ‘d = e’ >> gvs[]
QED

Theorem FINITE_FILTER_FINITE_BAG:
  FINITE A ⇒ FINITE_BAG (BAG_FILTER A b)
Proof
  Induct_on ‘FINITE’ >> simp[] >>
  simp[Once INSERT_SING_UNION, BAG_FILTER_UNION, BAG_FILTER_SING]
QED

Theorem FINITE_emap_edges[simp]:
  FINITE_BAG (emap_edges emap)
Proof
  simp[emap_edges_def, domain_toAList, GSYM ALOOKUP_toAList] >>
  REWRITE_TAC[GSYM FINITE_SET_OF_BAG] >>
  Q.SPEC_TAC (‘toAList emap’, ‘eal’) >> gen_tac >>
  irule SUBSET_FINITE >>
  qexists‘set (MAP FST eal) × set (MAP (λ(x,y). (y,x)) (FLAT (MAP SND eal)))’ >>
  simp[SUBSET_DEF, MEM_MAP, MEM_FLAT, PULL_EXISTS, FORALL_PROD, EXISTS_PROD] >>
  simp[BAG_IN, BAG_INN, DECIDE “x >= 1 ⇔ x <> 0”, FILTER_EQ_NIL, EVERY_MEM] >>
  rpt gen_tac >> rename [‘ALOOKUP eal e’] >> Cases_on ‘ALOOKUP eal e’ >>
  simp[] >>
  metis_tac[alistTheory.ALOOKUP_MEM]
QED

Theorem emap_edges_INSERT_NIL[simp]:
  emap_edges (insert n [] emap) = emap_edges (delete n emap)
Proof
  simp[emap_edges_def, lookup_insert, AllCaseEqs(), SF DNF_ss, lookup_delete,
       FUN_EQ_THM, FORALL_PROD] >> rw[]
QED

Theorem BAG_IN_APPLIED:
  BAG_IN e B <=> 0 < B e
Proof
  simp[BAG_IN, BAG_INN]
QED

fun renameCases q = rename [q] >> Cases_on q

Theorem emap_edges_toAList:
  set (emap_edges emap) =
  { (m,n,l) | ∃ei. ALOOKUP (toAList emap) m = SOME ei ∧ MEM (l,n) ei }
Proof
  simp[emap_edges_def, domain_toAList, GSYM ALOOKUP_toAList,
       MEM_MAP, EXTENSION, FORALL_PROD, BAG_IN_APPLIED] >> rpt gen_tac >>
  renameCases ‘ALOOKUP (toAList emap) e’ >> simp[] >>
  rename [‘MEM (e,i) l’] >> pop_assum kall_tac >> Induct_on ‘l’ >> simp[] >>
  rw[]
QED

Theorem nodes_foldi_addNode:
  nodes (foldi (addNode o nfn) 0 G0 nmap) = nodes G0 ∪ IMAGE nfn (domain nmap)
Proof
  simp[foldi_FOLDR_toAList, domain_toAList] >>
  Q.SPEC_TAC (‘toAList nmap’, ‘nal’) >> Induct >> simp[FORALL_PROD] >>
  simp[EXTENSION, AC DISJ_COMM DISJ_ASSOC]
QED

Theorem nlabelfun_foldi_addNode:
  nlabelfun (foldi (addNode o nfn) 0 G0 nmap) =
  λun. case lookup (unfn un) nmap of NONE => nlabelfun G0 un
                                  | SOME l => l
Proof
  simp[foldi_FOLDR_toAList, GSYM ALOOKUP_toAList] >>
  Q.SPEC_TAC (‘toAList nmap’, ‘nal’) >> Induct >>
  simp[SF ETA_ss, FORALL_PROD] >>
  rw[FUN_EQ_THM, AllCaseEqs(), SF CONJ_ss, combinTheory.APPLY_UPDATE_THM] >>
  Cases_on ‘un’ >> simp[] >~
  [‘_ ∨ m = SUC n ∨ _’]
  >- (Cases_on ‘m = SUC n’ >> simp[] >> Cases_on ‘ALOOKUP nal (SUC n)’ >>
      simp[]) >>
  rename [‘_ ∨ m = n ∨ _’] >> Cases_on ‘m = n’ >> simp[] >>
  Cases_on ‘ALOOKUP nal n’ >> simp[]
QED

Theorem edges_foldi_addNode[simp]:
  ∀n G0. edgebag (foldi (addNode o nfn) n G0 nmap) = edgebag G0
Proof
  Induct_on ‘nmap’ >> simp[foldi_def]
QED

val fdirtyq = ty_antiq “:(unit,'el,'nl) fdirgraph”
Theorem cAddEdges_INSERT =
  Q.ISPEC ‘λ(m,n,l). addEdge (nfn m) (nfn n) l : ^fdirtyq -> ^fdirtyq’
   COMMUTING_ITBAG_RECURSES
  |> SRULE[FORALL_PROD, addEdge_LCOMM_fdirg]
  |> CONV_RULE (RENAME_VARS_CONV ["m", "n", "l", "G"])

Theorem nodes_cAddEdges:
  ∀b g:^fdirtyq.
    FINITE_BAG b ==>
    nodes (cAddEdges b g) = nodes g ∪ { nfn m | ∃n l. BAG_IN (m,n,l) b } ∪
                            { nfn n | ∃m l. BAG_IN (m,n,l) b }
Proof
  Induct_on ‘FINITE_BAG’ >> simp[FORALL_PROD, cAddEdges_INSERT] >>
  rpt strip_tac >> SET_TAC[]
QED

Theorem edgebag_cAddEdges:
  ∀b g:^fdirtyq.
    FINITE_BAG b ⇒
    edgebag (cAddEdges b g) =
    BAG_UNION (BAG_IMAGE (λ(m,n,l). DE {nfn m} {nfn n} l) b) (edgebag g)
Proof
  Induct_on ‘FINITE_BAG’ >>
  simp[cAddEdges_INSERT, FORALL_PROD, edgebag_addEdge, edge0_def,
       BAG_UNION_INSERT]
QED

Theorem nlabelfun_cAddEdges:
  ∀b g:^fdirtyq.
    FINITE_BAG b ⇒ nlabelfun (cAddEdges b g) = nlabelfun g
Proof
  Induct_on ‘FINITE_BAG’ >> simp[FORALL_PROD, cAddEdges_INSERT]
QED

Theorem BAG_IN_emap_edges:
  BAG_IN (m,n,l) (emap_edges em) ⇔
  ∃ins. lookup m em = SOME ins ∧ MEM (l,n) ins
Proof
  REWRITE_TAC[GSYM IN_SET_OF_BAG, emap_edges_toAList] >>
  simp[ALOOKUP_toAList]
QED

Theorem nodes_fromConcrete:
  wfg cg ⇒
  nodes (fromConcrete cg) = IMAGE nfn (domain cg.nodeInfo)
Proof
  simp[fromConcrete_def, wfg_def, nodes_foldi_addNode,
       nodes_addEdges_fdirg, nodes_cAddEdges, edgebag_cAddEdges] >>
  strip_tac >> simp[Once EXTENSION, PULL_EXISTS] >> qx_gen_tac ‘n’ >>
  simp[EQ_IMP_THM, DISJ_IMP_THM, EXISTS_PROD, PULL_EXISTS] >>
  simp[BAG_IN_emap_edges, PULL_EXISTS] >>
  gs[wfAdjacency_def] >>
  metis_tac[domain_lookup]
QED

Theorem fromConcrete_addNodeN[simp]:
  wfg cg ⇒
  fromConcrete (addNodeN n l cg) = addNode (nfn n) l (fromConcrete cg)
Proof
  rw[addNodeN_def, fromConcrete_def, wfg_def] >>
  simp[gengraph_component_equality, nodes_addEdges_fdirg, nodes_foldi_addNode,
       nlabelfun_foldi_addNode, INSERT_UNION_EQ, edges_addEdges_fdirgraph,
       iffLR delete_fail, nodes_cAddEdges, edgebag_cAddEdges,
       nlabelfun_cAddEdges] >>
  simp[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM, AllCaseEqs(), lookup_insert,
       SF CONJ_ss] >> Cases >> simp[] >>
  BasicProvers.EVERY_CASE_TAC >> metis_tac[]
QED

Theorem addNodeN_transfer:
  ((=) |==> (=) |==> CGR |==> CGR) addNodeN (addNode o nfn)
Proof
  simp[FUN_REL_def, CGR_def, addNodeN_preserves_wfg]
QED

Definition optAddEdge_def:
  optAddEdge src (ei,tgt) g0 =
  if src ∉ nodes g0 \/ tgt ∉ nodes g0 then NONE
  else
    SOME $ addEdge src tgt ei g0
End

Theorem nlabelfun_fromConcrete:
  nlabelfun (fromConcrete G) =
  λun. if unfn un ∈ domain G.nodeInfo then THE $ lookup (unfn un) G.nodeInfo
       else ARB
Proof
  simp[fromConcrete_def] >>
  simp[nlabelfun_cAddEdges, nlabelfun_foldi_addNode] >>
  simp[FUN_EQ_THM] >> Cases >> simp[] >>
  BasicProvers.EVERY_CASE_TAC >>
  gvs[lookup_NONE_domain, AllCaseEqs()] >>
  gvs[domain_lookup]
QED

Theorem edgebag_foldi_addNode[local]:
  ∀i g spmap. edgebag (foldi (addNode o nfn) i g spmap) = edgebag g
Proof
  Induct_on ‘spmap’ >> simp[]
QED

Theorem edgebag_fromConcrete:
  wfg cg ⇒
  edgebag (fromConcrete cg) =
  BAG_IMAGE (λ(m,n,l). DE {nfn m} {nfn n} l) (emap_edges cg.followers)
Proof
  strip_tac >> simp[fromConcrete_def, edgebag_cAddEdges]
QED

Theorem emap_edges_insert_cons:
  lookup src m = SOME eis ⇒
  emap_edges (insert src ((l,tgt) :: eis) m) =
  BAG_INSERT (src,tgt,l) (emap_edges m)
Proof
  simp[emap_edges_def, lookup_insert, FUN_EQ_THM, FORALL_PROD, BAG_INSERT] >>
  rw[] >> rename [‘COND (src' = src)’] >> Cases_on ‘src' = src’ >> simp[] >>
  gvs[] >> rename [‘COND (lab' = lab ∧ tgt' = tgt)’] >>
  Cases_on ‘lab' = lab’ >> gvs[] >> COND_CASES_TAC >> gvs[]
QED

Theorem addEdge_fromConcrete:
  src ∈ domain G.nodeInfo ∧ tgt ∈ domain G.nodeInfo ∧ wfg G ⇒
  addEdge (nfn src) (nfn tgt) elab (fromConcrete G) =
  fromConcrete (THE $ addEdge src (elab,tgt) G)
Proof
  simp[gengraph_component_equality, nodes_fromConcrete, nlabelfun_fromConcrete,
       edgebag_addEdge, edge0_def] >>
  Cases_on ‘addEdge src (elab,tgt) G’
  >- (gs[addEdge_EQ_NONE] >> Cases_on ‘wfg G’ >> simp[] >>
      gs[wfg_def]) >>
  rename [‘addEdge _ (_,_) G0 = SOME G’] >> simp[] >> strip_tac >>
  ‘wfg G’ by metis_tac[addEdge_preserves_wfg] >>
  simp[nodes_fromConcrete, edgebag_fromConcrete] >>
  drule_then assume_tac addEdge_preserves_nodeInfo >>
  rpt conj_tac >~
  [‘IMAGE nfn _ ∪ _ = IMAGE nfn _’]
  >- (simp[EXTENSION] >> Cases >> simp[] >> metis_tac[]) >~
  [‘BAG_INSERT _ _ = BAG_IMAGE _ _’]
  >- (qpat_x_assum ‘addEdge src _ _ = SOME G’ mp_tac >>
      REWRITE_TAC[gfgTheory.addEdge_def] >> simp[AllCaseEqs()] >> rw[] >>
      simp[emap_edges_insert_cons]) >>
  simp[FUN_EQ_THM]
QED

Theorem addEdgeN'_transfer:
  ((=) |==> (=) |==> CGR |==> OPTREL CGR) addEdge
    (λm (i,n). optAddEdge (nfn m) (i,nfn n))
Proof
  simp[FUN_REL_def, CGR_def, gfgTheory.addEdge_def, optAddEdge_def,
       FORALL_PROD, nodes_fromConcrete] >> rw[] >> gvs[] >>
  rename [‘lookup src g0.followers’, ‘lookup tgt g0.preds’] >>
  Cases_on ‘lookup src g0.followers’
  >- gs[wfg_def, lookup_NONE_domain] >>
  Cases_on ‘lookup tgt g0.preds’
  >- gs[wfg_def, lookup_NONE_domain] >>
  simp[CGR_def] >>
  rename [‘addEdge (nfn src) (nfn tgt) elab (fromConcrete G)’] >>
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

Theorem CGR_surj:
  surj CGR
Proof
  simp[surj_def, CGR_def] >> Induct using fdirgraph_induction >> gvs[]
  >- (qexists‘empty’ >>
      simp[fromConcrete_def, empty_def, sptreeTheory.foldi_def,
           emap_edges_foldi])
  >- (rename [‘addNode n nl _ = fromConcrete _’] >>
      ‘∃un. n = nfn un’ by metis_tac[nfn_ONTO] >> gvs[] >>
      irule_at Any (GSYM fromConcrete_addNodeN) >>
      simp[addNodeN_preserves_wfg])
  >- (rename [‘addEdge m n el (fromConcrete cgr)’] >>
      ‘∃uns unt. m = nfn uns ∧ n = nfn unt’ by metis_tac[nfn_ONTO] >> gvs[] >>
      irule_at Any addEdge_fromConcrete >> gvs[nodes_fromConcrete] >>
      Cases_on ‘addEdge uns (el,unt) cgr’
      >- gvs[addEdge_EQ_NONE, wfg_def] >>
      simp[] >> metis_tac[addEdge_preserves_wfg])
QED

val _ = export_theory();
