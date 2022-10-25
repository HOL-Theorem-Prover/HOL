open HolKernel Parse boolLib bossLib;

open pred_setTheory pairTheory

val _ = new_theory "genericGraph";

Type edge[pp] = “:α # α # 'label”

Definition incident_def[simp]:
  incident (n1, n2, lab) = {n1;n2}
End

Definition selfloop_def[simp]:
  selfloop (m,n,lab) ⇔ m = n
End

Definition flip_edge_def[simp]:
  flip_edge (m,n,lab) = (n,m,lab)
End

Theorem flip_edge_idem[simp]:
  flip_edge (flip_edge e) = e
Proof
  PairCases_on ‘e’ >> simp[flip_edge_def]
QED

Theorem flip_edge_EQ[simp]:
  (flip_edge e = (a,b,lab) ⇔ e = (b,a,lab)) ∧
  ((a,b,lab) = flip_edge e ⇔ e = (b,a,lab))
Proof
  PairCases_on ‘e’ >> simp[] >> metis_tac[]
QED

Theorem incident_flip_edge[simp]:
  incident (flip_edge e) = incident e
Proof
  PairCases_on ‘e’ >> simp[EXTENSION] >> metis_tac[]
QED

Definition edge_label_def[simp]:
  edge_label ((m,n,l):(α,'l) edge) = l
End

Theorem edge_label_flip_edge[simp]:
  ∀e. edge_label (flip_edge e) = edge_label e
Proof
  simp[FORALL_PROD]
QED

Definition finite_cst_def:
  finite_cst cs A ⇔ if FINITE cs then
                      (CARD cs = 1 ⇒ FINITE A)
                    else
                      INFINITE A
End

(* constraining edge set sizes between any given pair of nodes.
   options are:
    - only one
    - finite
    - unconstrained
   (Necessarily infinitely many edges between any two nodes seems dumb.)
   The "only one" option needs to insist on 2 edges when dircst is false
 *)
Definition edge_cst_def:
  edge_cst ecst dirp slp es ⇔
    FINITE ecst ∧ CARD ecst ≤ 2 ⇒
    (∀m n. FINITE {e | e ∈ es ∧ incident e = {m;n}}) ∧
    (CARD ecst = 1 ⇒
     (slp ⇒ ∀m. CARD {e | e ∈ es ∧ incident e = {m}} ≤ 1) ∧
     (¬dirp ⇒
      (∀m n. m ≠ n ∧ (∃e. e ∈ es ∧ incident e = {m;n}) ⇒
             CARD { e | e ∈ es ∧ incident e = {m;n}} = 2 ∧
             ∃l. ∀e. e ∈ es ∧ incident e = {m;n} ⇒ edge_label e = l)) ∧
     (dirp ⇒ ∀m n. CARD {(m,n,l) | l | (m,n,l) ∈ es} ≤ 1))
End

Definition itself2set_def:
  itself2set (:'a) = univ(:'a)
End

Definition itself2bool_def:
  itself2bool x ⇔ FINITE $ itself2set x
End

Theorem itself2bool_num[simp]:
  itself2bool (:num) = F
Proof
  simp[itself2bool_def, itself2set_def]
QED

Theorem itself2bool_bool[simp]:
  itself2bool (:bool) = T
Proof
  simp[itself2bool_def, itself2set_def]
QED

(* generic graphs*)
Datatype:
  graphrep = <| nodes : ('a + num) set ;
                edges : ('a + num,'el) edge set ;
                nlab : 'a + num -> 'nl ;
                nfincst : 'nf itself ;
                dircst : 'd itself ;  (* true implies directed graph *)
                slcst : 'slc itself ; (* true implies self-loops allowed *)
                edgecst : 'ec  itself
             |>
End

Definition wfgraph_def:
  wfgraph grep ⇔
    (∀e. e ∈ grep.edges ⇒ incident e ⊆ grep.nodes) ∧
    finite_cst (itself2set grep.nfincst) grep.nodes ∧
    (¬itself2bool grep.slcst ⇒ ∀e. e ∈ grep.edges ⇒ ¬selfloop e) ∧
    (¬itself2bool grep.dircst ⇒ ∀e. e ∈ grep.edges ⇒ flip_edge e ∈ grep.edges) ∧
    edge_cst (itself2set grep.edgecst)
             (itself2bool grep.dircst)
             (itself2bool grep.slcst)
             grep.edges ∧
    (∀n. n ∉ grep.nodes ⇒ grep.nlab n = ARB)
End

Theorem UNIV_UNIT[simp]:
  UNIV : unit set = {()}
Proof
  simp[EXTENSION]
QED

Theorem finite_cst_EMPTY[simp]:
  finite_cst (itself2set (:unit)) {} ∧
  finite_cst (itself2set (:bool)) {}
Proof
  simp[finite_cst_def, itself2set_def]
QED

Theorem finite_cst_UNION:
  finite_cst s A ∧ FINITE B ⇒
  finite_cst s (A ∪ B) ∧ finite_cst s (B ∪ A)
Proof
  simp[finite_cst_def]
QED

Theorem edge_cst_EMPTY[simp]:
  edge_cst x y z {}
Proof
  rw[edge_cst_def]
QED



Theorem graphs_exist[local]:
  ∃g. wfgraph g
Proof
  Q.REFINE_EXISTS_TAC ‘<| nodes := Ns;
                          edges := {};
                          nlab := K ARB;
                          nfincst := ARB;
                          dircst := ARB;
                          slcst := ARB;
                          edgecst := ARB; |>’ >>
  simp[wfgraph_def, finite_cst_def, itself2set_def] >>
  rename [‘COND g’]>> Cases_on ‘g’ >> simp[]
  >- (qexists ‘{}’ >> simp[]) >>
  qexists ‘UNIV’ >>
  ‘INJ (INR:num->'a + num) UNIV UNIV’ by simp[INJ_DEF] >>
  drule INFINITE_INJ >> simp[]
QED

val tydefrec = newtypeTools.rich_new_type("graph", graphs_exist)

Definition emptyG0_def:
    emptyG0 : ('a,'dir,'ec,'el,unit,'nl,'sl) graphrep =
     <| nodes := {} ; edges := {}; nlab := K ARB;
        nfincst := (:unit); dircst := (:'dir); slcst := (:'sl);
        edgecst := (:'ec) |>
End

Definition emptyG_def:
  emptyG = graph_ABS emptyG0
End

Theorem wfgraph_emptyG0[simp]:
  wfgraph emptyG0
Proof
  simp[wfgraph_def, emptyG0_def]
QED

Definition nodes_def:
  nodes G = (graph_REP G).nodes
End

Theorem nodes_empty[simp]:
  nodes emptyG = ∅
Proof
  simp[nodes_def, emptyG_def, #repabs_pseudo_id tydefrec] >>
  simp[emptyG0_def]
QED

Definition adjacent_def:
  adjacent G n1 n2 ⇔ ∃l. (n1, n2, l) ∈ (graph_REP G).edges
End

Theorem adjacent_SYM:
  adjacent (G:('a,num,'ec,'el,'nf,'nl,'sl)graph) m n ⇔ adjacent G n m
Proof
  simp[adjacent_def] >>
  ‘wfgraph (graph_REP G)’ by simp[#termP_term_REP tydefrec] >>
  gs[wfgraph_def, ITSELF_UNIQUE, itself2bool_def, itself2set_def] >>
  simp[EQ_IMP_THM] >> rw[] >> first_x_assum drule >>
  simp[flip_edge_def, SF SFY_ss]
QED

Theorem adjacent_empty[simp]:
  adjacent emptyG m n ⇔ F
Proof
  simp[adjacent_def, emptyG_def, #repabs_pseudo_id tydefrec] >>
  simp[emptyG0_def]
QED

Theorem adjacent_irrefl[simp]:
  adjacent (G:('a,'dir,'ec,'el,'nf,'nl,num)graph) a a = F
Proof
  simp[adjacent_def] >>
  ‘wfgraph (graph_REP G)’ by simp[#termP_term_REP tydefrec] >>
  gs[wfgraph_def, ITSELF_UNIQUE, itself2bool_def, itself2set_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[selfloop_def]
QED

Type fsgraph[pp] = “:('a,num,unit,unit,unit,unit,num) graph”

Definition udedges_def:
  udedges (G:('a,num,unit,unit,unit,unit,'sl) graph) =
  {{m;n} | (m,n,()) ∈ (graph_REP G).edges}
End

Theorem udedges_thm:
  udedges G = {{m; n} | adjacent G m n}
Proof
  simp[udedges_def, adjacent_def]
QED

Theorem FINITE_nodes[simp]:
  FINITE (nodes (G:('a,'dir,'ec,'el,unit,'nl,'sl)graph))
Proof
  simp[nodes_def] >>
  ‘wfgraph (graph_REP G)’ by simp[#termP_term_REP tydefrec] >>
  gs[wfgraph_def, ITSELF_UNIQUE, finite_cst_def, itself2set_def]
QED

Definition addNode0_def:
  addNode0 n lab grep = grep with <| nodes updated_by (λs. n INSERT s);
                                     nlab := grep.nlab⦇n ↦ lab⦈ |>
End

Theorem wfgraph_addNode0[simp,local]:
  wfgraph grep ⇒ wfgraph (addNode0 n lab grep)
Proof
  simp[wfgraph_def, addNode0_def] >>
  rw[finite_cst_def, SUBSET_DEF, combinTheory.UPDATE_APPLY] >> metis_tac[]
QED

Definition addNode_def:
  addNode n l G = graph_ABS $ addNode0 n l $ graph_REP G
End

Theorem nodes_addNode[simp]:
  nodes (addNode n l G) = n INSERT nodes G
Proof
  simp[nodes_def, addNode_def] >>
  ‘wfgraph (graph_REP G)’ by simp[#termP_term_REP tydefrec] >>
  simp[#repabs_pseudo_id tydefrec, addNode0_def]
QED

Theorem adjacent_addNode[simp]:
  adjacent (addNode n l G) = adjacent G
Proof
  simp[adjacent_def, addNode_def, FUN_EQ_THM] >>
  ‘wfgraph (graph_REP G)’ by simp[#termP_term_REP tydefrec] >>
  simp[#repabs_pseudo_id tydefrec] >>
  simp[addNode0_def]
QED

Theorem edges_addNode[simp]:
  udedges (addNode n l G) = udedges G
Proof
  simp[udedges_thm]
QED

Definition addUDEdge0_def:
  addUDEdge0 m n lab (G:('a,num,'ec,'el,'nf,'nl,'sl)graphrep) =
  G with <| nodes := {m;n} ∪ G.nodes ;
            edges :=
            if m = n then
              if itself2bool (:'sl) then
                let
                  s = itself2set (:'ec) ;
                  e0 = if FINITE s ∧ CARD s = 1 then
                         G.edges DIFF { e | incident e = {m}}
                       else G.edges
                in
                  (m,m,lab) INSERT e0
              else G.edges
            else
              let s = itself2set (:'ec) ;
                  e0 = if FINITE s ∧ CARD s = 1 then
                         G.edges DIFF { e | incident e = {m;n}}
                       else G.edges
              in
                {(m,n,lab); (n,m,lab)} ∪ e0
         |>
End

Definition addUDEdge_def:
  addUDEdge m n lab G = graph_ABS (addUDEdge0 m n lab (graph_REP G))
End

Theorem SING_EQ2:
  {x} = {a;b} ⇔ x = a ∧ a = b
Proof
  simp[EXTENSION] >> metis_tac[]
QED

Theorem wfgraph_addEdge0[simp,local]:
  wfgraph G0 ⇒ wfgraph (addUDEdge0 m n lab G0)
Proof
  simp[addUDEdge0_def, wfgraph_def, ITSELF_UNIQUE] >>
  rw[incident_def, SUBSET_DEF] >>
  gs[incident_def, finite_cst_UNION]
  >- metis_tac[]
  >- (gs[itself2bool_def, itself2set_def, edge_cst_def] >> rw[]
      >- (dsimp[GSPEC_OR] >> csimp[incident_def, SING_EQ2] >>
          conj_tac >> irule SUBSET_FINITE
          >- (qexists ‘{(m,m,lab)}’ >> simp[SUBSET_DEF]) >>
          rename [‘incident _ = {a;b}’] >>
          qexists ‘{e | e ∈ G0.edges ∧ incident e = {a;b}}’ >>
          simp[SUBSET_DEF])
      >- (dsimp[GSPEC_OR] >> csimp[incident_def] >>
          rename [‘_ = (m,m,lab)’, ‘m = n’, ‘incident _ = {n}’] >>
          Cases_on ‘m = n’ >> simp[])
      >- gs[incident_def, SING_EQ2]
      >- gs[incident_def, SING_EQ2]
      >- (dsimp[GSPEC_OR] >> csimp[incident_def, SING_EQ2] >>
          rename [‘incident _ = {a;b}’] >>
          first_x_assum (irule o cj 1) >> metis_tac[]) >>
      dsimp[incident_def, SING_EQ2] >> metis_tac[])
  >- metis_tac[]
  >- (gs[edge_cst_def] >> rw[] >> gs[] >>
      dsimp[GSPEC_OR, SF CONJ_ss, incident_def, SING_EQ2] >>
      irule SUBSET_FINITE >> rename [‘_ = (nd,nd,label)’] >>
      qexists ‘{(nd,nd,label)}’ >> simp[SUBSET_DEF])
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- (gs[edge_cst_def] >> rw[] >> gs[] >>
      dsimp[GSPEC_OR, SF CONJ_ss, incident_def, SING_EQ2]
      >- (rpt strip_tac >>~-
          ([‘_ = (a,b,lab)’], simp[GSPEC_AND]) >>
          irule SUBSET_FINITE >> rename [‘incident _ = {a;b}’] >>
          qexists ‘{e | e ∈ G0.edges ∧ incident e = {a;b}}’ >>
          simp[SUBSET_DEF])
      >- (gs[INSERT_COMM] >>
          simp[CARD_UNION_EQN, DECIDE “2 - y = 2 ⇔ y = 0”] >>
          simp[EXTENSION])
      >- (gs[INSERT_COMM] >>
          simp[CARD_UNION_EQN, DECIDE “2 - y = 2 ⇔ y = 0”] >>
          simp[EXTENSION])
      >- gs[INSERT_COMM]
      >- (gs[INSERT_COMM] >> first_x_assum (irule o cj 1)>> metis_tac[]) >>
      gs[INSERT_COMM] >> first_x_assum (irule o cj 2) >> metis_tac[])
  >- metis_tac[] >>
  gs[edge_cst_def] >> rw[] >> gs[] >>
  dsimp[GSPEC_OR] >> simp[GSPEC_AND]
QED

Theorem addEdge_COMM:
  addUDEdge m n lab G = addUDEdge n m lab G
Proof
  Cases_on ‘m = n’ >> simp[] >>
  simp[addUDEdge_def, #term_ABS_pseudo11 tydefrec,
       #termP_term_REP tydefrec, wfgraph_addEdge0] >>
  simp[addUDEdge0_def, INSERT_COMM]
QED

Theorem nodes_addEdge[simp]:
  nodes (addUDEdge m n lab G) = {m; n} ∪ nodes G
Proof
  simp[addUDEdge_def, nodes_def, #repabs_pseudo_id tydefrec,
       #termP_term_REP tydefrec, wfgraph_addEdge0] >>
  simp[addUDEdge0_def]
QED

Theorem adjacent_addUDEdge[simp]:
  adjacent (addUDEdge m n lab (G:(α,num,'ec,'el,'nf,'nl,'sl)graph)) a b ⇔
    (m ≠ n ∨ itself2bool (:'sl)) ∧ {a;b} = {m;n} ∨ adjacent G a b
Proof
  simp[adjacent_def, addUDEdge_def, wfgraph_addEdge0,
       #termP_term_REP tydefrec, #repabs_pseudo_id tydefrec] >>
  simp[addUDEdge0_def] >> rw[SING_EQ2]
  >- (simp[EXISTS_OR_THM] >> metis_tac[])
  >- (simp[EXISTS_OR_THM] >> metis_tac[])
  >- (simp[EXISTS_OR_THM] >> Cases_on ‘{a;b} = {m;n}’ >> simp[] >>
      gs[EXTENSION]>> metis_tac[])
  >- (simp[EXISTS_OR_THM] >> Cases_on ‘{a;b} = {m;n}’ >> simp[] >>
      gs[EXTENSION]>> metis_tac[])
QED

Definition nlabelfun_def:
  nlabelfun G = (graph_REP G).nlab
End

Theorem addEdge_addNode[simp]:
  addUDEdge n n lab (G:(α,num,'ec,'el,'nf,'nl,num) graph) =
  addNode n (nlabelfun G n) G
Proof
  simp[addUDEdge_def, addNode_def, #term_ABS_pseudo11 tydefrec,
       wfgraph_addEdge0, wfgraph_addNode0, #termP_term_REP tydefrec] >>
  simp[addUDEdge0_def, addNode0_def] >>
  simp[theorem "graphrep_component_equality", GSYM INSERT_SING_UNION,
       nlabelfun_def]
QED

Definition connected_def:
  connected G ⇔
    ∀n1 n2. n1 ∈ nodes G ∧ n2 ∈ nodes G ∧ n1 ≠ n2 ⇒
            TC (adjacent G) n1 n2
End

Theorem connected_empty[simp]:
  connected emptyG
Proof
  simp[connected_def]
QED

Theorem fsgraph_component_equality:
  (g1:('a,num,unit,unit,unit,unit,'sl) graph) = g2 ⇔
    nodes g1 = nodes g2 ∧ udedges g1 = udedges g2
Proof
  simp[EQ_IMP_THM] >> simp[nodes_def, udedges_def, adjacent_def] >>
  strip_tac >> simp[SYM $ #term_REP_11 tydefrec] >>
  simp[theorem "graphrep_component_equality", ITSELF_UNIQUE] >>
  reverse conj_tac >- simp[FUN_EQ_THM] >>
  qpat_x_assum ‘GSPEC _ = GSPEC _’ mp_tac >>
  ONCE_REWRITE_TAC [EXTENSION] >>
  simp[EQ_IMP_THM, PULL_EXISTS, FORALL_AND_THM, FORALL_PROD] >>
  rw[] >> first_x_assum drule >>
  ‘wfgraph (graph_REP g1) ∧ wfgraph (graph_REP g2)’
    by simp[#termP_term_REP tydefrec] >>
  rpt (dxrule (cj 4 (iffLR wfgraph_def))) >>
  simp[ITSELF_UNIQUE] >> rename [‘(a,b,()) ∈ _’] >>
  Cases_on ‘a = b’ >> gs[SING_EQ2] >> rpt strip_tac >>
  rename [‘{a;b} = {m;n}’] >>
  Cases_on ‘a = m’ >> gvs[] >>
  qpat_x_assum ‘{_;_} = _’ mp_tac >>
  simp[EXTENSION] >> gs[FORALL_PROD] >> metis_tac[]
QED

Definition nrelabel0_def:
  nrelabel0 n l grep = if n ∈ grep.nodes then
                         grep with nlab := grep.nlab⦇ n ↦ l ⦈
                       else grep
End
Theorem wfgraph_nrelabel:
  wfgraph g0 ⇒ wfgraph $ nrelabel0 n l g0
Proof
  simp[wfgraph_def, nrelabel0_def] >> rw[] >>
  simp[combinTheory.APPLY_UPDATE_THM, AllCaseEqs()] >> strip_tac >> gvs[]
QED

Definition nrelabel_def:
  nrelabel n l G = graph_ABS (nrelabel0 n l $ graph_REP G)
End

Theorem nodes_nrelabel[simp]:
  nodes (nrelabel n l G) = nodes G
Proof
  simp[nodes_def, nrelabel_def, #termP_term_REP tydefrec,
       wfgraph_nrelabel, #repabs_pseudo_id tydefrec] >>
  rw[nrelabel0_def]
QED

Theorem nrelabel_id[simp]:
  nrelabel n l (G:(α,'d,'ecs,'el,'nf,unit,'sl) graph) = G
Proof
  simp[nrelabel_def, SYM $ #term_REP_11 tydefrec] >>
  simp[#repabs_pseudo_id tydefrec, wfgraph_nrelabel,
       #termP_term_REP tydefrec] >>
  rw[nrelabel0_def] >>
  simp[theorem "graphrep_component_equality"]
QED

Theorem adjacent_nrelabel[simp]:
  adjacent (nrelabel n l G) = adjacent G
Proof
  simp[nrelabel_def, adjacent_def, FUN_EQ_THM, #termP_term_REP tydefrec,
       #repabs_pseudo_id tydefrec, wfgraph_nrelabel] >>
  rw[nrelabel0_def]
QED

Theorem udedges_nrelabel[simp]:
  udedges (nrelabel n l G) = udedges G
Proof
  simp[udedges_thm]
QED

Theorem addNode_idem:
  n ∈ nodes G ⇒ addNode n l G = nrelabel n l G
Proof
  simp[addNode_def, ABSORPTION_RWT, SYM $ #term_REP_11 tydefrec, nodes_def,
       nrelabel_def] >>
  simp[#repabs_pseudo_id tydefrec, wfgraph_addNode0, #termP_term_REP tydefrec,
       wfgraph_nrelabel] >>
  simp[addNode0_def, nrelabel0_def] >>
  simp[theorem "graphrep_component_equality", ABSORPTION_RWT]
QED

Theorem nodes_EQ_EMPTY[simp]:
  nodes G = ∅ ⇔ G = emptyG
Proof
  simp[EQ_IMP_THM] >>
  simp[SYM $ #term_REP_11 tydefrec, emptyG_def, nodes_def,
       #repabs_pseudo_id tydefrec, wfgraph_emptyG0] >>
  simp[emptyG0_def, theorem "graphrep_component_equality", ITSELF_UNIQUE] >>
  strip_tac >> ‘wfgraph (graph_REP G)’ by simp[#termP_term_REP tydefrec] >>
  drule_then assume_tac (cj 1 $ iffLR wfgraph_def) >> gs[FORALL_PROD] >>
  reverse (Cases_on ‘(graph_REP G).edges’ >> gs[])
  >- (rename [‘_.edges = e INSERT _’] >> PairCases_on ‘e’ >> metis_tac[]) >>
  drule_then assume_tac (cj 6 $ iffLR wfgraph_def) >> gs[] >> simp[FUN_EQ_THM]
QED

Theorem adjacent_members:
  adjacent G m n ⇒ m ∈ nodes G ∧ n ∈ nodes G
Proof
  simp[adjacent_def, nodes_def] >> strip_tac >>
  ‘wfgraph (graph_REP G)’ by simp[#termP_term_REP tydefrec] >>
  drule_then drule (cj 1 $ iffLR wfgraph_def) >>
  simp[]
QED

Theorem connected_addNode:
  connected (addNode n l G) ⇔ n ∈ nodes G ∧ connected G ∨ G = emptyG
Proof
  simp[EQ_IMP_THM, addNode_idem, DISJ_IMP_THM] >> rw[connected_def] >>
  CCONTR_TAC >> gs[] >>
  ‘∃m. m ∈ nodes G’
    by (CCONTR_TAC >> gs[] >>
        ‘nodes G = {}’ by (Cases_on ‘nodes G’ >> gs[] >> metis_tac[]) >>
        gs[]) >>
  ‘(adjacent G)⁺ n m’ by metis_tac[] >>
  drule_then strip_assume_tac relationTheory.TC_CASES1_E >>
  drule adjacent_members >> simp[]
QED




val  _ = export_theory();
