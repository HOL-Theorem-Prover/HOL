open HolKernel Parse boolLib bossLib;

open pred_setTheory pairTheory sortingTheory

val _ = new_theory "genericGraph";

Type edge[pp] = “:α # α # 'label”

Theorem SING_EQ2[simp]:
  {x} = {a;b} ⇔ x = a ∧ a = b
Proof
  simp[EXTENSION] >> metis_tac[]
QED

Theorem INSERT2_lemma:
  {a;b} = {m;n} ⇔ a = b ∧ m = n ∧ a = m ∨
                  a = m ∧ b = n ∨
                  a = n ∧ b = m
Proof
  simp[EXTENSION] >> metis_tac[]
QED

Theorem GSPEC_lemma:
  (GSPEC (λx. (y, P)) = if P then {y} else {}) ∧
  (GSPEC (λx. (f x, x = e ∧ P)) = if P then {f e} else {})
Proof
  rw[EXTENSION]
QED

Definition incident_def[simp]:
  incident (n1, n2, lab) = {n1;n2}
End

Theorem FINITE_incident[simp]:
  FINITE (incident e)
Proof
  PairCases_on ‘e’ >> simp[]
QED

Theorem incident_EQ_SING:
  incident e = {m} ⇔ ∃l. e = (m,m,l)
Proof
  PairCases_on ‘e’ >> simp[] >> metis_tac[]
QED

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
  finite_cst cs A ⇔ (FINITE cs ⇒ FINITE A)
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
     (¬dirp ⇒
      (slp ⇒ ∀m. CARD {e | e ∈ es ∧ incident e = {m}} ≤ 1) ∧
      (∀m n. m ≠ n ∧ (∃e. e ∈ es ∧ incident e = {m;n}) ⇒
             CARD { e | e ∈ es ∧ incident e = {m;n}} = 2 ∧
             ∃l. ∀e. e ∈ es ∧ incident e = {m;n} ⇒ edge_label e = l)) ∧
     (dirp ⇒ ∀m n. CARD {(m,n,l) | l | (m,n,l) ∈ es} ≤ 1))
End

val SL_OK_tydefrec = newtypeTools.rich_new_type("SL_OK",
  prove(“∃x:unit. (λx. T) x”, simp[]));
val noSL_tydefrec = newtypeTools.rich_new_type("noSL",
  prove(“∃x:num. (λx. T) x”, simp[]));

val INF_OK_tydefrec = newtypeTools.rich_new_type("INF_OK",
  prove(“∃x:num. (λx. T) x”, simp[]));
val finiteG_tydefrec = newtypeTools.rich_new_type("finiteG",
  prove(“∃x:unit. (λx. T) x”, simp[]));

val undirectedG_tydefrec = newtypeTools.rich_new_type("undirectedG",
  prove(“∃x:num. (λx. T) x”, simp[]));
val directedG_tydefrec = newtypeTools.rich_new_type("directedG",
  prove(“∃x:unit. (λx. T) x”, simp[]));

val allEdgesOK_tydefrec = newtypeTools.rich_new_type("allEdgesOK",
  prove(“∃x:num. (λx. T) x”, simp[]));

Definition itself2set_def[simp]:
  itself2set (:'a) = univ(:'a)
End

Definition itself2bool_def:
  itself2bool x ⇔ FINITE $ itself2set x
End

Theorem UNIV_UNIT[simp]:
  UNIV : unit set = {()}
Proof
  simp[EXTENSION]
QED

Theorem UNIV_SL_OK[simp]:
  UNIV : SL_OK set = {SL_OK_ABS ()}
Proof
  simp[EXTENSION, SYM $ #term_REP_11 SL_OK_tydefrec]
QED

Theorem itself2bool_SL_OK[simp]:
  itself2bool (:SL_OK) = T
Proof
  simp[itself2bool_def]
QED

Theorem UNIV_finiteG[simp]:
  univ(:finiteG) = {finiteG_ABS ()}
Proof
  simp[EXTENSION, SYM $ #term_REP_11 finiteG_tydefrec]
QED

Theorem itself2bool_finiteG[simp]:
  itself2bool (:finiteG) = T
Proof
  simp[itself2bool_def]
QED

Theorem UNIV_directedG[simp]:
  univ(:directedG) = {directedG_ABS ()}
Proof
  simp[EXTENSION, SYM $ #term_REP_11 directedG_tydefrec]
QED

Theorem itself2bool_directedG[simp]:
  itself2bool (:directedG) = T
Proof
  simp[itself2bool_def]
QED

Theorem itself2bool_noSL[simp]:
  itself2bool (:noSL) = F
Proof
  simp[itself2bool_def] >>
  simp[infinite_num_inj] >> qexists ‘noSL_ABS’ >>
  simp[INJ_IFF, #term_ABS_pseudo11 noSL_tydefrec]
QED

Theorem itself2bool_undirectedG[simp]:
  itself2bool (:undirectedG) = F
Proof
  simp[itself2bool_def] >>
  simp[infinite_num_inj] >> qexists ‘undirectedG_ABS’ >>
  simp[INJ_IFF, #term_ABS_pseudo11 undirectedG_tydefrec]
QED

Theorem INFINITE_UINF_OK[simp]:
  INFINITE univ(:INF_OK)
Proof
  simp[infinite_num_inj] >> qexists ‘INF_OK_ABS’ >>
  simp[INJ_IFF, #term_ABS_pseudo11 INF_OK_tydefrec]
QED

Theorem INFINITE_allEdgesOK[simp]:
  INFINITE univ(:allEdgesOK)
Proof
  simp[infinite_num_inj] >> qexists ‘allEdgesOK_ABS’ >>
  simp[INJ_IFF, #term_ABS_pseudo11 allEdgesOK_tydefrec]
QED

Theorem itself2bool_INF_OK[simp]:
  itself2bool (:INF_OK) = F
Proof
  simp[itself2bool_def]
QED

Theorem itself2bool_num[simp]:
  itself2bool (:num) = F
Proof
  simp[itself2bool_def]
QED

Theorem itself2bool_bool[simp]:
  itself2bool (:bool) = T
Proof
  simp[itself2bool_def]
QED

Theorem itself2bool_unit[simp]:
  itself2bool (:unit) = T
Proof
  simp[itself2bool_def]
QED

(* generic graphs; because edges are a set, can't have multiple edges between
   same two nodes with the same label.  Could imagine making the set a bag
   if you really wanted that.
*)
Datatype:
  graphrep = <| nodes : 'a set ;
                edges : ('a,'el) edge set ;
                nlab : 'a -> 'nl ;
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

Theorem finite_cst_EMPTY[simp]:
  finite_cst (itself2set (:unit)) {} ∧
  finite_cst (itself2set (:bool)) {}
Proof
  simp[finite_cst_def]
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
  qexists ‘{}’ >> simp[]
QED

val tydefrec = newtypeTools.rich_new_type("graph", graphs_exist)

(* any undirected graph *)
Type udgraph[pp] = “:('a,undirectedG,'ec,'el,'nf,'nl,'sl)graph”


(* finite directed graph with labels on nodes and edges, possibility of
   multiple, but finitely many edges, and with self-loops allowed *)
Type fdirgraph[pp] = “:('NodeEnum,
                        directedG,
                        bool (* finitely many edges between nodes *),
                        'edgelabel,
                        finiteG (* finitely many nodes *),
                        'NodeLabel (* capitalised to precede 'edge *),
                        SL_OK (* self-loops OK *)
                       ) graph”

Type allokdirgraph[pp] = “:('NodeEnum,
                            directedG,
                            allEdgesOK,
                            'edgelabel,
                            INF_OK,
                            'NodeLabel,
                            SL_OK) graph”

(* unlabelled graph *)
Type ulabgraph[pp] = “:(α,
                        δ (* undirected? *),
                        unit,
                        unit (* edge label *),
                        ν (* infinite nodes allowed? *),
                        unit (* node label *),
                        σ (* self-loops? *)) graph”

(* undirected version of the same *)
Type udulgraph[pp] = “:(α, undirectedG, ν, σ)ulabgraph”

(* finite simple graph *)
Type fsgraph[pp] = “:(α,finiteG,noSL) udulgraph”


(* a relation graph; stripped such are in bijection with binary relations.
   (The stripping makes a canonical, minimal choice of node set in the graph.)
 *)
Type relgraph[pp] = “:(α, directedG, INF_OK, SL_OK) ulabgraph”


Definition emptyG0_def:
    emptyG0 : (α,δ,'ec,'el,ν,'nl,σ) graphrep =
     <| nodes := {} ; edges := {}; nlab := K ARB;
        nfincst := (:ν); dircst := (:δ); slcst := (:σ);
        edgecst := (:'ec) |>
End


Definition nodes_def:
  nodes G = (graph_REP G).nodes
End

Definition edges_def:
  edges G = (graph_REP G).edges
End

Theorem incident_SUBSET_nodes:
  e ∈ edges g ∧ n ∈ incident e ⇒ n ∈ nodes g
Proof
  rw[edges_def, nodes_def] >>
  ‘wfgraph (graph_REP g)’ by simp[#termP_term_REP tydefrec] >>
  gs[wfgraph_def, SUBSET_DEF] >> metis_tac[]
QED

Definition nlabelfun_def:
  nlabelfun G = (graph_REP G).nlab
End

Theorem nlabelfun_EQ_ARB[simp]:
  n ∉ nodes g ⇒ nlabelfun g n = ARB
Proof
  rw[nodes_def, nlabelfun_def] >>
  ‘wfgraph (graph_REP g)’ by simp[#termP_term_REP tydefrec] >>
  gs[wfgraph_def]
QED

Definition emptyG_def:
  emptyG = graph_ABS emptyG0
End

Theorem wfgraph_emptyG0[simp]:
  wfgraph emptyG0
Proof
  simp[wfgraph_def, emptyG0_def, finite_cst_def]
QED

Theorem nodes_empty[simp]:
  nodes emptyG = ∅
Proof
  simp[nodes_def, emptyG_def, #repabs_pseudo_id tydefrec] >>
  simp[emptyG0_def]
QED

Theorem edges_empty[simp]:
  edges emptyG = ∅
Proof
  simp[edges_def, emptyG_def, #repabs_pseudo_id tydefrec] >>
  simp[emptyG0_def]
QED

Theorem nlabelfun_empty[simp]:
  nlabelfun emptyG = (λn. ARB)
Proof
  simp[nlabelfun_def, emptyG_def, #repabs_pseudo_id tydefrec] >>
  simp[emptyG0_def, FUN_EQ_THM]
QED

Definition adjacent_def:
  adjacent G n1 n2 ⇔ ∃l. (n1, n2, l) ∈ edges G
End

Theorem edges_SYM:
  (m,n,l) ∈ edges (G : ('a,undirectedG,'ec,'el,'nf,'nl,'sl)graph) ⇔
  (n,m,l) ∈ edges G
Proof
  simp[edges_def] >>
  ‘wfgraph (graph_REP G)’ by simp[#termP_term_REP tydefrec] >>
  gs[wfgraph_def, FORALL_PROD, ITSELF_UNIQUE] >> metis_tac[]
QED

Theorem adjacent_SYM:
  adjacent (G:('a,undirectedG,'ec,'el,'nf,'nl,'sl)graph) m n ⇔ adjacent G n m
Proof
  simp[adjacent_def] >> metis_tac[edges_SYM]
QED

Theorem adjacent_empty[simp]:
  adjacent emptyG m n ⇔ F
Proof
  simp[adjacent_def, emptyG_def, #repabs_pseudo_id tydefrec] >>
  simp[emptyG0_def]
QED

Theorem edges_irrefl[simp]:
  (a,a,l) ∉ edges (G:('a,'dir,'ec,'el,'nf,'nl,noSL)graph)
Proof
  simp[edges_def] >>
  ‘wfgraph (graph_REP G)’ by simp[#termP_term_REP tydefrec] >>
  gs[wfgraph_def, ITSELF_UNIQUE, FORALL_PROD]
QED

Theorem adjacent_irrefl[simp]:
  adjacent (G:('a,'dir,'ec,'el,'nf,'nl,noSL)graph) a a = F
Proof
  simp[adjacent_def]
QED

Definition udedges_def:
  udedges (G:(α,ν,σ) udulgraph) = {{m;n} | (m,n,()) ∈ edges G}
End

Theorem udedges_thm:
  udedges G = {{m; n} | adjacent G m n}
Proof
  simp[udedges_def, adjacent_def]
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

Theorem edges_addNode[simp]:
  edges (addNode n l G) = edges G
Proof
  simp[edges_def, addNode_def, #repabs_pseudo_id tydefrec,
       #termP_term_REP tydefrec, wfgraph_addNode0] >>
  simp[addNode0_def]
QED

Theorem nlabelfun_addNode[simp]:
  nlabelfun (addNode n l g) = (nlabelfun g)⦇ n ↦ l ⦈
Proof
  simp[nlabelfun_def, addNode_def, #repabs_pseudo_id tydefrec,
      #termP_term_REP tydefrec, wfgraph_addNode0] >>
  simp[addNode0_def]
QED

Theorem adjacent_addNode[simp]:
  adjacent (addNode n l G) = adjacent G
Proof
  simp[adjacent_def, FUN_EQ_THM]
QED

Theorem udedges_addNode[simp]:
  udedges (addNode n l G) = udedges G
Proof
  simp[udedges_thm]
QED

Definition addUDEdge0_def:
  addUDEdge0 m n lab (G:('a,undirectedG,'ec,'el,'nf,'nl,'sl)graphrep) =
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

Definition edge0_def:
  edge0 m n lab slp ecset edges =
  if m = n ∧ ¬slp then edges
  else if FINITE ecset ∧ CARD ecset = 1 then
    edges DIFF {(m,n,l) | l | T} ∪ {(m,n,lab)}
  else edges ∪ {(m,n,lab)}
End

Definition addEdge0_def:
  addEdge0 m n (lab:'el) (G : ('ne,directedG,'ec,'el,'nf,'nl,'sl) graphrep) =
  G with <|
      nodes := G.nodes ∪ (if m = n ∧ ¬itself2bool (:'sl) then ∅ else {m;n}) ;
      edges := edge0 m n lab
                     (itself2bool G.slcst)
                     (itself2set G.edgecst)
                     G.edges
    |>
End

Definition addEdge_def:
  addEdge m n l G = graph_ABS (addEdge0 m n l (graph_REP G))
End

Theorem wfgraph_addUDEdge0[simp,local]:
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

Theorem CARD_LE1[local]:
  FINITE s ⇒
  (CARD s ≤ 1 ⇔ s = {} ∨ (∃e. s = {e}))
Proof
  simp[EQ_IMP_THM, PULL_EXISTS, DISJ_IMP_THM] >>
  simp[DECIDE “n ≤ 1 ⇔ n = 0 ∨ n = 1”, DISJ_IMP_THM] >> rpt strip_tac >>
  ‘SING s’ by metis_tac[SING_IFF_CARD1] >>
  gs[SING_DEF]
QED

Theorem GSPEC_EQ'[simp]:
  GSPEC (λx. (f x, x = y)) = {f y} ∧
  GSPEC (λx. (f x, y = x)) = {f y}
Proof
  simp[EXTENSION]
QED

Theorem IN_edge0:
  e ∈ edge0 m n lab slp ecset edgeset ⇒
  e = (m,n,lab) ∨ e ∈ edgeset
Proof
  rw[edge0_def] >> simp[]
QED

Theorem edge0_preserves_edge_cst:
  edge_cst ecset T slp edgeset ⇒
  edge_cst ecset T slp (edge0 m n lab slp ecset edgeset)
Proof
  rw[edge_cst_def, edge0_def] >> gvs[]
  >- (dsimp[GSPEC_OR] >>
      rename [‘_ = (m,n,lab) ∧ incident _ = {m1;n1}’] >>
      conj_tac >~
      [‘_ = (m,n,lab)’] >- simp[GSPEC_AND] >>
      irule SUBSET_FINITE >> first_assum $ irule_at Any >>
      simp[SUBSET_DEF] >> metis_tac[]) >~
  [‘(a,b,_) ∈ Es’, ‘a = m ∧ b = n ∧ _ = lab’]
  >- (Cases_on ‘a = m’ >> gvs[] >> Cases_on ‘b = n’ >> gvs[]) >>
  dsimp[] >> simp[GSPEC_OR] >> csimp[] >>
  rename [‘FINITE { e | e = x ∧ P}’] >> Cases_on ‘P’ >> simp[]
QED

Theorem wfgraph_addEdge0[local]:
  wfgraph G0 ⇒ wfgraph (addEdge0 m n lab G0)
Proof
  simp[wfgraph_def, addEdge0_def, ITSELF_UNIQUE, finite_cst_UNION] >>
  rpt strip_tac >> gvs[]
  >- (drule_then strip_assume_tac IN_edge0 >> rw[incident_def] >~
      [‘(m,m,lab) ∈ edge0 _ _ _ _ _ _ ’]
      >- (gs[edge0_def] >> first_x_assum drule >> simp[]) >>
      metis_tac[SUBSET_TRANS, SUBSET_UNION]) >~
  [‘selfloop e’]
  >- (gvs[edge0_def] >> qpat_x_assum ‘e ∈ _’ mp_tac >> rw[] >>
      metis_tac[selfloop_def]) >~
  [‘finite_cst _ (_ ∪ _)’]
  >- rw[finite_cst_UNION] >>
  simp[edge0_preserves_edge_cst]
QED

Definition selfloops_ok_def[simp]:
  selfloops_ok (G : (α,'d,'ec,'el,'nf,'nl,'sl) graph) = itself2bool (:'sl)
End

Definition oneEdge_max_def:
  oneEdge_max (G: (α,'d,'ec,'el,'nf,'nl,'sl) graph) ⇔
  FINITE (itself2set (:'ec)) ∧ CARD (itself2set (:'ec)) = 1
End

Theorem oneEdge_max_graph[simp]:
  oneEdge_max (g : ('a,'d,unit,'el,'nf,'nl,'sl) graph)
Proof
  simp[oneEdge_max_def, itself2set_def]
QED

Theorem oneEdge_max_fdirgraph[simp]:
  ¬oneEdge_max (g : (α,β,γ)fdirgraph)
Proof
  simp[oneEdge_max_def, itself2set_def]
QED

Theorem selfloops_ok_graph[simp]:
  selfloops_ok (g : ('a,'d,'ec,'el,'nf,'nl,unit) graph)
Proof
  simp[selfloops_ok_def]
QED

Theorem edges_addEdge:
  edges (addEdge m n lab G) =
  (edges G DIFF
   (if oneEdge_max G ∧ adjacent G m n then { (m,n,l) | l | (m,n,l) ∈ edges G }
    else {})) ∪
  (if m ≠ n ∨ selfloops_ok G then {(m,n,lab)} else {})
Proof
  simp[edges_def, addEdge_def, wfgraph_addEdge0, #termP_term_REP tydefrec,
       #repabs_pseudo_id tydefrec] >>
  simp[addEdge0_def, edge0_def, ITSELF_UNIQUE] >> rw[] >>
  gvs[oneEdge_max_def] >~
  [‘adjacent G m m’]
  >- (‘wfgraph (graph_REP G)’ by simp[#termP_term_REP tydefrec] >>
      gvs[wfgraph_def, adjacent_def, ITSELF_UNIQUE, edge_cst_def,
          selfloop_def, FORALL_PROD]) >~
  [‘¬adjacent G a b’]
  >- (gvs[adjacent_def, EXTENSION, edges_def] >> metis_tac[]) >~
  [‘adjacent G a b’]
  >- (simp[EXTENSION] >> metis_tac[])
QED

Theorem adjacent_addEdge[simp]:
  adjacent (addEdge m n lab G) a b ⇔
    (m ≠ n ∨ selfloops_ok G) ∧ m = a ∧ n = b ∨ adjacent G a b
Proof
  simp[adjacent_def, addEdge_def, wfgraph_addEdge0, #termP_term_REP tydefrec,
       #repabs_pseudo_id tydefrec, edges_def] >>
  simp[addEdge0_def, edge0_def, ITSELF_UNIQUE] >> rw[] >>
  metis_tac[]
QED

Theorem addUDEdge_COMM:
  addUDEdge m n lab G = addUDEdge n m lab G
Proof
  Cases_on ‘m = n’ >> simp[] >>
  simp[addUDEdge_def, #term_ABS_pseudo11 tydefrec,
       #termP_term_REP tydefrec, wfgraph_addUDEdge0] >>
  simp[addUDEdge0_def, INSERT_COMM]
QED

Theorem nodes_addUDEdge[simp]:
  nodes (addUDEdge m n lab G) = {m; n} ∪ nodes G
Proof
  simp[addUDEdge_def, nodes_def, #repabs_pseudo_id tydefrec,
       #termP_term_REP tydefrec, wfgraph_addUDEdge0] >>
  simp[addUDEdge0_def]
QED

Theorem adjacent_addUDEdge[simp]:
  adjacent (addUDEdge m n lab G) a b ⇔
    (m ≠ n ∨ selfloops_ok G) ∧ {a;b} = {m;n} ∨ adjacent G a b
Proof
  simp[adjacent_def, addUDEdge_def, wfgraph_addUDEdge0, edges_def,
       #termP_term_REP tydefrec, #repabs_pseudo_id tydefrec] >>
  simp[addUDEdge0_def] >> rw[SING_EQ2]
  >- metis_tac[]
  >- metis_tac[]
  >- (simp[EXISTS_OR_THM] >> Cases_on ‘{a;b} = {m;n}’ >> simp[] >>
      gs[EXTENSION]>> metis_tac[])
  >- (simp[EXISTS_OR_THM] >> Cases_on ‘{a;b} = {m;n}’ >> simp[] >>
      gs[EXTENSION]>> metis_tac[])
QED

Theorem nodes_addEdge[simp]:
  nodes (addEdge m n lab g) =
  nodes g ∪ (if selfloops_ok g ∨ m ≠ n then {m;n} else {})
Proof
  simp[addEdge_def, #termP_term_REP tydefrec, wfgraph_addEdge0, nodes_def,
       #repabs_pseudo_id tydefrec] >>
  simp[addEdge0_def] >> rw[] >> gvs[]
QED

Theorem nlabelfun_addEdge[simp]:
  nlabelfun (addEdge m n l g) = nlabelfun g
Proof
  simp[nlabelfun_def, addEdge_def, #repabs_pseudo_id tydefrec,
       #termP_term_REP tydefrec, wfgraph_addEdge0] >>
  simp[addEdge0_def]
QED

(* adding undirected self-edge from n to n is the same as adding bare node n *)
Theorem addUDEdge_addNode[simp]:
  addUDEdge n n lab (G:(α,undirectedG,'ec,'el,'nf,'nl,noSL) graph) =
  addNode n (nlabelfun G n) G
Proof
  simp[addUDEdge_def, addNode_def, #term_ABS_pseudo11 tydefrec,
       wfgraph_addUDEdge0, wfgraph_addNode0, #termP_term_REP tydefrec] >>
  simp[addUDEdge0_def, addNode0_def] >>
  simp[theorem "graphrep_component_equality", GSYM INSERT_SING_UNION,
       nlabelfun_def]
QED

(* "similarly" for addEdge: *)
Theorem addEdge_addNode[simp]:
  addEdge n n lab (G : (α,directedG,'ec,'el,'nf,'nl,noSL)graph) = G
Proof
  simp[SYM $ #term_REP_11 tydefrec] >>
  simp[addEdge_def, #term_ABS_pseudo11 tydefrec, #repabs_pseudo_id tydefrec,
       wfgraph_addEdge0, wfgraph_addNode0, #termP_term_REP tydefrec] >>
  simp[addEdge0_def, edge0_def, ITSELF_UNIQUE] >>
  simp[theorem "graphrep_component_equality"]
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

Theorem connected_RTC:
  connected G ⇔ ∀n1 n2. n1 ∈ nodes G ∧ n2 ∈ nodes G ⇒ (adjacent G)꙳ n1 n2
Proof
  simp[connected_def, GSYM $ cj 1 $ relationTheory.TC_RC_EQNS] >>
  simp[relationTheory.RC_DEF] >> metis_tac[]
QED

Theorem gengraph_component_equality:
  g1 = g2 ⇔ nodes g1 = nodes g2 ∧ edges g1 = edges g2 ∧
            nlabelfun g1 = nlabelfun g2
Proof
  simp[EQ_IMP_THM] >>
  simp[nodes_def, edges_def, SYM $ #term_REP_11 tydefrec,
       nlabelfun_def] >>
  simp[theorem "graphrep_component_equality", ITSELF_UNIQUE]
QED

Theorem udul_component_equality:
  (g1:(α,ν,σ) udulgraph) = g2 ⇔
    nodes g1 = nodes g2 ∧ udedges g1 = udedges g2
Proof
  simp[gengraph_component_equality, EQ_IMP_THM] >> rpt strip_tac
  >- simp[udedges_def]
  >- (gs[udedges_def] >>
      qpat_x_assum ‘GSPEC _ = GSPEC _’ mp_tac >>
      simp[SimpLHS, Once EXTENSION] >>
      simp[EQ_IMP_THM, FORALL_AND_THM, PULL_EXISTS] >>
      dsimp[INSERT2_lemma] >> strip_tac >>
      simp[EXTENSION, FORALL_PROD] >>
      metis_tac[edges_SYM]) >>
  simp[FUN_EQ_THM]
QED

Theorem ulabgraph_component_equality:
  (g1 : (α,δ,ν,σ) ulabgraph = g2) ⇔
    nodes g1 = nodes g2 ∧ ∀a b. adjacent g1 a b = adjacent g2 a b
Proof
  simp[EQ_IMP_THM, adjacent_def, gengraph_component_equality] >>
  strip_tac >> simp[EXTENSION, FORALL_PROD] >>
  simp[FUN_EQ_THM, EQ_IMP_THM]
QED

Definition nrelabel0_def:
  nrelabel0 n l grep = if n ∈ grep.nodes then
                         grep with nlab := grep.nlab⦇ n ↦ l ⦈
                       else grep
End

Theorem wfgraph_nrelabel0:
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
       wfgraph_nrelabel0, #repabs_pseudo_id tydefrec] >>
  rw[nrelabel0_def]
QED

Theorem nrelabel_id[simp]:
  nrelabel n l (G:(α,'d,'ecs,'el,'nf,unit,'sl) graph) = G
Proof
  simp[nrelabel_def, SYM $ #term_REP_11 tydefrec] >>
  simp[#repabs_pseudo_id tydefrec, wfgraph_nrelabel0,
       #termP_term_REP tydefrec] >>
  rw[nrelabel0_def] >>
  simp[theorem "graphrep_component_equality"]
QED

Theorem adjacent_nrelabel[simp]:
  adjacent (nrelabel n l G) = adjacent G
Proof
  simp[nrelabel_def, adjacent_def, FUN_EQ_THM, #termP_term_REP tydefrec,
       #repabs_pseudo_id tydefrec, wfgraph_nrelabel0, edges_def] >>
  rw[nrelabel0_def]
QED

Theorem udedges_nrelabel[simp]:
  udedges (nrelabel n l G) = udedges G
Proof
  simp[udedges_thm]
QED

Theorem edges_nrelabel[simp]:
  edges (nrelabel n l G) = edges G
Proof
  simp[edges_def, nrelabel_def, #termP_term_REP tydefrec, wfgraph_nrelabel0,
       #repabs_pseudo_id tydefrec] >>
  simp[nrelabel0_def] >> rw[]
QED

Theorem nlabelfun_nrelabel:
  n ∈ nodes G ⇒
  nlabelfun (nrelabel n l G) = (nlabelfun G) ⦇ n ↦ l ⦈
Proof
  simp[nlabelfun_def, nrelabel_def, wfgraph_nrelabel0, #termP_term_REP tydefrec,
       #repabs_pseudo_id tydefrec, nodes_def] >>
  simp[nrelabel0_def]
QED

Theorem addNode_idem:
  n ∈ nodes G ⇒ addNode n l G = nrelabel n l G
Proof
  simp[addNode_def, ABSORPTION_RWT, SYM $ #term_REP_11 tydefrec, nodes_def,
       nrelabel_def] >>
  simp[#repabs_pseudo_id tydefrec, wfgraph_addNode0, #termP_term_REP tydefrec,
       wfgraph_nrelabel0] >>
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
  simp[adjacent_def, nodes_def, edges_def] >> strip_tac >>
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

(* ----------------------------------------------------------------------
    building graphs from binary relations

    1. univR_graph : creates a graph where the node set is all possible
       elements

    2. restrR_graph: creates a graph where the node set is only those
       nodes touched by R
   ---------------------------------------------------------------------- *)

Definition univR_graph0_def:
  univR_graph0 R = <|
                     nodes := UNIV;
                     edges := {(a, b, ()) | R a b};
                     nlab := K ();
                     nfincst := (:INF_OK);
                     dircst := (:directedG) ;
                     slcst := (:SL_OK) ; (* self-loops allowed *)
                     edgecst := (:unit)
                   |>
End

Definition univR_graph_def:
  univR_graph R : α relgraph = graph_ABS (univR_graph0 R)
End

Theorem wfgraph_univR_graph0:
  wfgraph (univR_graph0 R)
Proof
  simp[wfgraph_def, univR_graph0_def, itself2set_def, finite_cst_def,
       edge_cst_def, PULL_EXISTS, INSERT2_lemma, SF CONJ_ss, SF DNF_ss] >>
  simp[GSPEC_OR] >>
  rpt strip_tac >>
  rpt (rename [‘GSPEC (λx. (x, x = _ ∧ P))’] >> Cases_on ‘P’ >> simp[])>>
  rw[GSPEC_lemma]
QED

Definition restrR_graph0_def:
  restrR_graph0 R = <|
                     nodes := { a | ∃b. R a b ∨ R b a };
                     edges := {(a, b, ()) | R a b};
                     nlab := K ();
                     nfincst := (:INF_OK);
                     dircst := (:directedG) ;
                     slcst := (:SL_OK) ; (* self-loops allowed *)
                     edgecst := (:unit)
                   |>
End

Definition restrR_graph_def:
  restrR_graph R : 'a relgraph = graph_ABS (restrR_graph0 R)
End

Theorem wfgraph_restrR_graph0:
  wfgraph (restrR_graph0 R)
Proof
  simp[wfgraph_def, restrR_graph0_def, itself2set_def, finite_cst_def,
       edge_cst_def, PULL_EXISTS, SF CONJ_ss, SF DNF_ss, INSERT2_lemma,
       GSPEC_lemma] >>
  simp[GSPEC_OR, GSPEC_lemma] >> rw[] >> metis_tac[]
QED

Theorem nodes_univR_graph[simp]:
  nodes (univR_graph R) = UNIV
Proof
  simp[univR_graph_def, nodes_def, #repabs_pseudo_id tydefrec,
       wfgraph_univR_graph0] >>
  simp[univR_graph0_def]
QED

Theorem edges_univR_graph[simp]:
  edges (univR_graph R) = { (x,y,()) | R x y }
Proof
  simp[univR_graph_def, edges_def, #repabs_pseudo_id tydefrec,
       wfgraph_univR_graph0] >>
  simp[univR_graph0_def]
QED

Theorem adjacent_univR_graph[simp]:
  adjacent (univR_graph R) = R
Proof
  simp[adjacent_def, FUN_EQ_THM]
QED

Theorem univR_graph_11[simp]:
  univR_graph R1 = univR_graph R2 ⇔ R1 = R2
Proof
  simp[ulabgraph_component_equality, FUN_EQ_THM]
QED

Theorem nodes_restrR_graph:
  nodes (restrR_graph R) = { a | (∃b. R a b) ∨ (∃b. R b a) }
Proof
  simp[restrR_graph_def, nodes_def, #repabs_pseudo_id tydefrec,
       wfgraph_restrR_graph0] >>
  simp[restrR_graph0_def, EXTENSION] >> metis_tac[]
QED

Theorem edges_restrR_graph[simp]:
  edges (restrR_graph R) = { (x,y,()) | R x y }
Proof
  simp[restrR_graph_def, edges_def, #repabs_pseudo_id tydefrec,
       wfgraph_restrR_graph0] >>
  simp[restrR_graph0_def]
QED

Theorem adjacent_restrR_graph[simp]:
  adjacent (restrR_graph R) = R
Proof
  simp[adjacent_def, FUN_EQ_THM]
QED

Theorem restrR_graph_11[simp]:
  restrR_graph r1 = restrR_graph r2 ⇔ r1 = r2
Proof
  simp[ulabgraph_component_equality, nodes_restrR_graph, Once EQ_IMP_THM] >>
  strip_tac >> simp[FUN_EQ_THM]
QED

Theorem univR_graph_inj:
  INJ univR_graph
      (UNIV : (α -> α -> bool) set)
      (UNIV: α relgraph set)
Proof
  simp[INJ_IFF]
QED

Theorem restrR_graph_inj:
  INJ restrR_graph UNIV UNIV
Proof
  simp[INJ_IFF]
QED

Theorem relgraph_components_inj:
  INJ (λg. (adjacent g, nodes g))
      (UNIV: α relgraph set)
      (UNIV: (('a -> 'a -> bool) # 'a set) set)
Proof
  simp[INJ_IFF, ulabgraph_component_equality] >> metis_tac[]
QED

Definition stripped_def:
  stripped g ⇔ nodes g = { a | ∃e. e ∈ edges g ∧ a ∈ incident e }
End

Theorem stripped_restrR_graph[simp]:
  stripped (restrR_graph r)
Proof
  dsimp[stripped_def, PULL_EXISTS, nodes_restrR_graph]
QED

Theorem relgraph_adjacent_EQ_edges_EQ:
  adjacent (g1 : α relgraph) = adjacent g2 ⇔
  edges g1 = edges g2
Proof
  simp[SimpLHS, FUN_EQ_THM] >> simp[adjacent_def, EXTENSION, FORALL_PROD]
QED

Theorem stripped_graph_relation_bij:
  BIJ adjacent { g : α relgraph | stripped g } UNIV
Proof
  simp[BIJ_DEF, INJ_IFF, SURJ_DEF] >> conj_tac
  >- (qx_genl_tac [‘g1’, ‘g2’] >> rpt strip_tac >>
      simp[ulabgraph_component_equality, Once EQ_IMP_THM] >>
      rpt strip_tac
      >- gs[stripped_def, relgraph_adjacent_EQ_edges_EQ] >>
      simp[FUN_EQ_THM]) >>
  qx_gen_tac ‘R’ >> qexists‘restrR_graph R’ >>
  simp[]
QED

Definition univnodes_def:
  univnodes g ⇔ nodes g = UNIV
End

Theorem univnodes_univR_graph[simp]:
  univnodes (univR_graph R)
Proof
  simp[univnodes_def]
QED

Theorem univnodes_graph_relation_bij:
  BIJ adjacent { g:'a relgraph | univnodes g } UNIV
Proof
  simp[BIJ_DEF, INJ_IFF, SURJ_DEF] >> conj_tac
  >- (qx_genl_tac [‘g1’, ‘g2’] >> rpt strip_tac >>
      simp[ulabgraph_component_equality, Once EQ_IMP_THM] >>
      rpt strip_tac >- gs[univnodes_def] >>
      simp[FUN_EQ_THM]) >>
  qx_gen_tac ‘R’ >> qexists ‘univR_graph R’ >> simp[]
QED

Theorem univnodes_graph_symrelation_bij:
  BIJ adjacent { g : (α,INF_OK,SL_OK) udulgraph | univnodes g }
               { r : α -> α -> bool | symmetric r }
Proof
  simp[BIJ_DEF, INJ_IFF, SURJ_DEF, relationTheory.symmetric_def,
       adjacent_SYM] >> conj_tac
  >- (simp[ulabgraph_component_equality] >> qx_genl_tac [‘g1’, ‘g2’] >>
      strip_tac >> simp[Once EQ_IMP_THM] >> gs[univnodes_def] >>
      simp[FUN_EQ_THM]) >>
  qx_gen_tac ‘R’ >> strip_tac >>
  qexists ‘graph_ABS <| nodes := UNIV;
                        edges := {(x,y,()) | R x y };
                        nlab := K ();
                        nfincst := (:INF_OK);
                        dircst := (:undirectedG) ;
                        slcst := (:SL_OK) ; (* self-loops allowed *)
                        edgecst := (:unit);
                     |>’ >>
  qmatch_abbrev_tac ‘univnodes (graph_ABS G0) ∧ _’ >>
  ‘G0.nodes = UNIV ∧ G0.edges = {(x,y,()) | R x y}’ by simp[Abbr‘G0’] >>
  ‘wfgraph G0’
    by (simp[wfgraph_def, ITSELF_UNIQUE, itself2set_def, finite_cst_def] >>
        simp[PULL_EXISTS] >>
        simp[edge_cst_def, SF CONJ_ss, PULL_EXISTS, INSERT2_lemma] >>
        rpt strip_tac >> gvs[]
        >- (simp[SF DNF_ss] >> simp[GSPEC_OR, GSPEC_lemma] >> rw[])
        >- (simp[GSPEC_lemma] >> rw[])
        >- (simp[SF CONJ_ss, SF DNF_ss] >>
            simp[GSPEC_OR, CARD_UNION_EQN, DECIDE “2 - y = 2 ⇔ y = 0”] >>
            simp[EXTENSION]) >>
        simp[SF CONJ_ss, SF DNF_ss] >>
        simp[GSPEC_OR, CARD_UNION_EQN, DECIDE “2 - y = 2 ⇔ y = 0”] >>
        simp[EXTENSION]) >>
  simp[univnodes_def, nodes_def, #repabs_pseudo_id tydefrec] >>
  simp[FUN_EQ_THM, edges_def, adjacent_def, #repabs_pseudo_id tydefrec]
QED

(* ----------------------------------------------------------------------
    graph measurements
   ---------------------------------------------------------------------- *)

Definition gsize_def:
  gsize (g : (α,δ,'ec,'ei,finiteG,'nl,σ)graph) = CARD $ nodes g
End

Overload order = “gsize”

Theorem FINITE_nodes[simp]:
  FINITE (nodes (G:('a,'dir,'ec,'el,finiteG,'nl,'sl)graph))
Proof
  simp[nodes_def] >>
  ‘wfgraph (graph_REP G)’ by simp[#termP_term_REP tydefrec] >>
  gs[wfgraph_def, ITSELF_UNIQUE, finite_cst_def, itself2set_def]
QED

Theorem gsize_addNode:
  n ∉ nodes g ⇒ gsize (addNode n l g) = gsize g + 1
Proof
  simp[gsize_def]
QED

Theorem gsize_EQ0[simp]:
  (gsize g = 0 ⇔ g = emptyG) ∧
  (0 = gsize g ⇔ g = emptyG)
Proof
  simp[gsize_def]
QED

Theorem gsize_emptyG[simp]:
  gsize emptyG = 0
Proof
  simp[gsize_def]
QED

Theorem FINITE_edges:
  FINITE $ edges (g : (α,δ,finiteG,σ)ulabgraph)
Proof
  irule SUBSET_FINITE >>
  qexists ‘nodes g × nodes g × UNIV’ >> simp[] >>
  simp[SUBSET_DEF, FORALL_PROD] >> rpt strip_tac >>
  irule incident_SUBSET_nodes >> simp[incident_def, EXISTS_PROD] >>
  metis_tac[]
QED

Definition edgesize_def:
  edgesize (g : (α,directedG,finiteG,σ) ulabgraph) = CARD $ edges g
End

Theorem edgesize_empty[simp]:
  edgesize emptyG = 0
Proof
  simp[edgesize_def]
QED

(* ----------------------------------------------------------------------
    pulling a graph apart and putting it back together
   ---------------------------------------------------------------------- *)

Definition addEdges0_def:
  addEdges0 eset0 (g: (α,directedG,'ec,'ei,ν,'nl,σ) graphrep) =
  let
      ecset = itself2set (:'ec) ;
      slokp = itself2bool (:σ) ;
      eset = if slokp then eset0 else { e | e ∈ eset0 ∧ ¬selfloop e } ;
      ns = { n | ∃m l. (m,n,l) ∈ eset ∨ (n,m,l) ∈ eset } ;
  in
    if itself2bool(:ν) ∧ INFINITE ns then g
    else if FINITE ecset then
      if CARD ecset = 1 then
        let edges_to_add = { (m,n,l) | (m,n,l) ∈ eset ∧
                                       ∀l'. (m,n,l') ∈ eset ⇒ l' = l }
        in
          g with <| edges :=
                      (g.edges DIFF
                       {(m,n,l0) | m,n,l0 | ∃l. (m,n,l) ∈ edges_to_add}) ∪
                      edges_to_add ;
                    nodes := g.nodes ∪ ns |>
      else if CARD ecset ≤ 2 then
        let edges_to_add =
            { (m,n,l) | (m,n,l) ∈ eset ∧ FINITE { l | (m,n,l) ∈ eset }} ;
        in
          g with <| edges := g.edges ∪ edges_to_add ; nodes := g.nodes ∪ ns |>
      else g with <| edges := g.edges ∪ eset ; nodes := g.nodes ∪ ns |>
    else g with <| edges := g.edges ∪ eset ; nodes := g.nodes ∪ ns |>
End

Theorem silly_image_lemma[local]:
  FINITE s ∧ t = IMAGE f s ⇒ FINITE t
Proof
  simp[]
QED

Theorem wfgraph_addEdges0:
  wfgraph (g:(α,directedG,β,γ,ν,'nl,σ) graphrep) ⇒ wfgraph (addEdges0 es g)
Proof
  REWRITE_TAC[addEdges0_def] >> BasicProvers.LET_ELIM_TAC >>
  Cases_on ‘itself2bool (:ν) ∧ INFINITE ns’ >- gs[] >>
  simp[] >>
  ‘finite_cst (univ (:ν)) (g.nodes ∪ ns)’
    by gs[itself2bool_def, finite_cst_def, wfgraph_def, ITSELF_UNIQUE] >>
  ‘¬slokp ⇒ ∀e. e ∈ eset ⇒ ¬selfloop e’ by simp[Abbr‘eset’] >>
  ‘∀e. e ∈ g.edges ⇒ incident e ⊆ g.nodes ∪ ns’
    by (gs[wfgraph_def] >> metis_tac[SUBSET_TRANS, SUBSET_UNION]) >>
  ‘∀e. e ∈ eset ⇒ incident e ⊆ g.nodes ∪ ns’
    by (simp[Abbr‘eset’, Abbr‘ns’, FORALL_PROD] >> rw[] >>
        metis_tac[]) >>
  reverse $ Cases_on ‘FINITE ecset’ >> simp[]
  >- (qpat_x_assum ‘wfgraph g’ mp_tac >> simp[wfgraph_def, ITSELF_UNIQUE] >>
      strip_tac >>
      simp[DISJ_IMP_THM, FORALL_AND_THM] >>
      qpat_x_assum ‘edge_cst _ _ _ _’ mp_tac >>
      simp[edge_cst_def]) >>
  reverse $ Cases_on ‘CARD ecset = 1’ >> simp[]
  >- (reverse $ Cases_on ‘CARD ecset ≤ 2’ >> simp[]
      >- (qpat_x_assum ‘wfgraph g’ mp_tac >> simp[wfgraph_def, ITSELF_UNIQUE] >>
          strip_tac >>
          simp[DISJ_IMP_THM, FORALL_AND_THM] >>
          qpat_x_assum ‘edge_cst _ _ _ _’ mp_tac >>
          simp[edge_cst_def]) >>
      qpat_x_assum ‘wfgraph g’ mp_tac >> simp[wfgraph_def, ITSELF_UNIQUE] >>
      strip_tac >>
      simp[DISJ_IMP_THM, FORALL_AND_THM] >>
      rename [‘_ ∧ (¬slokp ⇒ ∀e. e ∈ eadds ⇒ ¬selfloop e) ∧ _’] >>
      simp[Abbr‘eadds’, PULL_EXISTS] >>
      qpat_x_assum ‘edge_cst _ _ _ _’ mp_tac >> simp[edge_cst_def] >>
      simp[SF DNF_ss] >> simp[GSPEC_OR] >> rw[] >>
      simp[SF CONJ_ss, INSERT2_lemma, SF DNF_ss] >> simp[GSPEC_OR] >> rw[] >>
      qmatch_goalsub_abbrev_tac ‘_ = _ ∧ _ ∈ eset ∧ P’ >>
      (reverse $ Cases_on ‘P’ >- simp[]) >>
      pop_assum mp_tac >> simp[markerTheory.Abbrev_def] >> strip_tac >>
      drule_then irule silly_image_lemma >>
      simp[EXTENSION] >> simp[EQ_IMP_THM, FORALL_AND_THM, PULL_EXISTS] >>
      qmatch_goalsub_abbrev_tac ‘(a,b,_) ∈ eset ⇒ _’ >>
      qexists ‘λl. (a,b,l)’ >> simp[]) >>
  qpat_x_assum ‘wfgraph g’ mp_tac >> simp[wfgraph_def, ITSELF_UNIQUE] >>
  strip_tac >> rename [‘(_,_,_) ∉ eadds’] >>
  ‘∀e. e ∈ eadds ⇒ e ∈ eset’ by simp[Abbr‘eadds’, PULL_EXISTS] >>
  simp[DISJ_IMP_THM, FORALL_AND_THM] >>
  qpat_x_assum ‘edge_cst _ _ _ _ ’ mp_tac >> simp[edge_cst_def] >>
  rpt strip_tac >~
  [‘FINITE _’, ‘incident _ = {a;b}’]
  >- (simp[SF DNF_ss] >> simp[GSPEC_OR] >> conj_tac >~
      [‘FINITE { e | e ∈ eadds ∧ incident e = {a;b}}’]
      >- (Q.UNABBREV_TAC ‘eadds’ >> simp_tac (srw_ss()) [] >>
          qpat_x_assum ‘∀e. _ ⇒ e ∈ eset’ kall_tac >>
          simp[PULL_EXISTS, SF CONJ_ss, SF DNF_ss, INSERT2_lemma] >>
          simp[GSPEC_OR] >> rpt strip_tac
          >- (Cases_on ‘a = b’ >> simp[] >>
              Cases_on ‘∃l. (b,b,l) ∈ eset ∧ ∀m. (b,b,m) ∈ eset ⇒ m = l’
              >- (pop_assum strip_assume_tac >>
                  ‘∀m. (b,b,m) ∈ eset ⇔ m = l’ by metis_tac[] >> simp[]) >>
              qmatch_abbrev_tac ‘FINITE A’ >>
              ‘A = ∅’ suffices_by simp[] >> simp[Abbr‘A’, EXTENSION] >>
              metis_tac[])
          >- (Cases_on ‘∃l. (a,b,l) ∈ eset ∧ ∀m. (a,b,m) ∈ eset ⇒ m = l’
              >- (pop_assum strip_assume_tac >>
                  ‘∀m. (a,b,m) ∈ eset ⇔ m = l’ by metis_tac[] >> simp[]) >>
              qmatch_abbrev_tac ‘FINITE A’ >>
              ‘A = ∅’ suffices_by simp[] >> simp[Abbr‘A’, EXTENSION] >>
              metis_tac[]) >>
          Cases_on ‘∃l. (b,a,l) ∈ eset ∧ ∀m. (b,a,m) ∈ eset ⇒ m = l’
          >- (pop_assum strip_assume_tac >>
              ‘∀m. (b,a,m) ∈ eset ⇔ m = l’ by metis_tac[] >> simp[]) >>
          qmatch_abbrev_tac ‘FINITE A’ >>
          ‘A = ∅’ suffices_by simp[] >> simp[Abbr‘A’, EXTENSION] >>
          metis_tac[]) >>
      irule SUBSET_FINITE >>
      first_assum $ irule_at Any >> simp[SUBSET_DEF] >> metis_tac[]) >~
  [‘CARD _ ≤ 1’]
  >- (irule $ iffRL CARD_LE1 >> simp[SF DNF_ss, SF CONJ_ss] >>
      simp[GSPEC_OR] >>
      rename [‘(m,n,_) ∈ eadds’, ‘(m,n,_) ∉ eadds’] >>
      reverse $ Cases_on ‘∃l. (m,n,l) ∈ eadds’
      >- (‘∀l. (m,n,l) ∉ eadds’ by metis_tac[] >> simp[] >>
          first_x_assum $ qspecl_then [‘m’, ‘n’] assume_tac >>
          drule_at_then (Pos (el 2)) irule (iffLR $ CARD_LE1) >>
          irule SUBSET_FINITE >> first_assum $ irule_at Any >>
          simp[SUBSET_DEF, PULL_EXISTS] >> metis_tac[]) >>
      ‘(∀l. (m,n,l) ∉ eadds) = F’ by metis_tac[] >> simp[] >>
      pop_assum kall_tac >> pop_assum strip_assume_tac >>
      disj2_tac >> qexists ‘(m,n,l)’ >> simp[EXTENSION] >>
      qpat_x_assum ‘∀e. e ∈ eadds ⇒ e ∈ eset’ kall_tac >>
      simp[Abbr‘eadds’] >> pop_assum mp_tac >> simp[] >> metis_tac[])
QED

Definition addEdges_def:
  addEdges es g = graph_ABS $ addEdges0 es $ graph_REP g
End

Theorem nodes_addEdges_allokgraph:
  nodes (addEdges es0 g : (α,β,γ) allokdirgraph) =
  nodes g ∪ BIGUNION (IMAGE incident es0)
Proof
  simp[nodes_def, addEdges_def, #repabs_pseudo_id tydefrec, wfgraph_addEdges0,
       #termP_term_REP tydefrec] >>
  simp[addEdges0_def, itself2set_def] >>
  simp[Once EXTENSION, PULL_EXISTS, EXISTS_PROD] >> metis_tac[]
QED

Theorem nodes_addEdges_fdirg:
  FINITE es ⇒
  nodes (addEdges es g : (α,β,γ) fdirgraph) =
  nodes g ∪ BIGUNION (IMAGE incident es)
Proof
  simp[nodes_def, addEdges_def, #repabs_pseudo_id tydefrec, wfgraph_addEdges0,
       #termP_term_REP tydefrec] >>
  simp[addEdges0_def, itself2set_def] >> strip_tac >>
  qabbrev_tac ‘touching = { n | ∃m l. (m,n,l) ∈ es ∨ (n,m,l) ∈ es}’ >>
  ‘touching = BIGUNION (IMAGE incident es)’
    by (simp[Abbr‘touching’, Once EXTENSION, PULL_EXISTS, EXISTS_PROD] >>
        metis_tac[]) >>
  simp[PULL_EXISTS]
QED


Theorem nlabelfun_addEdges[simp]:
  nlabelfun (addEdges es g) = nlabelfun g
Proof
  simp[addEdges_def, nlabelfun_def, #repabs_pseudo_id tydefrec,
       wfgraph_addEdges0, #termP_term_REP tydefrec] >>
  rw[addEdges0_def]
QED

Theorem addEdges_EMPTY[simp]:
  addEdges ∅ g = g
Proof
  simp[addEdges_def, #termP_term_REP tydefrec, wfgraph_addEdges0,
       SYM $ #term_REP_11 tydefrec, #repabs_pseudo_id tydefrec] >>
  simp[addEdges0_def] >>
  simp[theorem "graphrep_component_equality"]
QED

Theorem addEdges_SING[simp]:
  addEdges {(m,n,l)} g = addEdge m n l (g: (α,directedG,'ec,β,ν,'nl,σ) graph)
Proof
  simp[addEdges_def, #termP_term_REP tydefrec, wfgraph_addEdges0,
       wfgraph_addEdge0, #repabs_pseudo_id tydefrec, addEdge_def,
       #term_ABS_pseudo11 tydefrec] >>
  REWRITE_TAC[addEdges0_def] >> BasicProvers.LET_ELIM_TAC >>
  ‘FINITE eset’ by rw[Abbr‘eset’, SF CONJ_ss, GSPEC_lemma] >>
  ‘ns = BIGUNION (IMAGE incident eset)’
    by (simp[Once EXTENSION, PULL_EXISTS, Abbr‘ns’, EXISTS_PROD] >>
        metis_tac[]) >>
  ‘FINITE ns’ by simp[PULL_EXISTS, FORALL_PROD] >>
  qpat_x_assum ‘ns = _’ kall_tac >>
  simp[] >>
  Cases_on ‘¬slokp ∧ m = n’ >> gvs[] >> gs[Abbr‘eset’]
  >- (gs[SF CONJ_ss] >> markerLib.UNABBREV_ALL_TAC>> gvs[] >>
      simp[addEdge0_def, edge0_def, ITSELF_UNIQUE])
  >- (‘ns = {m;n} ∧ edges_to_add = {(m,n,l)} ∧ edges_to_add' = {(m,n,l)}’
        by (simp[Abbr‘edges_to_add'’, Abbr‘edges_to_add’, Abbr‘ns’] >>
            simp[EXTENSION] >> Cases_on ‘slokp’ >> gvs[] >> metis_tac[]) >>
      gvs[] >>
      Cases_on ‘FINITE ecset’ >> simp[]
      >- (Cases_on ‘CARD ecset = 1’ >> simp[]
          >- (simp[addEdge0_def, edge0_def, ITSELF_UNIQUE] >>
              simp[theorem "graphrep_component_equality"] >>
              Cases_on ‘m = n’ >> gvs[] >>
              simp[EXTENSION]) >>
          simp[addEdge0_def, edge0_def, ITSELF_UNIQUE] >>
          Cases_on ‘m = n’ >> gvs[SF CONJ_ss]) >>
      simp[addEdge0_def, edge0_def, ITSELF_UNIQUE] >>
      Cases_on ‘m = n’ >> gvs[SF CONJ_ss])
QED

Theorem edges_addEdges_allokdirgraph:
  edges (addEdges es (g : (α,β,γ)allokdirgraph)) = es ∪ edges g
Proof
  simp[addEdges_def, nlabelfun_def, #repabs_pseudo_id tydefrec,
       wfgraph_addEdges0, #termP_term_REP tydefrec, edges_def] >>
  rw[addEdges0_def] >> gs[itself2set_def, UNION_COMM]
QED

Theorem edges_addEdges_fdirgraph:
  FINITE es ⇒ edges (addEdges es (g : (α,β,γ) fdirgraph)) = es ∪ edges g
Proof
  simp[addEdges_def, nlabelfun_def, #repabs_pseudo_id tydefrec,
       wfgraph_addEdges0, #termP_term_REP tydefrec, edges_def] >>
  rw[addEdges0_def] >> gs[itself2set_def] >~
  [‘INFINITE _’]
  >- (‘FINITE { n | ∃m l. (m,n,l) ∈ es ∨ (n,m,l) ∈ es}’ suffices_by simp[] >>
      qpat_x_assum ‘INFINITE _’ kall_tac >>
      simp[EXISTS_OR_THM, GSPEC_OR] >> conj_tac >>
      drule_then irule silly_image_lemma
      >- (qexists ‘FST o SND’ >> simp[EXTENSION, FORALL_PROD, EXISTS_PROD]) >>
      qexists ‘FST’ >> simp[EXTENSION, FORALL_PROD, EXISTS_PROD]) >>
  ‘∀m n. FINITE {l | (m,n,l) ∈ es}’
    by (rpt gen_tac >>
        ‘{ l | (m,n,l) ∈ es} = IMAGE (SND o SND) {(m,n,l) | l | (m,n,l) ∈ es}’
          by simp[EXTENSION, FORALL_PROD, EXISTS_PROD] >>
        simp[] >> irule IMAGE_FINITE >>
        irule SUBSET_FINITE >> qexists ‘es’ >> simp[SUBSET_DEF, PULL_EXISTS])>>
  simp[] >> simp[EXTENSION, FORALL_PROD] >> metis_tac[]
QED

Theorem addEdges_INSERT_fdirG:
  ∀es m n l g.
    FINITE es ⇒
    addEdges ((m,n,l) INSERT es) (g:(α,β,γ)fdirgraph) =
    addEdge m n l (addEdges (es DELETE (m,n,l)) g)
Proof
  simp[gengraph_component_equality, edges_addEdges_fdirgraph, edges_addEdge,
       oneEdge_max_def, itself2set_def, nodes_addEdges_fdirg] >>
  rpt strip_tac >>
  simp[Once EXTENSION, PULL_EXISTS] >> gen_tac >> eq_tac >> rpt strip_tac >>
  simp[EXISTS_PROD] >> rename [‘x ∈ incident e’] >> PairCases_on ‘e’ >>
  gvs[] >> metis_tac[]
QED

Theorem addEdges_addEdge_fdirG:
  FINITE es ⇒
  addEdges es (addEdge s d lab (G:(α,β,γ)fdirgraph)) =
  addEdges ((s,d,lab) INSERT es) G
Proof
  simp[gengraph_component_equality, edges_addEdges_fdirgraph, edges_addEdge,
       oneEdge_max_def, itself2set_def, nodes_addEdges_fdirg] >> rw[] >>
  simp[Once EXTENSION, PULL_EXISTS] >> metis_tac[]
QED

Theorem addEdges_addEdges_fdirG:
  FINITE es1 ∧ FINITE es2 ⇒
  addEdges es1 (addEdges es2 (G:(α,β,γ)fdirgraph)) =
  addEdges (es1 ∪ es2) G
Proof
  simp[gengraph_component_equality, edges_addEdges_fdirgraph, edges_addEdge,
       oneEdge_max_def, itself2set_def, nodes_addEdges_fdirg] >> rw[] >>
  simp[Once EXTENSION, PULL_EXISTS] >> metis_tac[]
QED

Definition removeNode0_def:
  removeNode0 n grep =
  grep with <| nodes := grep.nodes DELETE n ;
               edges := grep.edges DIFF { e | n ∈ incident e } ;
               nlab := grep.nlab ⦇ n ↦ ARB ⦈ |>
End

Theorem wfgraph_removeNode0:
  wfgraph g ⇒ wfgraph (removeNode0 n g)
Proof
  simp[wfgraph_def, removeNode0_def, ITSELF_UNIQUE, DISJ_IMP_THM,
       FORALL_AND_THM, combinTheory.APPLY_UPDATE_THM] >>
  rw[SUBSET_DEF, finite_cst_def] >> rpt strip_tac >> gs[] >~
  [‘edge_cst _ _ _ (_ DIFF _)’]
  >- (gs[edge_cst_def] >> rw[] >> gs[SF CONJ_ss] >>~-
      ([‘incident edge = {a;b}’],
       (first_x_assum (irule o cj 1) ORELSE first_x_assum (irule o cj 2)) >>
       metis_tac[]) >~
      [‘FINITE _’, ‘CARD _ ≤ 2’]
      >- (irule SUBSET_FINITE >> first_assum $ irule_at Any >>
          simp[SUBSET_DEF] >> metis_tac[]) >~
      [‘CARD _ = 1’, ‘CARD _ ≤ 1’, ‘incident _ = {a}’]
      >- (irule arithmeticTheory.LESS_EQ_TRANS >>
          first_assum $ irule_at (Pat ‘_ ≤ 1’) >>
          irule_at Any CARD_SUBSET >>
          ONCE_REWRITE_TAC [prove(“{m} = {m;m}”, simp[])] >>
          first_assum $ irule_at Any >> simp[SUBSET_DEF] >>
          metis_tac[]) >>
      rename [‘a ≠ b ∧ a ≠ c’] >> Cases_on ‘a ≠ b ∧ a ≠ c’ >> gs[])
  >- metis_tac[]
QED

Definition removeNode_def:
  removeNode n g = graph_ABS $ removeNode0 n $ graph_REP g
End

Theorem nodes_removeNode[simp]:
  nodes (removeNode n g) = nodes g DELETE n
Proof
  simp[#termP_term_REP tydefrec, wfgraph_removeNode0, removeNode_def,
       nodes_def, #repabs_pseudo_id tydefrec] >>
  simp[removeNode0_def]
QED

Theorem gsize_removeNode[simp]:
  n ∈ nodes g ⇒ gsize (removeNode n g) = gsize g - 1
Proof
  simp[gsize_def]
QED

Theorem edges_removeNode[simp]:
  edges (removeNode n g) = edges g DIFF { e | n ∈ incident e}
Proof
  simp[#termP_term_REP tydefrec, wfgraph_removeNode0, removeNode_def,
       edges_def, #repabs_pseudo_id tydefrec] >>
  simp[removeNode0_def]
QED

Theorem nlabelfun_removeNode[simp]:
  nlabelfun (removeNode n g) = (nlabelfun g)⦇ n ↦ ARB ⦈
Proof
  simp[#termP_term_REP tydefrec, wfgraph_removeNode0, removeNode_def,
       nlabelfun_def, #repabs_pseudo_id tydefrec] >>
  simp[removeNode0_def]
QED

Theorem removeNode_addNode[simp]:
  n ∉ nodes g ⇒ removeNode n (addNode n l g) = g
Proof
  simp[gengraph_component_equality] >>
  simp[EXTENSION, SF CONJ_ss] >>
  metis_tac[incident_SUBSET_nodes]
QED

Definition edgesTo_def:
  edgesTo g n = { (m,n,l) | m,l | (m,n,l) ∈ edges g }
End

Definition edgesFrom_def:
  edgesFrom g m = { (m,n,l) | n,l | (m,n,l) ∈ edges g }
End

Definition isolated_def:
  isolated n g ⇔ n ∈ nodes g ∧ edgesTo g n = ∅ ∧ edgesFrom g n = ∅
End

Theorem isolated_addNode_removeNode:
  isolated n g ⇔ addNode n (nlabelfun g n) (removeNode n g) = g
Proof
  rw[isolated_def, gengraph_component_equality, edgesTo_def, edgesFrom_def,
     EQ_IMP_THM] >>
  gs[EXTENSION, FORALL_PROD] >> metis_tac[]
QED

Theorem FINITE_edges_fdir[simp]:
  FINITE (edges (g : (α,β,γ) fdirgraph))
Proof
  simp[edges_def] >>
  ‘wfgraph (graph_REP g)’ by simp[#termP_term_REP tydefrec] >>
  gs[wfgraph_def, ITSELF_UNIQUE, finite_cst_def, itself2set_def, edge_cst_def]>>
  ‘(graph_REP g).edges =
   BIGUNION (IMAGE (λ(m,n). { e | e ∈ (graph_REP g).edges ∧ incident e = {m;n}})
             ((graph_REP g).nodes × (graph_REP g).nodes))’
    by (simp[Once EXTENSION, PULL_EXISTS, EXISTS_PROD, FORALL_PROD] >>
        simp[INSERT2_lemma, SF DNF_ss] >>
        gs[FORALL_PROD] >> metis_tac[]) >>
  pop_assum SUBST1_TAC >>
  simp[PULL_EXISTS, FORALL_PROD]
QED

Theorem decomposition_fdir:
  ∀g. g = emptyG ∨
      ∃n l es g0 : (α,β,γ) fdirgraph.
        n ∉ nodes g0 ∧ FINITE es ∧ g = addEdges es (addNode n l g0) ∧
        (∀e. e ∈ es ⇒ n ∈ incident e) ∧
        (∀e m . e ∈ es ∧ m ∈ incident e ⇒ m = n ∨ m ∈ nodes g0) ∧
        gsize g = gsize g0 + 1
Proof
  strip_tac >> Cases_on ‘g = emptyG’ >> simp[] >>
  ‘nodes g ≠ ∅’ by simp[] >>
  ‘0 < gsize g’ by (CCONTR_TAC >> gs[]) >>
  gs[GSYM MEMBER_NOT_EMPTY] >> rename [‘n ∈ nodes g’] >>
  qabbrev_tac ‘es = { e | e ∈ edges g ∧ n ∈ incident e }’ >>
  ‘FINITE es’
    by (irule SUBSET_FINITE >> qexists ‘edges g’ >> simp[] >>
        simp[SUBSET_DEF, Abbr‘es’]) >>
  qexistsl [‘n’, ‘nlabelfun g n’, ‘es’, ‘removeNode n g’] >> simp[] >>
  rpt conj_tac >~
  [‘_ ∈ es ∧ _ ∈ incident _ ⇒ _’]
  >- (simp[Abbr‘es’] >> metis_tac[incident_SUBSET_nodes]) >~
  [‘_ ∈ es ⇒ n ∈ incident _’] >- (simp[Abbr‘es’]) >>
  simp[gengraph_component_equality, nodes_addEdges_fdirg,
       edges_addEdges_fdirgraph] >> conj_tac >>
  simp[Once EXTENSION, PULL_EXISTS]
  >- (simp[Abbr‘es’] >> metis_tac[incident_SUBSET_nodes]) >>
  simp[Abbr‘es’] >> metis_tac[]
QED

Theorem fdirG_induction:
  ∀P. P emptyG ∧
      (∀n l es g0. n ∉ nodes g0 ∧ FINITE es ∧
                   (∀e. e ∈ es ⇒ n ∈ incident e) ∧
                   (∀e m. e ∈ es ∧ m ∈ incident e ⇒ m = n ∨ m ∈ nodes g0) ∧
                   P g0 ⇒ P (addEdges es (addNode n l g0))) ⇒
      ∀g : (α,β,γ) fdirgraph. P g
Proof
  rpt strip_tac >>
  Induct_on ‘gsize g’ >> rw[] >>
  ‘g ≠ emptyG’ by (strip_tac >> gs[]) >>
  qspec_then ‘g’ strip_assume_tac decomposition_fdir >> gs[] >>
  last_x_assum irule >> simp[] >> metis_tac[]
QED



Definition closed_neighborhood_def:
  closed_neighborhood g v = v INSERT { m | adjacent g v m }
End

Definition ON_def: (* open neighbourhood *)
  ON g A = { v | ∃a. a ∈ A ∧ adjacent g a v }
End

Definition CN_def:
  CN g A = BIGUNION $ IMAGE (closed_neighborhood g) A
End

Theorem CN_ON_UNION:
  CN g A = A ∪ ON g A
Proof
  simp[CN_def, ON_def, closed_neighborhood_def, Once EXTENSION] >>
  dsimp[PULL_EXISTS] >> metis_tac[]
QED

(* doesn't add any nodes *)
Definition fsgAddEdges0_def:
  fsgAddEdges0 (es0: α set set) g0 =
  let
    es = { (m,n,()) | m ≠ n ∧ m ∈ g0.nodes ∧ n ∈ g0.nodes ∧ {m;n} ∈ es0 }
  in
    g0 with edges := g0.edges ∪ es
End

Theorem wfgraph_fsgAddEdges0:
  FINITE (itself2set g0.nfincst) ∧ ¬itself2bool (g0.dircst) ∧
  wfgraph g0 ⇒
  wfgraph (fsgAddEdges0 es g0)
Proof
  simp[wfgraph_def, fsgAddEdges0_def, SF CONJ_ss, edge_cst_def,
       finite_cst_def] >> rw[] >>
  simp[incident_def] >~
  [‘{m;n} ∈ es’] >- metis_tac[pred_setTheory.INSERT_COMM] >~
  [‘FINITE (GSPEC _)’]
  >- (irule SUBSET_FINITE >> qexists ‘g0.nodes × g0.nodes × UNIV’ >> simp[] >>
      simp[SUBSET_DEF, FORALL_PROD, INSERT2_lemma, SF DNF_ss] >>
      gs[FORALL_PROD, incident_def] >> metis_tac[])
  >- simp[SF DNF_ss, SF CONJ_ss]
  >- (simp[SF DNF_ss, SF CONJ_ss, GSPEC_OR] >> gs[PULL_EXISTS] >>
      qmatch_abbrev_tac ‘CARD (A1 ∪ A2) = 2’ >>
      ‘A2 ⊆ A1’
        by (simp[SUBSET_DEF, Abbr‘A2’, Abbr‘A1’, PULL_EXISTS,
                 INSERT2_lemma] >>
            ‘flip_edge e ∈ g0.edges’ by simp[] >> PairCases_on ‘e’ >>
            gs[INSERT2_lemma, flip_edge_def] >> rw[] >> simp[]) >>
      ‘A1 ∪ A2 = A1’ by (simp[EXTENSION] >> gs[SUBSET_DEF] >> metis_tac[]) >>
      simp[Abbr‘A1’] >> first_x_assum irule >> metis_tac[])
  >- (qmatch_abbrev_tac ‘CARD A = 2’ >>
      ‘A = {(m,n,()); (n,m,())}’ suffices_by simp[] >>
      simp[Abbr‘A’, Once EXTENSION] >> simp[FORALL_PROD] >>
      rw[EQ_IMP_THM] >> gvs[INSERT2_lemma] >>
      metis_tac[pred_setTheory.INSERT_COMM])
QED

Definition fsgAddEdges_def:
  fsgAddEdges es (g : α fsgraph) =
  graph_ABS (fsgAddEdges0 es $ graph_REP g)
End

Theorem nodes_fsgAddEdges[simp]:
  nodes (fsgAddEdges es g) = nodes g
Proof
  simp[nodes_def, fsgAddEdges_def, #repabs_pseudo_id tydefrec,
       #termP_term_REP tydefrec, wfgraph_fsgAddEdges0, ITSELF_UNIQUE] >>
  simp[fsgAddEdges0_def]
QED

Theorem edges_fsgAddEdges:
  edges (fsgAddEdges es g) =
    edges g ∪
    { (m,n,()) | {m;n} ∈ es ∧ m ≠ n ∧ m ∈ nodes g ∧ n ∈ nodes g }
Proof
  simp[edges_def, fsgAddEdges_def, #repabs_pseudo_id tydefrec, nodes_def,
       #termP_term_REP tydefrec, wfgraph_fsgAddEdges0, ITSELF_UNIQUE] >>
  simp[fsgAddEdges0_def] >>
  simp[EXTENSION, FORALL_PROD] >> rw[EQ_IMP_THM] >> simp[]
QED

Theorem adjacent_fsgEdges[simp]:
  adjacent (fsgAddEdges es g) m n ⇔
    adjacent g m n ∨
    m ≠ n ∧ m ∈ nodes g ∧ n ∈ nodes g ∧ {m;n} ∈ es
Proof
  simp[adjacent_def, edges_fsgAddEdges] >> iff_tac >> rw[] >> simp[]
QED

Theorem FINITE_fsg_edges[simp]:
  FINITE (edges (g : α fsgraph))
Proof
  irule SUBSET_FINITE >> qexists ‘nodes g × nodes g × UNIV’ >> simp[] >>
  rw[SUBSET_DEF, FORALL_PROD] >> irule incident_SUBSET_nodes >>
  simp[EXISTS_PROD] >> metis_tac[]
QED

Theorem fsg_selfloop:
  (m,n,()) ∈ edges (g : α fsgraph) ⇒ m ≠ n
Proof
  simp[edges_def] >> rpt strip_tac >>
  ‘wfgraph (graph_REP g)’ by simp[#termP_term_REP tydefrec] >>
  gs[wfgraph_def, ITSELF_UNIQUE, FORALL_PROD]
QED

Definition valid_edges_def:
  valid_edges es s ⇔ ∀e. e ∈ es ⇒ e ⊆ s ∧ FINITE e ∧ CARD e = 2
End

Definition fsgedges_def:
  fsgedges (g: α fsgraph) = { {a;b} | adjacent g a b }
End

Theorem fsgedges_emptyG[simp]:
  fsgedges emptyG = ∅
Proof
  simp[fsgedges_def]
QED

Theorem fsgedges_addNode[simp]:
  fsgedges (addNode n u g) = fsgedges g
Proof
  simp[fsgedges_def]
QED

Theorem CARDEQ2:
  FINITE s ⇒ (CARD s = 2 ⇔ ∃a b. a ≠ b ∧ s = {a;b})
Proof
  strip_tac >> simp[EQ_IMP_THM, PULL_EXISTS] >>
  Cases_on ‘s’ >> gs[] >> rename [‘a ∉ s’] >>
  Cases_on ‘s’ >> gs[] >> metis_tac[]
QED

Theorem fsgedges_fsgAddEdges:
  valid_edges es (nodes g) ⇒
  fsgedges (fsgAddEdges es g) = es ∪ fsgedges g
Proof
  simp[fsgedges_def, valid_edges_def] >> strip_tac >>
  simp[Once EXTENSION] >> qx_gen_tac ‘ed’ >> iff_tac >> rw[] >>
  simp[SF SFY_ss]
  >- metis_tac[]
  >- (gs[CARDEQ2, SUBSET_DEF, PULL_EXISTS, SF CONJ_ss, DISJ_IMP_THM,
         FORALL_AND_THM] >>
      first_x_assum $ drule >> simp[PULL_EXISTS] >> rw[] >>
      metis_tac[]) >>
  metis_tac[]
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
      ‘m ≠ p’ by simp[fsg_selfloop, SF SFY_ss] >>
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

Theorem FINITE_least_measure_ind:
  ∀f P. P {} ∧
        (∀a s. a ∉ s ∧ (∀b. b ∈ s ⇒ f a ≤ f b) ∧ P s ⇒ P (a INSERT s)) ⇒
        ∀s. FINITE s ⇒ P s
Proof
  rpt gen_tac >> strip_tac >> Induct_on ‘CARD s’ >> rpt strip_tac >>
  gvs[] >> ‘s ≠ ∅’ by (strip_tac >> gvs[]) >>
  qspecl_then [‘λa. a ∈ s’, ‘f’] mp_tac arithmeticTheory.WOP_measure >>
  impl_tac >- gs[MEMBER_NOT_EMPTY] >>
  rw[] >> rename [‘a ∈ s’] >>
  drule_then (qx_choose_then ‘s0’ strip_assume_tac) (iffLR DECOMPOSITION) >>
  gvs[]
QED

Theorem FINITE_sets_have_descending_measure_lists:
  ∀s. FINITE s ⇒
      ∃es. SORTED (inv $<=) (MAP f es) ∧ set es = s ∧
           ALL_DISTINCT es
Proof
  Induct_on ‘FINITE’ using FINITE_least_measure_ind >> qexists ‘f’ >>
  simp[PULL_EXISTS] >> rpt strip_tac >>
  rename [‘¬MEM a es’] >> qexists ‘es ++ [a]’ >>
  simp[EXTENSION, AC DISJ_ASSOC DISJ_COMM, listTheory.ALL_DISTINCT_APPEND] >>
  simp[SORTED_APPEND, listTheory.MEM_MAP, PULL_EXISTS]
QED

Theorem descending_measure_lists_unique:
  ∀es1 es2. SORTED (inv $<=) (MAP f es1) ∧ SORTED (inv $<=) (MAP f es2) ∧
            set es1 = set es2 ∧ ALL_DISTINCT es1 ∧ ALL_DISTINCT es2 ⇒
            MAP f es1 = MAP f es2
Proof
  Induct >> simp[SORTED_EQ, listTheory.MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >> simp[listTheory.MAP_EQ_CONS] >>
  Cases_on ‘es2’ >> gvs[SORTED_EQ, listTheory.MEM_MAP, PULL_EXISTS] >>
  rename [‘h1 INSERT set es1 = h2 INSERT set es2’] >>
  Cases_on ‘h1 = h2’
  >- (gvs[] >> first_x_assum irule >> simp[] >>
      qpat_x_assum ‘_ INSERT _ = _ INSERT _’ mp_tac >>
      simp[EXTENSION] >> metis_tac[]) >>
  ‘MEM h1 es2 ∧ MEM h2 es1’ by (gs[EXTENSION] >> metis_tac[]) >>
  ‘f h1 = f h2’ by metis_tac[arithmeticTheory.EQ_LESS_EQ] >> simp[] >>
  ‘∃p2 s2. es2 = p2 ++ [h1] ++ s2’
    by metis_tac[listTheory.MEM_SPLIT_APPEND_first] >>
  gvs[listTheory.ALL_DISTINCT_APPEND, DISJ_IMP_THM, FORALL_AND_THM] >>
  first_x_assum $ qspec_then ‘p2 ++ [h2] ++ s2’ mp_tac >> simp[] >>
  disch_then irule >>
  simp[listTheory.ALL_DISTINCT_APPEND, DISJ_IMP_THM, FORALL_AND_THM] >>
  qpat_x_assum ‘_ INSERT _ = _’ mp_tac >>
  simp[EXTENSION] >> metis_tac[]
QED

Theorem FINITE_fsgedges[simp]:
  ∀g. FINITE (fsgedges g)
Proof
  Induct using fsg_induction >> simp[fsgedges_fsgAddEdges]
QED

Definition fsgsize_def:
  fsgsize (g : α fsgraph) = CARD (fsgedges g)
End

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
  dsimp[degree_def, FUN_EQ_THM, fsgedges_fsgAddEdges, GSPEC_OR]
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
       fsgedges_fsgAddEdges] >>
  ‘degree (fsgAddEdges es (addNode n () g)) n = CARD es’
    by (‘∀e. e ∈ fsgedges g ⇒ n ∉ e’
          by (simp[fsgedges_def, PULL_EXISTS] >>
              metis_tac[adjacent_members]) >>
        dsimp[degree_def, fsgedges_fsgAddEdges, SF CONJ_ss]) >>
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

val  _ = export_theory();
