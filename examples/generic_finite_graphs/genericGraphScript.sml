open HolKernel Parse boolLib bossLib;

open pred_setTheory pairTheory bagTheory

(* Material on finite simple graphs mechanised from
     "Combinatorics and Graph Theory" by Harris, Hirst, and Mossinghoff
 *)

val _ = new_theory "genericGraph";

Datatype: diredge = directed α α 'label
End
Datatype: hyperedge = hyper (α set) 'label
End
Datatype:
  core_edge = cDE (('a,'l) diredge) | cHE (('a,'l) hyperedge)
End
Overload DE = “λm n l. cDE (directed m n l)”
Overload HE = “λns l. cHE (hyper ns l)”

Theorem core_edge_cases:
  ∀e. (∃m n l. e = DE m n l) ∨ (∃ns l. e = HE ns l)
Proof
  Cases >> simp[] >>
  metis_tac[TypeBase.nchotomy_of “:('a,'l) diredge”,
            TypeBase.nchotomy_of “:('a,'l) hyperedge”]
QED

val _ = TypeBase.export [
  TypeBasePure.put_nchotomy core_edge_cases
             (valOf (TypeBase.read {Tyop = "core_edge",
                                    Thy = "genericGraph"}))
  ];

Definition is_directed_edge_def[simp]:
  is_directed_edge (cDE _ ) = T ∧
  is_directed_edge (cHE _ ) = F
End
Definition denodes_def[simp]:
  denodes (directed m n l) = (m,n)
End
Definition henodes_def[simp]:
  henodes (hyper ns l) = ns
End
Definition enodes_def[simp]:
  enodes (cDE de) = INL (denodes de) ∧
  enodes (cHE he) = INR (henodes he)
End

Theorem enodesEQ:
  (enodes e = INL (m,n) ⇔ ∃l. e = DE m n l) ∧
  (enodes e = INR ns ⇔ ∃l. e = HE ns l)
Proof
  Cases_on ‘e’ >> simp[]
QED

Theorem SING_EQ2[simp]:
  {x} = {a;b} ⇔ x = a ∧ a = b
Proof
  simp[EXTENSION] >> metis_tac[]
QED

Theorem CARDEQ2:
  FINITE s ⇒ (CARD s = 2 ⇔ ∃a b. a ≠ b ∧ s = {a;b})
Proof
  strip_tac >> simp[EQ_IMP_THM, PULL_EXISTS] >>
  Cases_on ‘s’ >> gs[] >> rename [‘a ∉ s’] >>
  Cases_on ‘s’ >> gs[] >> metis_tac[]
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

Definition incidentDE_def[simp]:
  incidentDE (directed n1 n2 lab) = {n1;n2}
End

Overload incidentHE = “henodes”
Overload henodes = “henodes”
Overload incident = “incidentHE”
Overload incident = “incidentDE”

Definition core_incident_def[simp]:
  core_incident (cDE de) = incident de ∧
  core_incident (cHE he) = incident he
End

Theorem FINITE_incident[simp]:
  FINITE (incidentDE de)
Proof
  Cases_on ‘de’ >> simp[]
QED

Theorem incident_EQ_SING:
  incident e = {m} ⇔ ∃l. e = directed m m l
Proof
  Cases_on ‘e’ >> simp[] >> metis_tac[]
QED

Definition selfloop_def[simp]:
  selfloop (directed m n lab) ⇔ m = n
End

Definition gen_selfloop_def[simp]:
  gen_selfloop (cDE de) = selfloop de ∧
  gen_selfloop (cHE he) = SING (henodes he)
End

Definition dirflip_edge_def[simp]:
  dirflip_edge (directed m n l) = directed n m l
End

Theorem dirflip_edge_inverts[simp]:
  dirflip_edge (dirflip_edge de) = de
Proof
  Cases_on ‘de’ >> simp[]
QED

Theorem dirflip_edge_11[simp]:
  dirflip_edge de1 = dirflip_edge de2 ⇔ de1 = de2
Proof
  map_every Cases_on [‘de1’, ‘de2’] >> simp[] >> metis_tac[]
QED

Definition flip_edge_def[simp]:
  flip_edge (cDE de) = cDE (dirflip_edge de) ∧
  flip_edge (cHE he) = cHE he
End

Theorem flip_edge_inverts[simp]:
  flip_edge (flip_edge e) = e
Proof
  Cases_on ‘e’ >> simp[]
QED

Theorem flip_edge_11[simp]:
  flip_edge e1 = flip_edge e2 ⇔ e1 = e2
Proof
  map_every Cases_on [‘e1’, ‘e2’] >> simp[] >> metis_tac[]
QED

Theorem dirflip_edge_EQ[simp]:
  (dirflip_edge de = directed a b l ⇔ de = directed b a l) ∧
  (directed a b l = dirflip_edge de ⇔ de = directed b a l)
Proof
  Cases_on ‘de’ >> simp[] >> metis_tac[]
QED

Theorem flip_edge_EQ[simp]:
  (flip_edge e = DE a b lab ⇔ e = DE b a lab) ∧
  (DE a b lab = flip_edge e ⇔ e = DE b a lab) ∧
  (flip_edge e = HE ns lab ⇔ e = HE ns lab) ∧
  (HE ns lab = flip_edge e ⇔ e = HE ns lab)
Proof
  Cases_on ‘e’ >> simp[] >> metis_tac[]
QED

Theorem incident_dirflip_edge[simp]:
  incident (dirflip_edge de) = incident de
Proof
  Cases_on ‘de’ >> simp[INSERT_COMM]
QED

Theorem incident_flip_edge[simp]:
  core_incident (flip_edge e) = core_incident e
Proof
  Cases_on ‘e’ >> simp[INSERT2_lemma]
QED

Definition hedge_label_def[simp]:
  hedge_label (hyper ns l) = l
End
Definition dedge_label_def[simp]:
  dedge_label (directed m n l) = l
End
Theorem dedge_label_dirflip_edge[simp]:
  dedge_label (dirflip_edge de) = dedge_label de
Proof
  Cases_on ‘de’ >> simp[]
QED

Definition edge_label_def[simp]:
  edge_label (cDE de) = dedge_label de ∧
  edge_label (cHE he) = hedge_label he
End

Theorem edge_label_flip_edge[simp]:
  ∀e. edge_label (flip_edge e) = edge_label e
Proof
  Cases>> simp[]
QED

Definition finite_cst_def:
  finite_cst cs A ⇔ (FINITE cs ⇒ FINITE A)
End

Overload set = “SET_OF_BAG”

Definition itself2set_def[simp]:
  itself2set (:'a) = univ(:'a)
End

Definition itself2bool_def:
  itself2bool x ⇔ FINITE $ itself2set x
End

Definition itself2boolopt_def:
  itself2boolopt x =
  let A = itself2set x
  in
    if FINITE A then
      if CARD A = 1 then SOME F
      else SOME T
    else NONE
End

Definition itself2_4_def:
  itself2_4 x =
  let A = itself2set x
  in
    if FINITE A then
      if CARD A = 1 then (F,F)
      else if CARD A = 2 then (F,T)
      else (T,F)
    else (T,T)
End

(* types of graph encoded with an itself2boolopt:

       directed      (SOME F)
       undirected    (SOME T)
       hypergraph    NONE
*)

(* constraining edge set sizes between any given set of nodes (possibly
   singleton if selfloops allowed; possibly with size > 2 if hypergraph)
   options are:
    - only one                (F,F)
    - only one per label      (F,T)
    - finite                  (T,F)
    - unconstrained           (T,T)
   (Necessarily infinitely many edges between any two nodes seems dumb.)
 *)

Definition only_one_edge_def:
  only_one_edge (ebag : ('a,'l) core_edge bag) ⇔
    ∀A e. e ∈ set ebag ∧ enodes e = A ⇒
          ebag e = 1 ∧
          (∀f. f ∈ set ebag ∧ enodes f = A ⇒ f = e)
End

Definition only_one_edge_per_label_def:
  only_one_edge_per_label (ebag : ('a,'l) core_edge bag) ⇔
    ∀e. e ∈ set ebag ⇒ ebag e = 1
End

Definition finite_edges_per_nodeset_def:
  finite_edges_per_nodeset (ebag : ('a,'l) core_edge bag) ⇔
    ∀A. FINITE { e | e ∈ set ebag ∧ core_incident e = A }
End

Definition edge_cst_def:
  edge_cst ecst dirp slp ebag ⇔
    (case itself2_4 ecst of
     | (F,F) => only_one_edge ebag
     | (F,T) => only_one_edge_per_label ebag
     | (T,F) => finite_edges_per_nodeset ebag
     | (T,T) => T) ∧
    case (itself2boolopt dirp, itself2bool slp) of
    | (NONE,   F) => (∀A e. e ∈ set ebag ∧ A = core_incident e ⇒
                            ¬is_directed_edge e ∧
                            (FINITE A ⇒ 2 ≤ CARD A))
    | (NONE,   T) => (∀A e. e ∈ set ebag ∧ A = core_incident e ⇒
                            ¬is_directed_edge e ∧
                            (FINITE A ⇒ 1 ≤ CARD A))
    | (SOME F, F) => (∀e. e ∈ set ebag ⇒ is_directed_edge e ∧ ¬gen_selfloop e)
    | (SOME F, T) => (∀e. e ∈ set ebag ⇒ is_directed_edge e)
    | (SOME T, F) => (∀e. e ∈ set ebag ⇒
                          ¬is_directed_edge e ∧
                          ∃m n. m ≠ n ∧ core_incident e = {m;n})
    | (SOME T, T) => (∀e. e ∈ set ebag ⇒
                          ¬is_directed_edge e ∧
                          ∃m n. core_incident e = {m;n})
End

val SL_OK_tydefrec = newtypeTools.rich_new_type
   {tyname = "SL_OK",
    exthm  = prove(“∃x:unit. (λx. T) x”, simp[]),
    ABS    = "SL_OK_ABS",
    REP    = "SL_OK_REP"};

val noSL_tydefrec = newtypeTools.rich_new_type
   {tyname = "noSL",
    exthm  = prove(“∃x:num. (λx. T) x”, simp[]),
    ABS    = "noSL_ABS",
    REP    = "noSL_REP"};

val INF_OK_tydefrec = newtypeTools.rich_new_type
   {tyname = "INF_OK",
    exthm  = prove(“∃x:num. (λx. T) x”, simp[]),
    ABS    = "INF_OK_ABS",
    REP    = "INF_OK_REP"};

val finiteG_tydefrec = newtypeTools.rich_new_type
   {tyname = "finiteG",
    exthm  = prove(“∃x:unit. (λx. T) x”, simp[]),
    ABS    = "finiteG_ABS",
    REP    = "finiteG_REP"};

val undirectedG_tydefrec = newtypeTools.rich_new_type
   {tyname = "undirectedG",
    exthm  = prove(“∃x:bool. (λx. T) x”, simp[]),
    ABS    = "undirectedG_ABS",
    REP    = "undirectedG_REP"};

val directedG_tydefrec = newtypeTools.rich_new_type
   {tyname = "directedG",
    exthm  = prove(“∃x:unit. (λx. T) x”, simp[]),
    ABS    = "directedG_ABS",
    REP    = "directedG_REP"};

val hyperG_tydefrec = newtypeTools.rich_new_type
   {tyname = "hyperG",
    exthm  = prove(“∃x:num. (λx. T) x”, simp[]),
    ABS    = "hyperG_ABS",
    REP    = "hyperG_REP"};

val allEdgesOK_tydefrec = newtypeTools.rich_new_type
   {tyname = "allEdgesOK",
    exthm  = prove(“∃x:num. (λx. T) x”, simp[]),
    ABS    = "allEdgesOK_ABS",
    REP    = "allEdgesOK_REP"};

val finiteEdges_tydefrec = newtypeTools.rich_new_type
   {tyname = "finiteEdges",
    exthm  = prove(“∃x:bool option. (λx. T) x”, simp[]),
    ABS    = "finiteEdges_ABS",
    REP    = "finiteEdges_REP"};

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

Theorem itself2boolopt_directedG[simp]:
  itself2boolopt (:directedG) = SOME F
Proof
  simp[itself2boolopt_def]
QED

Theorem itself2bool_noSL[simp]:
  itself2bool (:noSL) = F
Proof
  simp[itself2bool_def] >>
  simp[infinite_num_inj] >> qexists ‘noSL_ABS’ >>
  simp[INJ_IFF, #term_ABS_pseudo11 noSL_tydefrec]
QED

Theorem UNIV_undirectedG:
  univ(:undirectedG) = {undirectedG_ABS F; undirectedG_ABS T}
Proof
  simp[EXTENSION, SYM $ #term_REP_11 undirectedG_tydefrec,
       #repabs_pseudo_id undirectedG_tydefrec
      ]
QED

Theorem UNIV_finiteEdges[simp]:
  univ(:finiteEdges) = {finiteEdges_ABS (SOME F); finiteEdges_ABS (SOME T);
                        finiteEdges_ABS NONE}
Proof
  simp[EXTENSION, SYM $ #term_REP_11 finiteEdges_tydefrec,
       #repabs_pseudo_id finiteEdges_tydefrec
      ] >> qx_gen_tac ‘e’ >> Cases_on ‘finiteEdges_REP e’ >> simp[]
QED

Theorem itself2_t_finiteEdges[simp]:
  itself2_4 (:finiteEdges) = (T,F)
Proof
  simp[itself2_4_def, AllCaseEqs(), #term_ABS_pseudo11 finiteEdges_tydefrec]
QED

Theorem itself2boolopt_undirectedG[simp]:
  itself2boolopt (:undirectedG) = SOME T
Proof
  simp[itself2boolopt_def, AllCaseEqs(), UNIV_undirectedG,
       #term_ABS_pseudo11 undirectedG_tydefrec]
QED

Theorem INFINITE_UINF_OK[simp]:
  INFINITE univ(:INF_OK)
Proof
  simp[infinite_num_inj] >> qexists ‘INF_OK_ABS’ >>
  simp[INJ_IFF, #term_ABS_pseudo11 INF_OK_tydefrec]
QED

Theorem itself2_4_allEdgesOK[simp]:
  itself2_4 (:allEdgesOK) = (T,T)
Proof
  simp[itself2_4_def, AllCaseEqs(), infinite_num_inj] >>
  qexists ‘allEdgesOK_ABS’ >>
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

(* generic graphs
*)
Datatype:
  graphrep = <| nodes : ('a+num) set ;
                  (* useful to have countable space to expand into *)
                edges : ('a+num,'el) core_edge bag ;
                nlab : 'a+num -> 'nl ;
                nfincst : 'nf itself ;
                dircst : 'd itself ;  (* true implies directed graph *)
                slcst : 'slc itself ; (* true implies self-loops allowed *)
                edgecst : 'ec  itself
             |>
End

Definition wfgraph_def:
  wfgraph grep ⇔
    (∀e. e ∈ set grep.edges ⇒ core_incident e ⊆ grep.nodes) ∧
    finite_cst (itself2set grep.nfincst) grep.nodes ∧
    edge_cst grep.edgecst grep.dircst grep.slcst grep.edges ∧
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
Theorem optelim[local] = prove_case_elim_thm {
  nchotomy = TypeBase.nchotomy_of ``:'a option``,
  case_def = TypeBase.case_def_of ``:'a option``};

Theorem edge_cst_EMPTY[simp]:
  edge_cst x y z EMPTY_BAG
Proof
  rw[edge_cst_def, finite_edges_per_nodeset_def, only_one_edge_per_label_def,
     only_one_edge_def]
  >- (rename [‘itself2_4 X’] >> Cases_on ‘itself2_4 X’ >> simp[])
  >- (rename [‘itself2boolopt X’] >> Cases_on ‘itself2boolopt X’ >> simp[])
QED

Theorem finite_edges_per_nodeset_BAG_INSERT[simp]:
  finite_edges_per_nodeset (BAG_INSERT e es) ⇔ finite_edges_per_nodeset es
Proof
  dsimp[finite_edges_per_nodeset_def, GSPEC_OR] >> simp[GSPEC_AND]
QED

Theorem only_one_edge_per_label_BAG_INSERT:
  only_one_edge_per_label (BAG_INSERT e es) ⇒ only_one_edge_per_label es
Proof
  simp[only_one_edge_per_label_def, BAG_INSERT, AllCaseEqs(), DISJ_IMP_THM,
       FORALL_AND_THM, SF CONJ_ss, BAG_IN, BAG_INN] >> rpt strip_tac >>
  first_x_assum $ drule_then strip_assume_tac >> gvs[]
QED

Theorem only_one_edge_BAG_INSERT:
  only_one_edge (BAG_INSERT e es) ⇒ only_one_edge es
Proof
  REWRITE_TAC[only_one_edge_def, SET_OF_BAG_INSERT] >>
  REWRITE_TAC[BAG_INSERT, IN_INSERT, RIGHT_AND_OVER_OR] >> BETA_TAC >>
  rpt strip_tac >>
  metis_tac[DECIDE “x + 1 = 1 ⇔ x = 0”, IN_SET_OF_BAG_NONZERO]
QED

Theorem edge_cst_DELETE:
  edge_cst x y z es0 ∧ BAG_DELETE es0 e es ⇒ edge_cst x y z es
Proof
  simp[edge_cst_def, BAG_DELETE] >> rw[] >> gvs[] >>
  rename [‘itself2_4 ecst’] >> Cases_on ‘itself2_4 ecst’ >>
  rename [‘itself2_4 ecst = (b1,b2)’] >> map_every Cases_on [‘b1’, ‘b2’] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >>~-
  ([‘only_one_edge_per_label (BAG_INSERT e es)’, ‘only_one_edge_per_label es’],
   drule only_one_edge_per_label_BAG_INSERT >> simp[]) >>~-
  ([‘only_one_edge (BAG_INSERT e es)’, ‘only_one_edge es’],
   drule only_one_edge_BAG_INSERT >> simp[]) >>
  rename [‘itself2boolopt uhd’] >> Cases_on ‘itself2boolopt uhd’ >> gvs[] >>
  metis_tac[]
QED

Theorem graphs_exist[local]:
  ∃g. wfgraph g
Proof
  qexists ‘<| nodes := {};
              edges := EMPTY_BAG;
              nlab := K ARB;
              nfincst := ARB;
              dircst := ARB;
              slcst := ARB;
              edgecst := ARB; |>’ >>
  simp[wfgraph_def, finite_cst_def, itself2set_def]
QED

val tydefrec = newtypeTools.rich_new_type
   {tyname = "graph",
    exthm  = graphs_exist,
    ABS    = "graph_ABS",
    REP    = "graph_REP"};

(* any undirected graph *)
Type udgraph[pp] = “:('a,undirectedG,'ec,'el,'nf,'nl,'sl)graph”

(* finite directed graph with labels on nodes and edges, possibility of
   multiple, but finitely many edges, and with self-loops allowed *)
Type fdirgraph[pp] = “:('NodeEnum,
                        directedG,
                        finiteEdges (* finitely many edges between nodes *),
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
Type ulabgraphrep[local] = “:(α,δ,unit,unit,ν,unit,σ) graphrep”

(* undirected version of the same *)
Type udulgraph[pp] = “:(α, undirectedG, ν, σ)ulabgraph”
Type udulgraphrep[local] = “:(α,undirectedG,ν,σ)ulabgraphrep”

(* a relation graph; stripped such are in bijection with binary relations.
   (The stripping makes a canonical, minimal choice of node set in the graph.)
 *)
Type relgraph[pp] = “:(α, directedG, INF_OK, SL_OK) ulabgraph”


Definition emptyG0_def:
    emptyG0 : (α,δ,'ec,'el,ν,'nl,σ) graphrep =
     <| nodes := {} ; edges := {||}; nlab := K ARB;
        nfincst := (:ν); dircst := (:δ); slcst := (:σ);
        edgecst := (:'ec) |>
End


Definition nodes_def:
  nodes G = (graph_REP G).nodes
End

Definition edgebag_def:
  edgebag G = (graph_REP G).edges
End

Definition edges_def:
  edges (G:(α,directedG,'ec,'el,ν,'nl,σ) graph) =
  {de | cDE de ∈ set $ edgebag G}
End

Definition udedges_def:
  udedges (G:(α,'ec,'el,'nf,'nl,'sl) udgraph) = {he | cHE he ∈ set (edgebag G)}
End

Theorem incident_SUBSET_nodes:
  e ∈ edges g ∧ n ∈ incident e ⇒ n ∈ nodes g
Proof
  rw[edges_def, nodes_def, edgebag_def] >>
  ‘wfgraph (graph_REP g)’ by simp[#termP_term_REP tydefrec] >>
  gs[wfgraph_def, SUBSET_DEF] >> first_x_assum irule >>
  first_assum $ irule_at Any >> simp[]
QED

Theorem incident_udedges_SUBSET_nodes:
  e ∈ udedges g ∧ n ∈ incident e ⇒ n ∈ nodes g
Proof
  rw[udedges_def, nodes_def, edgebag_def] >>
  ‘wfgraph (graph_REP g)’ by simp[#termP_term_REP tydefrec] >>
  gvs[wfgraph_def, SUBSET_DEF, ITSELF_UNIQUE] >>
  first_x_assum irule >> first_assum $ irule_at Any >> simp[]
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

Theorem edgebag_empty[simp]:
  edgebag emptyG = {||}
Proof
  simp[edgebag_def, emptyG_def, #repabs_pseudo_id tydefrec] >>
  simp[emptyG0_def]
QED

Theorem edges_empty[simp]:
  edges emptyG = ∅
Proof
  simp[edges_def]
QED

Theorem udedges_empty[simp]:
  udedges emptyG = ∅
Proof
  simp[udedges_def]
QED

Theorem nlabelfun_empty[simp]:
  nlabelfun emptyG = (λn. ARB)
Proof
  simp[nlabelfun_def, emptyG_def, #repabs_pseudo_id tydefrec] >>
  simp[emptyG0_def, FUN_EQ_THM]
QED

Definition adjacent_def:
  adjacent G m n ⇔
    ∃e. e ∈ set (edgebag G) ∧
        (enodes e = INL (m,n) ∨ enodes e = INR {m;n})
End

Theorem edge_cst_directedG:
  edge_cst ecst (:directedG) slcst ebag ⇒
  ∀e. e ∈ set ebag ⇒ is_directed_edge e
Proof
  gvs[edge_cst_def] >> metis_tac[]
QED

Theorem edge_cst_undirectedG:
  edge_cst ecst (:undirectedG) slcst ebag ⇒
  ∀e. e ∈ set ebag ⇒ ¬is_directed_edge e ∧
                     ∃m n. core_incident e = {m;n}
Proof
  gvs[edge_cst_def] >> metis_tac[]
QED

Theorem adjacent_directed:
  adjacent (G : (α,directedG,'ec,'el,'nf,'nl,'sl)graph) m n ⇔
    ∃l. directed m n l ∈ edges G
Proof
  simp[adjacent_def] >>
  ‘wfgraph (graph_REP G)’ by simp[#termP_term_REP tydefrec] >>
  gvs[wfgraph_def, ITSELF_UNIQUE, edgebag_def, edges_def] >>
  drule_then strip_assume_tac edge_cst_directedG >> iff_tac >> rw[] >>
  gvs[IN_SET_OF_BAG, enodesEQ, SF SFY_ss]
  >- (first_x_assum drule >> simp[]) >>
  first_assum $ irule_at Any >> simp[]
QED

Theorem adjacent_undirected:
  adjacent (G : ('a,'ec,'el,'nf,'nl,'sl)udgraph) m n ⇔
    ∃l. hyper {m;n} l ∈ udedges G
Proof
  simp[adjacent_def] >>
  ‘wfgraph (graph_REP G)’ by simp[#termP_term_REP tydefrec] >>
  gvs[wfgraph_def, ITSELF_UNIQUE, edgebag_def, udedges_def] >>
  drule_then strip_assume_tac edge_cst_undirectedG >> iff_tac >> rw[] >>
  gvs[IN_SET_OF_BAG, enodesEQ, SF SFY_ss]
  >- (first_x_assum drule >> simp[]) >>
  first_assum $ irule_at Any >> simp[]
QED

Theorem adjacent_SYM:
  adjacent (G:('a,undirectedG,'ec,'el,'nf,'nl,'sl)graph) m n ⇔ adjacent G n m
Proof
  simp[adjacent_undirected] >> metis_tac[INSERT_COMM]
QED

Theorem adjacent_empty[simp]:
  adjacent emptyG m n ⇔ F
Proof
  simp[adjacent_def, emptyG_def, edgebag_def, #repabs_pseudo_id tydefrec] >>
  simp[emptyG0_def]
QED

Theorem edges_irrefl[simp]:
  directed a a l ∉ edges (G:('a,directedG,'ec,'el,'nf,'nl,noSL)graph)
Proof
  simp[edges_def, edgebag_def] >>
  ‘wfgraph (graph_REP G)’ by simp[#termP_term_REP tydefrec] >>
  gs[wfgraph_def, ITSELF_UNIQUE, FORALL_PROD, edge_cst_def] >>
  strip_tac >> first_x_assum drule >> simp[]
QED

Theorem adjacent_irrefl[simp]:
  adjacent (G:('a,'dir,'ec,'el,'nf,'nl,noSL)graph) a a = F
Proof
  simp[adjacent_def] >>
  ‘wfgraph (graph_REP G)’ by simp[#termP_term_REP tydefrec] >>
  gs[wfgraph_def, ITSELF_UNIQUE, FORALL_PROD, edge_cst_def, edgebag_def] >>
  rpt strip_tac >>
  Cases_on ‘itself2boolopt(:'dir)’ >> gvs[]
  >- (Cases_on ‘BAG_IN e (graph_REP G).edges’ >> simp[] >>
      first_x_assum drule >> Cases_on ‘e’>> simp[] >> rpt strip_tac >> gvs[]) >>
  Cases_on ‘BAG_IN e (graph_REP G).edges’ >> simp[] >>
  rename [‘SOME b = itself2boolopt _’] >>
  Cases_on ‘b’ >> gvs[] >> first_x_assum drule >> simp[] >>
  rename [‘enodes e’] >>
  Cases_on ‘e’ >> gvs[PULL_EXISTS] >> rw[] >> simp[]
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

Theorem edgebag_addNode[simp]:
  edgebag (addNode n l G) = edgebag G
Proof
  simp[edgebag_def, addNode_def, #repabs_pseudo_id tydefrec,
       #termP_term_REP tydefrec, wfgraph_addNode0] >>
  simp[addNode0_def]
QED

Theorem edges_addNode[simp]:
  edges (addNode n l G) = edges G
Proof
  simp[edges_def]
QED

Theorem udedges_addNode[simp]:
  udedges (addNode n l G) = udedges G
Proof
  simp[udedges_def]
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

Definition udfilter_insertedge_def:
  udfilter_insertedge ns lab ecst ebag =
  let e = HE ns lab
  in
    case itself2_4 ecst of
    | (F,F) => BAG_INSERT e $ BAG_FILTER (λe. core_incident e ≠ ns) ebag
    | (F,T) => if BAG_IN e ebag then ebag else BAG_INSERT e ebag
    | (T,F) => BAG_INSERT e ebag
    | (T,T) => BAG_INSERT e ebag
End

Theorem BAG_IN_udfilter_insertedge:
  BAG_IN e (udfilter_insertedge ns lab ecst ebag) ⇒
  core_incident e = ns ∧ ¬is_directed_edge e ∨ BAG_IN e ebag
Proof
  simp[udfilter_insertedge_def] >> Cases_on ‘itself2_4 ecst’ >>
  rename [‘itself2_4 ecst = (b1,b2)’] >>
  map_every Cases_on [‘b1’, ‘b2’] >> gvs[DISJ_IMP_THM] >> rw[] >> simp[]
QED

Theorem finite_edges_per_nodeset_udfilter_insertedge[local]:
  itself2_4(:'ec) = (T,F) ∧ finite_edges_per_nodeset ebag ⇒
  finite_edges_per_nodeset (udfilter_insertedge ns lab (:'ec) ebag)
Proof
  dsimp[finite_edges_per_nodeset_def, udfilter_insertedge_def, GSPEC_OR] >>
  simp[GSPEC_AND]
QED

Theorem only_one_edge_per_label_udfilter_insertedge[local]:
  itself2_4(:'ec) = (F,T) ∧ only_one_edge_per_label ebag ⇒
  only_one_edge_per_label (udfilter_insertedge ns lab (:'ec) ebag)
Proof
  dsimp[only_one_edge_per_label_def, udfilter_insertedge_def, GSPEC_OR] >>
  rw[BAG_IN, BAG_INN, BAG_INSERT] >>
  gvs[DECIDE “¬(x >= 1) ⇔ x = 0”] >> rw[] >> gvs[]
QED

Theorem only_one_edge_udfilter_insertedge[local]:
  itself2_4 (:'ec) = (F,F) ∧ only_one_edge ebag ⇒
  only_one_edge (udfilter_insertedge ns lab (:'ec) ebag)
Proof
  simp[only_one_edge_def, udfilter_insertedge_def] >> rw[] >> gvs[] >>
  simp[BAG_FILTER_DEF, BAG_INSERT, AllCaseEqs()] >>
  rename [‘enodes e’] >> Cases_on ‘e’ >> gvs[]
QED

Definition addUDEdge0_def:
  addUDEdge0 m n lab (G:('a,undirectedG,'ec,'el,'nf,'nl,'sl)graphrep) =
  if m = n ∧ ¬itself2bool(:'sl) then G
  else
    G with <| nodes := {m;n} ∪ G.nodes ;
              edges := udfilter_insertedge {m;n} lab (:'ec) G.edges
           |>
End

Definition addUDEdge_def:
  addUDEdge m n lab G = graph_ABS (addUDEdge0 m n lab (graph_REP G))
End

Theorem wfgraph_addUDEdge0[simp,local]:
  wfgraph G0 ⇒
  wfgraph (addUDEdge0 m n lab
                      (G0:('a,undirectedG,'ec,'el,'nf,'nl, 'sl)graphrep))
Proof
  simp[addUDEdge0_def, wfgraph_def, ITSELF_UNIQUE] >>
  Cases_on ‘m = n’ >> simp[] >>
  Cases_on ‘itself2bool (:'sl)’ >> simp[] >>
  (rw[finite_cst_UNION]
   >- (drule_then strip_assume_tac BAG_IN_udfilter_insertedge >> simp[] >>
       first_x_assum drule >> simp[SUBSET_DEF]) >>
   qpat_x_assum ‘edge_cst _ _ _ _’ mp_tac >>
   simp[edge_cst_def] >>
   Cases_on ‘itself2_4 (:'ec)’ >>
   rename [‘itself2_4 _ = (b1,b2)’] >>
   map_every Cases_on [‘b1’, ‘b2’] >> gvs[] >>
   simp[finite_edges_per_nodeset_udfilter_insertedge,
        only_one_edge_per_label_udfilter_insertedge,
        only_one_edge_udfilter_insertedge] >>
   strip_tac >> gen_tac >> strip_tac >>
   drule_then strip_assume_tac BAG_IN_udfilter_insertedge >>
   metis_tac[INSERT_INSERT])
QED

Definition edge0_def:
  edge0 m n lab ecst edges =
  let e = DE m n lab
  in
    case itself2_4 ecst of
      (F,F) => BAG_INSERT e $ BAG_FILTER (λe. enodes e ≠ INL (m,n)) edges
    | (F,T) => if BAG_IN e edges then edges else BAG_INSERT e edges
    | (T,F) => BAG_INSERT e edges
    | (T,T) => BAG_INSERT e edges
End

Definition addEdge0_def:
  addEdge0 m n (lab:'el) (G : ('ne,directedG,'ec,'el,'nf,'nl,'sl) graphrep) =
  if m = n ∧ ¬itself2bool (:'sl) then G
  else
    G with <|
        nodes := G.nodes ∪ {m;n} ;
        edges := edge0 m n lab (:'ec) G.edges
    |>
End

Definition addEdge_def:
  addEdge m n l G = graph_ABS (addEdge0 m n l (graph_REP G))
End

Theorem IN_edge0:
  BAG_IN e (edge0 m n lab ecset ebag) ⇒ e = DE m n lab ∨ BAG_IN e ebag
Proof
  rw[edge0_def] >>
  Cases_on ‘itself2_4 ecset’ >> gvs[] >>
  rename [‘itself2_4 _ = (b1,b2)’] >>
  map_every Cases_on [‘b1’, ‘b2’] >> gvs[]
QED

Theorem edge0_preserves_edge_cst:
  (m ≠ n ∨ itself2bool slp) ∧ edge_cst ecset (:directedG) slp edgeset ⇒
  edge_cst ecset (:directedG) slp (edge0 m n lab ecset edgeset)
Proof
  rw[edge_cst_def, edge0_def] >> gvs[] >>
  Cases_on ‘itself2_4 ecset’ >> gvs[] >>
  rename [‘itself2_4 _ = (b1,b2)’] >>
  map_every Cases_on [‘b1’, ‘b2’] >> gvs[] >>~-
  ([‘only_one_edge (BAG_INSERT _ _)’, ‘¬(BAG_IN (DE _ _ _) ebag)’],
   qpat_x_assum ‘only_one_edge _’ mp_tac >>
   simp[only_one_edge_def] >>
   simp[BAG_INSERT, BAG_FILTER_DEF, AllCaseEqs(), BAG_IN, BAG_INN] >>
   rw[] >> gvs[BAG_IN, BAG_INN]) >>~-
  ([‘only_one_edge (BAG_INSERT _ _)’],
   qpat_x_assum ‘only_one_edge _’ mp_tac >>
   simp[only_one_edge_def] >>
   simp[BAG_INSERT, BAG_FILTER_DEF, AllCaseEqs(), BAG_IN, BAG_INN] >>
   rw[] >> gvs[BAG_IN, BAG_INN]) >>
  qpat_x_assum ‘only_one_edge_per_label _’ mp_tac >>
  simp[only_one_edge_per_label_def, BAG_INSERT, BAG_IN, BAG_INN,
       DISJ_IMP_THM, AllCaseEqs(), FORALL_AND_THM] >>
  gvs[BAG_IN, BAG_INN]
QED

Theorem wfgraph_addEdge0[local]:
  wfgraph G0 ⇒
  wfgraph (addEdge0 m n lab (G0:('a,directedG,'ec,'el,'nf,'nl,'sl) graphrep))
Proof
  simp[addEdge0_def, ITSELF_UNIQUE, finite_cst_UNION] >>
  Cases_on ‘m = n’ >> gvs[] >>
  Cases_on ‘itself2bool (:'sl)’ >> gvs[] >>
  simp[wfgraph_def, finite_cst_UNION] >> rpt strip_tac >>~-
  ([‘core_incident _ ⊆ _ ∪ _’],
   drule IN_edge0 >> simp[DISJ_IMP_THM] >> ASM_SET_TAC[]) >>
  gvs[ITSELF_UNIQUE] >>
  irule edge0_preserves_edge_cst >> simp[]
QED

Definition selfloops_ok_def[simp]:
  selfloops_ok (G : (α,'d,'ec,'el,'nf,'nl,'sl) graph) = itself2bool (:'sl)
End

Theorem selfloop_edges_E:
  directed m m l ∈ edges G ⇒ selfloops_ok G
Proof
  simp[selfloops_ok_def] >> strip_tac >>
  ‘wfgraph (graph_REP G)’ by simp[#termP_term_REP tydefrec] >>
  gvs[wfgraph_def, ITSELF_UNIQUE, edge_cst_def, COND_EXPAND_OR] >>
  gvs[edges_def, edgebag_def] >> first_x_assum drule >> simp[]
QED

Definition oneEdge_max_def:
  oneEdge_max (G: (α,'d,'ec,'el,'nf,'nl,'sl) graph) ⇔
  itself2_4 (:'ec) = (F,F)
End

Theorem oneEdge_max_graph[simp]:
  oneEdge_max (g : ('a,'d,unit,'el,'nf,'nl,'sl) graph)
Proof
  simp[oneEdge_max_def, itself2set_def, itself2_4_def]
QED

Definition oneEdge_perlabel_def:
  oneEdge_perlabel (G: (α,'d,'ec,'el,'nf,'nl,'sl) graph) ⇔
    itself2_4 (:'ec) = (F,T)
End

Theorem oneEdge_max_fdirgraph[simp]:
  ¬oneEdge_max (g : (α,β,γ)fdirgraph)
Proof
  simp[oneEdge_max_def, itself2set_def]
QED

Theorem selfloops_ok_graph[simp]:
  selfloops_ok (g1 : ('a,'d,'ec,'el,'nf,'nl,unit) graph) ∧
  selfloops_ok (g2 : ('a,'d,'ec,'el,'nf,'nl,SL_OK) graph)
Proof
  simp[selfloops_ok_def]
QED

Theorem wrong_edgetype[simp]:
  ¬(BAG_IN (DE a b l)
           (edgebag (G:('a,undirectedG,'ec, 'el, 'nf, 'nl, 'sl) graph))) ∧
  ¬(BAG_IN (HE hs l)
           (edgebag (H:('a,directedG,'ec, 'el, 'nf, 'nl, 'sl) graph)))
Proof
  simp[edgebag_def] >> rpt strip_tac
  >- (‘wfgraph (graph_REP G)’
        by simp[#termP_term_REP tydefrec] >>
      gvs[wfgraph_def, edge_cst_def, optelim, COND_EXPAND_OR, ITSELF_UNIQUE] >>
      first_x_assum drule >> simp[])
  >- (‘wfgraph (graph_REP H)’
        by simp[#termP_term_REP tydefrec] >>
      gvs[wfgraph_def, edge_cst_def, optelim, COND_EXPAND_OR, ITSELF_UNIQUE] >>
      first_x_assum drule >> simp[])
QED

Theorem edges_addEdge:
  edges (addEdge m n lab (G:('a,directedG,'ecst,'el,'nf,'nl,'sl)graph)) =
  (edges G DIFF
         (if adjacent G m n ∧ oneEdge_max G then
              { directed m n l | l | directed m n l ∈ edges G }
          else {})) ∪
  (if m ≠ n ∨ selfloops_ok G then {directed m n lab} else {})
Proof
  simp[edges_def, edgebag_def, addEdge_def, wfgraph_addEdge0,
       #termP_term_REP tydefrec, #repabs_pseudo_id tydefrec] >>
  simp[addEdge0_def, edge0_def, ITSELF_UNIQUE] >> rw[] >>
  gvs[oneEdge_max_def] >~
  [‘adjacent G m m’]
  >- (‘wfgraph (graph_REP G)’ by simp[#termP_term_REP tydefrec] >>
      gvs[wfgraph_def, adjacent_def, ITSELF_UNIQUE, edge_cst_def, enodesEQ,
          edgebag_def] >>
      first_x_assum drule >> simp[]) >>
  simp[EXTENSION] >> Cases >> simp[]
  >- metis_tac[]
  >- (Cases_on ‘itself2_4 (:'ecst)’ >> simp[] >> rw[]
      >- metis_tac[]
      >- metis_tac[] >>
      iff_tac >> rw[] >> simp[] >> rw[] >>
      ‘wfgraph (graph_REP G)’ by simp[#termP_term_REP tydefrec] >>
      gvs[wfgraph_def, edge_cst_def, ITSELF_UNIQUE, COND_EXPAND_OR,
          only_one_edge_def] >>
      first_x_assum (dxrule_then drule o cj 2) >> simp[])
  >- metis_tac[] >>
  Cases_on ‘itself2_4 (:'ecst)’ >> simp[] >> rw[]
  >- metis_tac[]
  >- metis_tac[] >>
  iff_tac >> rw[] >> rw[] >>
  gvs[adjacent_directed, edges_def, edgebag_def]
QED

Theorem directed_oneEdge_max:
  oneEdge_max (G : ('a,directedG,'ecst,'el,'nf, 'nl, 'sl) graph) ∧
  directed a b l1 ∈ edges G ∧ directed a b l2 ∈ edges G ⇒ l1 = l2
Proof
  simp[oneEdge_max_def, edges_def, edgebag_def] >>
  ‘wfgraph (graph_REP G)’ by simp[#termP_term_REP tydefrec] >>
  strip_tac >>
  gvs[wfgraph_def, edge_cst_def, ITSELF_UNIQUE, only_one_edge_def] >>
  first_x_assum (dxrule_then drule o cj 2)>> simp[]
QED

Theorem adjacent_addEdge[simp]:
  adjacent (addEdge m n lab G) a b ⇔
    (m ≠ n ∨ selfloops_ok G) ∧ m = a ∧ n = b ∨ adjacent G a b
Proof
  simp[adjacent_directed, edges_addEdge] >> rw[EQ_IMP_THM] >> gvs[] >>
  TRY (drule_then assume_tac selfloop_edges_E) >> gvs[] >>
  metis_tac[directed_oneEdge_max]
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
  nodes (addUDEdge m n lab G) =
  (if m ≠ n ∨ selfloops_ok G then {m; n} else ∅) ∪ nodes G
Proof
  simp[addUDEdge_def, nodes_def, #repabs_pseudo_id tydefrec,
       #termP_term_REP tydefrec, wfgraph_addUDEdge0] >>
  simp[addUDEdge0_def] >> rw[] >> gvs[]
QED

Theorem udedges_addUDEdge:
  udedges (addUDEdge m n lab (G:('a,undirectedG,'ecst,'el,'nf,'nl,'sl) graph)) =
  if m ≠ n ∨ selfloops_ok G then
    if oneEdge_max G then
      {hyper {m;n} lab} ∪ { ude | ude ∈ udedges G ∧ henodes ude ≠ {m;n} }
    else
      {hyper {m;n} lab} ∪ udedges G
  else udedges G
Proof
  simp[addUDEdge_def, udedges_def, #repabs_pseudo_id tydefrec,
       #termP_term_REP tydefrec, wfgraph_addUDEdge0, edgebag_def] >>
  simp[addUDEdge0_def] >> Cases_on ‘selfloops_ok G’ >>
  Cases_on ‘m = n’ >> gvs[oneEdge_max_def] >> rw[] >>
  Cases_on ‘itself2_4(:'ecst)’ >> gvs[COND_EXPAND_OR] >>
  TRY (qpat_x_assum ‘_ = itself2_4 _’ (assume_tac o SYM)) >>
  simp[udfilter_insertedge_def, GSPEC_OR] >> rw[GSPEC_OR] >>
  simp[Once EXTENSION] >> metis_tac[]
QED

Theorem adjacent_addUDEdge[simp]:
  adjacent (addUDEdge m n lab G) a b ⇔
    (m ≠ n ∨ selfloops_ok G) ∧ {a;b} = {m;n} ∨ adjacent G a b
Proof
  simp[adjacent_undirected, udedges_addUDEdge] >> rw[] >>
  dsimp[INSERT2_lemma] >> metis_tac[]
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
  rw[addEdge0_def]
QED

(* adding undirected self-edge from n to n in a no-selfloop graph is an
   identity operation *)
Theorem addUDEdge_addNode[simp]:
  addUDEdge n n lab (G:(α,undirectedG,'ec,'el,'nf,'nl,noSL) graph) = G
Proof
  simp[addUDEdge_def, GSYM (#term_REP_11 tydefrec), #repabs_pseudo_id tydefrec,
       wfgraph_addUDEdge0, #termP_term_REP tydefrec] >>
  rw[addUDEdge0_def]
QED

(* "similarly" for addEdge: *)
Theorem addEdge_addNode[simp]:
  addEdge n n lab (G : (α,directedG,'ec,'el,'nf,'nl,noSL)graph) = G
Proof
  simp[SYM $ #term_REP_11 tydefrec] >>
  simp[addEdge_def, #term_ABS_pseudo11 tydefrec, #repabs_pseudo_id tydefrec,
       wfgraph_addEdge0, #termP_term_REP tydefrec] >>
  simp[addEdge0_def]
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
  g1 = g2 ⇔ nodes g1 = nodes g2 ∧ edgebag g1 = edgebag g2 ∧
            nlabelfun g1 = nlabelfun g2
Proof
  simp[EQ_IMP_THM] >>
  simp[nodes_def, edgebag_def, SYM $ #term_REP_11 tydefrec,
       nlabelfun_def] >>
  simp[theorem "graphrep_component_equality", ITSELF_UNIQUE]
QED

Theorem oneEdge_max_BAG_INN_edgebag[simp]:
  oneEdge_max g ⇒
  (BAG_INN e c (edgebag g) ⇔ c = 0 ∨ BAG_IN e (edgebag g) ∧ c = 1)
Proof
  simp[EQ_IMP_THM, DISJ_IMP_THM, edgebag_def, oneEdge_max_def] >> strip_tac >>
  ‘wfgraph (graph_REP g)’ by simp[#termP_term_REP tydefrec] >>
  gvs[ITSELF_UNIQUE, wfgraph_def, edge_cst_def, COND_EXPAND_OR,
      only_one_edge_def, BAG_INN, BAG_IN] >>
  Cases_on ‘c = 0’ >> gvs[] >> strip_tac >>
  rename [‘(graph_REP g).edges e ≥ c’] >>
  ‘(graph_REP g).edges e ≥ 1’ by simp[] >>
  ‘(graph_REP g).edges e = 1’ by simp[] >> simp[]
QED

Theorem udul_component_equality:
  (g1:(α,ν,σ) udulgraph) = g2 ⇔
    nodes g1 = nodes g2 ∧ udedges g1 = udedges g2
Proof
  simp[gengraph_component_equality, EQ_IMP_THM] >> rpt strip_tac
  >- simp[udedges_def]
  >- (gs[udedges_def] >>
      qpat_x_assum ‘GSPEC _ = GSPEC _’ mp_tac >>
      simp[SimpLHS, Once EXTENSION] >> simp[BAG_EXTENSION] >> rpt strip_tac >>
      rename [‘BAG_IN e _’] >> Cases_on ‘e’ >> simp[]) >>
  simp[FUN_EQ_THM]
QED

Theorem diffedge_types_impossible:
  BAG_IN (DE m n l1) (edgebag (g1:('a1,'d,'ec1,'el1,'nf1,'nl1,'sl1) graph)) ⇒
  BAG_IN (HE ns l2) (edgebag (g2:('a2,'d,'ec2,'el2,'nf2,'nl2,'sl2) graph)) ⇒
  F
Proof
  simp[edgebag_def] >>
  ‘wfgraph (graph_REP g1) ∧ wfgraph (graph_REP g2)’
    by simp[#termP_term_REP tydefrec] >>
  gvs[wfgraph_def, edge_cst_def, ITSELF_UNIQUE, optelim, COND_EXPAND_OR] >>
  rpt strip_tac >> res_tac >> gvs[] >>
  rpt (qpat_x_assum ‘_ = itself2boolopt _’ (assume_tac o SYM)) >> gvs[]
QED

Definition is_hypergraph_def:
  is_hypergraph (g:(α,'d,'ecst,'el,'nf,'nl,'sl) graph) ⇔
  itself2boolopt(:'d) = NONE
End

Theorem nonhypergraph_edges:
  ¬is_hypergraph g ∧ BAG_IN e (edgebag g) ⇒
  (∃m n l. e = HE {m;n} l) ∨ ∃m n l. e = DE m n l
Proof
  simp[is_hypergraph_def, edgebag_def] >> strip_tac >>
  ‘wfgraph (graph_REP g)’ by simp[#termP_term_REP tydefrec] >>
  gvs[wfgraph_def, edge_cst_def, optelim, COND_EXPAND_OR, ITSELF_UNIQUE] >>
  first_x_assum drule >> Cases_on ‘e’ >> simp[PULL_EXISTS] >>
  rpt strip_tac >> irule_at Any EQ_REFL
QED

Theorem ulabgraph_component_equality:
  ¬is_hypergraph g1 ⇒
  (g1 : (α,δ,ν,σ) ulabgraph = g2 ⇔
    nodes g1 = nodes g2 ∧ ∀a b. adjacent g1 a b = adjacent g2 a b)
Proof
  simp[Once EQ_IMP_THM, gengraph_component_equality] >> rw[]
  >- simp[adjacent_def]
  >- (simp[BAG_EXTENSION, oneEdge_max_BAG_INN_edgebag] >>
      gvs[adjacent_def, IN_SET_OF_BAG, enodesEQ, SF DNF_ss] >>
      rpt strip_tac >> Cases_on ‘e’ >> simp[] >>
      Cases_on ‘n = 0’ >> simp[] >> Cases_on ‘n = 1’ >> simp[] >>
      gvs[EQ_IMP_THM, DISJ_IMP_THM, FORALL_AND_THM] >>
      rpt strip_tac >> ‘¬is_hypergraph g2’ by gvs[is_hypergraph_def] >>
      drule_all_then strip_assume_tac nonhypergraph_edges >>
      gvs[] >>
      first_x_assum drule >> simp[DISJ_IMP_THM] >>
      drule_at_then Any (simp o single) diffedge_types_impossible) >>
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
       #repabs_pseudo_id tydefrec, wfgraph_nrelabel0, edgebag_def] >>
  rw[nrelabel0_def]
QED

Theorem edges_nrelabel[simp]:
  edges (nrelabel n l G) = edges G
Proof
  simp[edges_def, nrelabel_def, #termP_term_REP tydefrec, wfgraph_nrelabel0,
       #repabs_pseudo_id tydefrec, edgebag_def] >>
  simp[nrelabel0_def] >> rw[]
QED

Theorem udedges_nrelabel[simp]:
  udedges (nrelabel n l G) = udedges G
Proof
  simp[udedges_def, nrelabel_def, #termP_term_REP tydefrec, wfgraph_nrelabel0,
       #repabs_pseudo_id tydefrec, edgebag_def] >>
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

Theorem core_incident_NOT_EMPTY[simp]:
  BAG_IN e (edgebag g) ⇒ core_incident e ≠ {}
Proof
  rw[edgebag_def] >> ‘wfgraph (graph_REP g)’ by simp[#termP_term_REP tydefrec]>>
  gvs[wfgraph_def, edge_cst_def, optelim, COND_EXPAND_OR, ITSELF_UNIQUE]>>
  first_x_assum drule >> rpt strip_tac >> gvs[] >>
  Cases_on ‘e’ >> gvs[]
QED

Theorem core_incident_SUBSET_nodes:
  BAG_IN e (edgebag g) ⇒ core_incident e ⊆ nodes g
Proof
  rw[edgebag_def, nodes_def] >>
  ‘wfgraph (graph_REP g)’ by simp[#termP_term_REP tydefrec]>>
  gvs[wfgraph_def]
QED

Theorem nodes_EQ_EMPTY[simp]:
  nodes G = ∅ ⇔ G = emptyG
Proof
  simp[EQ_IMP_THM] >> simp[gengraph_component_equality, nlabelfun_EQ_ARB] >>
  reverse $ rpt strip_tac
  >- simp[FUN_EQ_THM, nlabelfun_EQ_ARB] >>
  qspec_then ‘edgebag G’ strip_assume_tac BAG_cases >> simp[] >>
  rename [‘BAG_INSERT e _’] >>
  ‘BAG_IN e (edgebag G)’ by simp[] >>
  map_every drule [core_incident_NOT_EMPTY, core_incident_SUBSET_nodes] >>
  simp[]
QED

Theorem adjacent_members:
  adjacent G m n ⇒ m ∈ nodes G ∧ n ∈ nodes G
Proof
  simp[adjacent_def, IN_SET_OF_BAG] >> strip_tac >>
  drule core_incident_SUBSET_nodes >> gvs[core_incident_def, enodesEQ]
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
  univR_graph0 (R:'a -> 'a -> bool) = <|
    nodes := { INL (a:'a) | T };
    edges := BAG_OF_SET {DE (INL m) (INL n) () | R m n};
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
  simp[itself2_4_def, BAG_IN, BAG_INN] >>
  simp[only_one_edge_def, PULL_EXISTS, BAG_OF_SET]
QED

Definition restrR_graph0_def:
  restrR_graph0 R = <|
                     nodes := { INL a | ∃b. R a b ∨ R b a };
                     edges := BAG_OF_SET {DE (INL a) (INL b) () | R a b};
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
       GSPEC_lemma, itself2_4_def] >>
  conj_tac >- metis_tac[] >>
  simp[only_one_edge_def, PULL_EXISTS] >>
  simp[BAG_OF_SET]
QED

Theorem nodes_univR_graph[simp]:
  nodes (univR_graph R) = IMAGE INL UNIV
Proof
  simp[univR_graph_def, nodes_def, #repabs_pseudo_id tydefrec,
       wfgraph_univR_graph0] >>
  simp[univR_graph0_def, EXTENSION]
QED

Theorem edges_univR_graph[simp]:
  edges (univR_graph R) = { directed (INL x) (INL y) () | R x y }
Proof
  simp[univR_graph_def, edges_def, #repabs_pseudo_id tydefrec,
       wfgraph_univR_graph0, edgebag_def] >>
  simp[univR_graph0_def, Once EXTENSION]
QED

Theorem adjacent_univR_graph[simp]:
  adjacent (univR_graph R) a b = ∃a0 b0. a = INL a0 ∧ b = INL b0 ∧ R a0 b0
Proof
  simp[adjacent_directed, FUN_EQ_THM, AC CONJ_ASSOC CONJ_COMM]
QED

Theorem univR_graph_11[simp]:
  univR_graph R1 = univR_graph R2 ⇔ R1 = R2
Proof
  simp[ulabgraph_component_equality, FUN_EQ_THM, is_hypergraph_def] >>
  simp[EQ_IMP_THM, PULL_EXISTS]
QED

Theorem nodes_restrR_graph:
  nodes (restrR_graph R) = { INL a | (∃b. R a b) ∨ (∃b. R b a) }
Proof
  simp[restrR_graph_def, nodes_def, #repabs_pseudo_id tydefrec,
       wfgraph_restrR_graph0] >>
  simp[restrR_graph0_def, EXTENSION] >> metis_tac[]
QED

Theorem edges_restrR_graph[simp]:
  edges (restrR_graph R) = { directed (INL x) (INL y) () | R x y }
Proof
  simp[restrR_graph_def, edges_def, #repabs_pseudo_id tydefrec,
       wfgraph_restrR_graph0, edgebag_def] >>
  simp[restrR_graph0_def, EXTENSION]
QED

Theorem adjacent_restrR_graph[simp]:
  adjacent (restrR_graph R) a b = ∃a0 b0. a = INL a0 ∧ b = INL b0 ∧ R a0 b0
Proof
  simp[adjacent_directed, FUN_EQ_THM, AC CONJ_COMM CONJ_ASSOC]
QED

Theorem restrR_graph_11[simp]:
  restrR_graph r1 = restrR_graph r2 ⇔ r1 = r2
Proof
  simp[ulabgraph_component_equality, nodes_restrR_graph, is_hypergraph_def] >>
  simp[EQ_IMP_THM] >>
  simp[FORALL_AND_THM, PULL_EXISTS] >>
  simp[FUN_EQ_THM] >> metis_tac[]
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
      (UNIV: (('a + num -> 'a + num -> bool) # ('a+num) set) set)
Proof
  simp[INJ_IFF, ulabgraph_component_equality, is_hypergraph_def] >> metis_tac[]
QED

Definition stripped_def:
  stripped g ⇔ nodes g = { a | ∃e. e ∈ edges g ∧ a ∈ incident e ∧ ISL a }
End

Theorem stripped_restrR_graph[simp]:
  stripped (restrR_graph r)
Proof
  dsimp[stripped_def, PULL_EXISTS, nodes_restrR_graph] >>
  dsimp[EXTENSION, SF CONJ_ss] >> metis_tac[]
QED

Theorem relgraph_adjacent_EQ_edges_EQ:
  adjacent (g1 : α relgraph) = adjacent g2 ⇔
  edges g1 = edges g2
Proof
  simp[SimpLHS, FUN_EQ_THM] >>
  simp[adjacent_directed, EXTENSION, FORALL_PROD, enodesEQ, SF CONJ_ss,
       SF DNF_ss] >>
  simp[Once EQ_IMP_THM] >>
  simp[edges_def] >> strip_tac >> Cases >> simp[]
QED

Theorem stripped_graph_relation_bij:
  BIJ (λg m n. adjacent g (INL m) (INL n)) { g : α relgraph | stripped g } UNIV
Proof
  simp[BIJ_DEF, INJ_IFF, SURJ_DEF] >> conj_tac
  >- (qx_genl_tac [‘g1’, ‘g2’] >> rpt strip_tac >>
      simp[ulabgraph_component_equality, Once EQ_IMP_THM, is_hypergraph_def] >>
      strip_tac >>
      ‘adjacent g1 = adjacent g2’
        by (gvs[FUN_EQ_THM, sumTheory.FORALL_SUM] >> rpt strip_tac >> iff_tac >>
            strip_tac >> drule adjacent_members >> gvs[stripped_def]) >>
      gvs[] >>
      gs[relgraph_adjacent_EQ_edges_EQ, stripped_def]) >>
  qx_gen_tac ‘R’ >>
  qexists‘restrR_graph R’ >>
  simp[] >> simp[FUN_EQ_THM]
QED

Definition univnodes_def:
  univnodes g ⇔ nodes g = IMAGE INL UNIV
End

Theorem univnodes_univR_graph[simp]:
  univnodes (univR_graph R)
Proof
  simp[univnodes_def]
QED

Theorem univnodes_graph_relation_bij:
  BIJ (λg m n. adjacent g (INL m) (INL n)) { g:'a relgraph | univnodes g } UNIV
Proof
  simp[BIJ_DEF, INJ_IFF, SURJ_DEF] >> conj_tac
  >- (qx_genl_tac [‘g1’, ‘g2’] >> rpt strip_tac >>
      simp[ulabgraph_component_equality, Once EQ_IMP_THM, is_hypergraph_def] >>
      strip_tac >>
      ‘adjacent g1 = adjacent g2’
        by (gvs[FUN_EQ_THM, sumTheory.FORALL_SUM]>> rpt strip_tac >> iff_tac >>
            strip_tac >> drule adjacent_members >> gvs[univnodes_def]) >>
      gvs[] >> gs[univnodes_def]) >>
  qx_gen_tac ‘R’ >> qexists ‘univR_graph R’ >> simp[FUN_EQ_THM]
QED

Theorem univnodes_graph_symrelation_bij:
  BIJ (λg m n. adjacent g (INL m) (INL n))
      { g : (α,INF_OK,SL_OK) udulgraph | univnodes g }
      { r : α -> α -> bool | symmetric r }
Proof
  simp[BIJ_DEF, INJ_IFF, SURJ_DEF, relationTheory.symmetric_def,
       adjacent_SYM] >> conj_tac
  >- (simp[ulabgraph_component_equality, is_hypergraph_def] >>
      qx_genl_tac [‘g1’, ‘g2’] >>
      strip_tac >> simp[Once EQ_IMP_THM] >> strip_tac >>
      ‘adjacent g1 = adjacent g2’
        by (gvs[FUN_EQ_THM, sumTheory.FORALL_SUM]>> rpt strip_tac >> iff_tac >>
            strip_tac >> drule adjacent_members >> gvs[univnodes_def]) >>
      gvs[] >> gvs[univnodes_def]) >>
  qx_gen_tac ‘R’ >> strip_tac >>
  qexists ‘graph_ABS <| nodes := IMAGE INL UNIV;
                        edges := BAG_OF_SET { HE {INL x; INL y} () | R x y };
                        nlab := K ();
                        nfincst := (:INF_OK);
                        dircst := (:undirectedG) ;
                        slcst := (:SL_OK) ; (* self-loops allowed *)
                        edgecst := (:unit);
                     |>’ >>
  qmatch_abbrev_tac ‘univnodes (graph_ABS G0) ∧ _’ >>
  ‘G0.nodes = IMAGE INL UNIV ∧
   G0.edges = BAG_OF_SET {HE {INL x; INL y} () | R x y}’ by simp[Abbr‘G0’] >>
  ‘wfgraph G0’
    by (simp[wfgraph_def, ITSELF_UNIQUE, itself2set_def, finite_cst_def] >>
        simp[PULL_EXISTS] >>
        dsimp[edge_cst_def, SF CONJ_ss, PULL_EXISTS, INSERT2_lemma,
              itself2_4_def] >>
        simp[only_one_edge_def, PULL_EXISTS, BAG_OF_SET, AllCaseEqs()]) >>
  simp[univnodes_def, nodes_def, #repabs_pseudo_id tydefrec] >>
  simp[FUN_EQ_THM, udedges_def, adjacent_undirected,
       #repabs_pseudo_id tydefrec] >>
  simp[edgebag_def, #repabs_pseudo_id tydefrec] >>
  simp[INSERT2_lemma] >> metis_tac[]
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

Theorem FINITE_edges[simp]:
  FINITE $ edges (g : (α,directedG,finiteG,σ)ulabgraph)
Proof
  irule SUBSET_FINITE >>
  qexists ‘IMAGE (λ(m,n). directed m n ()) (nodes g × nodes g)’ >> simp[] >>
  simp[SUBSET_DEF, FORALL_PROD, EXISTS_PROD] >> Cases >> simp[] >>
  rpt strip_tac >> irule incident_SUBSET_nodes >>
  first_assum $ irule_at Any >> simp[]
QED

Theorem IN_udedges_E:
  hyper f l ∈ udedges g ⇒ ∃m n. f = {m;n}
Proof
  simp[udedges_def] >> strip_tac >> drule_at Any nonhypergraph_edges >>
  simp[is_hypergraph_def]
QED

Theorem FINITE_udedges:
  FINITE $ udedges (g : (α,undirectedG,finiteG,σ)ulabgraph)
Proof
  irule SUBSET_FINITE >>
  qexists ‘IMAGE (λ(m,n). hyper {m; n} ()) (nodes g × nodes g)’ >> simp[] >>
  simp[SUBSET_DEF, FORALL_PROD, EXISTS_PROD] >> Cases >> simp[] >>
  strip_tac >> drule IN_udedges_E >> simp[PULL_EXISTS] >> rw[] >>
  irule_at Any EQ_REFL >> drule incident_udedges_SUBSET_nodes >> simp[]
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
      slokp = itself2bool (:σ) ;
      eset = if slokp then eset0 else { e | e ∈ eset0 ∧ ¬selfloop e } ;
      ns = { n | ∃m l. directed m n l ∈ eset ∨ directed n m l ∈ eset } ;
  in
    if itself2bool(:ν) ∧ INFINITE ns then g
    else
      case itself2_4 (:'ec) of
        (F,F) =>
          let edges_to_add = { directed m n l | directed m n l ∈ eset ∧
                                                ∀l'. directed m n l' ∈ eset ⇒
                                                     l' = l }
          in
            g with <| edges := BAG_OF_SET {directed m n l

     if FINITE ecset then
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

Theorem removeNode_NONMEMBER:
  n ∉ nodes g ⇒ (removeNode n g = g)
Proof
  simp[gengraph_component_equality, DELETE_NON_ELEMENT_RWT] >>
  simp[EXTENSION] >> metis_tac[incident_SUBSET_nodes]
QED

Theorem removeNode_LCOMM:
  removeNode m (removeNode n g) = removeNode n (removeNode m g)
Proof
  simp[gengraph_component_equality, DELETE_COMM, DIFF_COMM] >>
  simp[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >> rw[]
QED

Definition removeNodes_def:
  removeNodes G N = ITSET removeNode N G
End

Definition removeEdge0_def:
  removeEdge0 e (grep: (α,δ,'ec,'ei,ν,'nl,σ) graphrep) =
  if itself2bool (:δ) then
    grep with edges := grep.edges DELETE e
  else
    grep with edges := grep.edges DIFF {e; flip_edge e}
End

Theorem wfgraph_removeEdge0:
  wfgraph grep ⇒ wfgraph (removeEdge0 e grep)
Proof
  rw[wfgraph_def, removeEdge0_def, ITSELF_UNIQUE, edge_cst_DELETE,
     edge_cst_DIFF] >~
  [‘flip_edge e1 ≠ e2’] >- (strip_tac >> gvs[])
QED

Definition removeEdge_def:
  removeEdge e g = graph_ABS $ removeEdge0 e $ graph_REP g
End

Theorem nodes_removeEdge[simp]:
  nodes (removeEdge e g) = nodes g
Proof
  simp[removeEdge_def, nodes_def, #termP_term_REP tydefrec,
       #repabs_pseudo_id tydefrec, wfgraph_removeEdge0] >>
  rw[removeEdge0_def]
QED

Theorem diredges_removeEdge[simp]:
  edges (removeEdge e (g:(α,directedG,'ec,'ei,ν,'nl,σ) graph)) =
  edges g DELETE e
Proof
  simp[removeEdge_def, edges_def, #termP_term_REP tydefrec,
       #repabs_pseudo_id tydefrec, wfgraph_removeEdge0] >>
  simp[removeEdge0_def, ITSELF_UNIQUE]
QED

Theorem nlabelfun_removeEdge[simp]:
  nlabelfun (removeEdge e g) = nlabelfun g
Proof
  simp[removeEdge_def, nlabelfun_def, #termP_term_REP tydefrec,
       #repabs_pseudo_id tydefrec, wfgraph_removeEdge0] >>
  rw[removeEdge0_def]
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

Theorem edges_addUDEdge_udul:
  edges (addUDEdge m n lab (g:(α,ν,σ)udulgraph)) =
  if selfloops_ok g ∨ m ≠ n then
    edges g ∪ {(m,n,()); (n,m,())}
  else edges g
Proof
  simp[addUDEdge_def, edges_def, #repabs_pseudo_id tydefrec,
       #termP_term_REP tydefrec, wfgraph_addUDEdge0] >>
  simp[addUDEdge0_def, ITSELF_UNIQUE] >> rw[] >> gvs[] >>
  simp[EXTENSION,FORALL_PROD] >> metis_tac[]
QED

Theorem addUDEdge_udul_LCOMM:
  addUDEdge m n l1 (addUDEdge a b l2 g : (α,ν,σ)udulgraph) =
  addUDEdge a b l2 (addUDEdge m n l1 g)
Proof
  simp[gengraph_component_equality] >> rw[]
  >- SET_TAC[]
  >- (simp[edges_addUDEdge_udul] >> rw[] >> gvs[] >>
      SET_TAC[]) >>
  simp[FUN_EQ_THM]
QED

Theorem edges_ITSET_addUDEdge_udul:
  ∀A g : (α,ν,σ) udulgraph.
    FINITE A ∧ (∀m n. (m,n) ∈ A ⇒ m ∈ nodes g ∧ n ∈ nodes g) ∧
    (¬selfloops_ok g ⇒ ∀m n. (m,n) ∈ A ⇒ m ≠ n)
    ⇒
    edges (ITSET (λ(m,n) g. addUDEdge m n () g) A g) =
    { (m,n,()) | (m,n) ∈ A } ∪ { (m,n,()) | (n,m) ∈ A } ∪ edges g
Proof
  Induct_on ‘FINITE’ >>
  simp[COMMUTING_ITSET_RECURSES, FORALL_PROD, addUDEdge_udul_LCOMM,
       DELETE_NON_ELEMENT_RWT, edges_addUDEdge_udul] >> rw[] >>
  gs[DISJ_IMP_THM, FORALL_AND_THM] >>
  first_x_assum $ drule_then strip_assume_tac >> simp[] >> rw[] >>
  ASM_SET_TAC[]
QED

Theorem selfloop_ok_thm:
  (m,m,l) ∈ edges g ⇒ selfloops_ok g
Proof
  simp[edges_def] >> rpt strip_tac >>
  ‘wfgraph (graph_REP g)’ by simp[#termP_term_REP tydefrec] >>
  gs[wfgraph_def, ITSELF_UNIQUE, FORALL_PROD] >> metis_tac[]
QED

Theorem edges_removeEdge:
  edges (removeEdge e g:(α,δ,'ec,'ei,ν,'nl,σ)graph) =
  if itself2bool(:δ) then edges g DELETE e
  else edges g DIFF {e; flip_edge e}
Proof
  simp[edges_def, removeEdge_def, #termP_term_REP tydefrec,
       #repabs_pseudo_id tydefrec, wfgraph_removeEdge0] >>
  simp[removeEdge0_def] >> rw[]
QED

Theorem removeEdge_LCOMM:
  removeEdge e1 (removeEdge e2 g) = removeEdge e2 (removeEdge e1 g)
Proof
  simp[gengraph_component_equality, edges_removeEdge] >> rw[] >>
  simp[DELETE_COMM, DIFF_COMM]
QED

val _ = export_theory();
val _ = html_theory "genericGraph";
