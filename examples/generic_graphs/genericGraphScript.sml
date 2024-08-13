open HolKernel Parse boolLib bossLib;

open pred_setTheory pairTheory bagTheory liftingTheory transferTheory
     transferLib

(* Material on finite simple graphs mechanised from
     "Combinatorics and Graph Theory" by Harris, Hirst, and Mossinghoff
 *)

val _ = new_theory "genericGraph";

Datatype: diredge = directed ((α+num) set) ((α+num) set) 'label
End
Datatype: undiredge = undirected ((α+num) set) 'label
End
Datatype:
  core_edge = cDE (('a,'l) diredge) | cUDE (('a,'l) undiredge)
End
Overload DE = “λm n l. cDE (directed m n l)”
Overload UDE = “λns l. cUDE (undirected ns l)”

Theorem FORALL_DIREDGE:
  (∀de. P de) ⇔ ∀ms ns lab. P (directed ms ns lab)
Proof
  simp[EQ_IMP_THM] >> strip_tac >> Cases >> simp[]
QED

Theorem EXISTS_UNDIREDGE:
  (∃ud:('a,'l)undiredge. P ud) ⇔ ∃ns l. P (undirected ns l)
Proof
  iff_tac >> rw[] >> simp[SF SFY_ss] >>
  Cases_on ‘ud’>> metis_tac[]
QED

Theorem core_edge_cases:
  ∀e. (∃m n l. e = DE m n l) ∨ (∃ns l. e = UDE ns l)
Proof
  Cases >> simp[] >>
  metis_tac[TypeBase.nchotomy_of “:('a,'l) diredge”,
            TypeBase.nchotomy_of “:('a,'l) undiredge”]
QED

val _ = TypeBase.export [
  TypeBasePure.put_nchotomy core_edge_cases
             (valOf (TypeBase.read {Tyop = "core_edge",
                                    Thy = "genericGraph"}))
  ];

Definition is_directed_edge_def[simp]:
  is_directed_edge (cDE _ ) = T ∧
  is_directed_edge (cUDE _ ) = F
End
Definition denodes_def[simp]:
  denodes (directed m n l) = (m,n)
End
Definition udenodes_def[simp]:
  udenodes (undirected ns l) = ns
End
Definition enodes_def[simp]:
  enodes (cDE de) = INL (denodes de) ∧
  enodes (cUDE he) = INR (udenodes he)
End

Theorem enodesEQ:
  (enodes e = INL (m,n) ⇔ ∃l. e = DE m n l) ∧
  (enodes e = INR ns ⇔ ∃l. e = UDE ns l)
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
  incidentDE (directed n1 n2 lab) = n1 ∪ n2
End

Overload incident = “udenodes”
Overload incident = “incidentDE”

Definition core_incident_def[simp]:
  core_incident (cDE de) = incident de ∧
  core_incident (cUDE he) = incident he
End

Definition selfloop_def[simp]:
  selfloop (directed m n lab) ⇔ ¬(DISJOINT m n)
End

Definition gen_selfloop_def[simp]:
  gen_selfloop (cDE de) = selfloop de ∧
  gen_selfloop (cUDE he) = SING (udenodes he)
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
  flip_edge (cUDE he) = cUDE he
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
  (flip_edge e = UDE ns lab ⇔ e = UDE ns lab) ∧
  (UDE ns lab = flip_edge e ⇔ e = UDE ns lab)
Proof
  Cases_on ‘e’ >> simp[] >> metis_tac[]
QED

Theorem incident_dirflip_edge[simp]:
  incident (dirflip_edge de) = incident de
Proof
  Cases_on ‘de’ >> simp[UNION_COMM]
QED

Theorem incident_flip_edge[simp]:
  core_incident (flip_edge e) = core_incident e
Proof
  Cases_on ‘e’ >> simp[INSERT2_lemma, AC UNION_COMM UNION_ASSOC]
QED

Definition udedge_label_def[simp]:
  udedge_label (undirected ns l) = l
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
  edge_label (cUDE he) = udedge_label he
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

Datatype:
  edge_cst_vals = ONE_EDGE | ONE_EDGE_PERLABEL | FINITE_EDGES | UNC_EDGES
End

Definition itself2_ecv_def:
  itself2_ecv x =
  case itself2_4 x of
  | (F,F) => ONE_EDGE
  | (F,T) => ONE_EDGE_PERLABEL
  | (T,F) => FINITE_EDGES
  | (T,T) => UNC_EDGES
End

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

Definition dirhypcst_def:
  dirhypcst dirp hypp slp ebag ⇔
    case (itself2bool dirp, itself2bool hypp, itself2bool slp) of
    | (F, F, F) => (∀e. e ∈ set ebag ⇒ ∃m n l. e = UDE {m;n} l ∧ m ≠ n)
    | (F, F, T) => (∀e. e ∈ set ebag ⇒ ∃m n l. e = UDE {m;n} l)
    | (F, T, F) => (∀e. e ∈ set ebag ⇒
                        ∃ns l. e = UDE ns l ∧ (FINITE ns ⇒ 2 ≤ CARD ns))
    | (F, T, T) => (∀e. e ∈ set ebag ⇒ ∃ns l. e = UDE ns l ∧ ns ≠ ∅)
    | (T, F, F) => (∀e. e ∈ set ebag ⇒ ∃m n l. e = DE {m} {n} l ∧ m ≠ n)
    | (T, F, T) => (∀e. e ∈ set ebag ⇒ ∃m n l. e = DE {m} {n} l)
    | (T, T, F) => (∀e. e ∈ set ebag ⇒
                        ∃ms ns l. e = DE ms ns l ∧ DISJOINT ms ns ∧
                                  ms ≠ ∅ ∧ ns ≠ ∅)
    | (T, T, T) => (∀e. e ∈ set ebag ⇒
                        ∃ms ns l. e = DE ms ns l ∧ ms ≠ ∅ ∧ ns ≠ ∅)
End

Definition edge_cst_def:
  edge_cst ecst ebag ⇔
    (case itself2_ecv ecst of
     | ONE_EDGE => only_one_edge ebag
     | ONE_EDGE_PERLABEL => only_one_edge_per_label ebag
     | FINITE_EDGES => finite_edges_per_nodeset ebag
     | UNC_EDGES => T)
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
    exthm  = prove(“∃x:num. (λx. T) x”, simp[]),
    ABS    = "undirectedG_ABS",
    REP    = "undirectedG_REP"};

val unhyperG_tydefrec = newtypeTools.rich_new_type
   {tyname = "unhyperG",
    exthm  = prove(“∃x:num. (λx. T) x”, simp[]),
    ABS    = "unhyperG_ABS",
    REP    = "unhyperG_REP"};

val directedG_tydefrec = newtypeTools.rich_new_type
   {tyname = "directedG",
    exthm  = prove(“∃x:unit. (λx. T) x”, simp[]),
    ABS    = "directedG_ABS",
    REP    = "directedG_REP"};

val hyperG_tydefrec = newtypeTools.rich_new_type
   {tyname = "hyperG",
    exthm  = prove(“∃x:unit. (λx. T) x”, simp[]),
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

val oneEdge_tydefrec = newtypeTools.rich_new_type
   {tyname = "oneedgeG",
    exthm  = prove(“∃x:unit. (λx. T) x”, simp[]),
    ABS    = "oneedgeG_ABS",
    REP    = "oneedgeG_REP"};

val oneedgeplG_tydefrec = newtypeTools.rich_new_type
   {tyname = "oneedgeplG",
    exthm  = prove(“∃x:bool. (λx. T) x”, simp[]),
    ABS    = "oneedgeplG_ABS",
    REP    = "oneedgeplG_REP"};

Theorem UNIV_UNIT[simp]:
  UNIV : unit set = {()}
Proof
  simp[EXTENSION]
QED

Theorem UNIV_oneedgeG[simp]:
  univ(:oneedgeG) = {oneedgeG_ABS ()}
Proof
  simp[EXTENSION, SYM $ #term_REP_11 oneEdge_tydefrec]
QED

Theorem UNIV_oneedgeplG[simp]:
  univ(:oneedgeplG) = {oneedgeplG_ABS F; oneedgeplG_ABS T}
Proof
  simp[EXTENSION, SYM $ #term_REP_11 oneedgeplG_tydefrec,
       #repabs_pseudo_id oneedgeplG_tydefrec]
QED

Theorem itself2_ecv_oneedgeG[simp]:
  itself2_ecv (:oneedgeG) = ONE_EDGE
Proof
  simp[itself2_ecv_def, itself2_4_def]
QED

Theorem itself2_ecv_oneedgeplG[simp]:
  itself2_ecv (:oneedgeplG) = ONE_EDGE_PERLABEL
Proof
  simp[itself2_ecv_def, itself2_4_def, #term_ABS_pseudo11 oneedgeplG_tydefrec]
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

Theorem UNIV_finiteEdges[simp]:
  univ(:finiteEdges) = {finiteEdges_ABS (SOME F); finiteEdges_ABS (SOME T);
                        finiteEdges_ABS NONE}
Proof
  simp[EXTENSION, SYM $ #term_REP_11 finiteEdges_tydefrec,
       #repabs_pseudo_id finiteEdges_tydefrec
      ] >> qx_gen_tac ‘e’ >> Cases_on ‘finiteEdges_REP e’ >> simp[]
QED

Theorem itself2_ecv_finiteEdges[simp]:
  itself2_ecv (:finiteEdges) = FINITE_EDGES
Proof
  simp[itself2_ecv_def, itself2_4_def,
       AllCaseEqs(), #term_ABS_pseudo11 finiteEdges_tydefrec]
QED

Theorem itself2bool_undirectedG[simp]:
  itself2bool (:undirectedG) = F
Proof
  simp[itself2bool_def, AllCaseEqs(), infinite_num_inj] >>
  qexists ‘undirectedG_ABS’ >>
  simp[INJ_IFF, #term_ABS_pseudo11 undirectedG_tydefrec]
QED

Theorem itself2bool_unhyperG[simp]:
  itself2bool (:unhyperG) = F
Proof
  simp[itself2bool_def, AllCaseEqs(), infinite_num_inj] >>
  qexists ‘unhyperG_ABS’ >>
  simp[INJ_IFF, #term_ABS_pseudo11 unhyperG_tydefrec]
QED

Theorem UNIV_hyperG[simp]:
  univ(:hyperG) = {hyperG_ABS ()}
Proof
  simp[EXTENSION, SYM $ #term_REP_11 hyperG_tydefrec]
QED

Theorem itself2bool_hyperG[simp]:
  itself2bool (:hyperG) = T
Proof
  simp[itself2bool_def]
QED


Theorem INFINITE_UINF_OK[simp]:
  INFINITE univ(:INF_OK)
Proof
  simp[infinite_num_inj] >> qexists ‘INF_OK_ABS’ >>
  simp[INJ_IFF, #term_ABS_pseudo11 INF_OK_tydefrec]
QED

Theorem itself2_4_allEdgesOK[simp]:
  itself2_ecv (:allEdgesOK) = UNC_EDGES
Proof
  simp[itself2_ecv_def, itself2_4_def, AllCaseEqs(), infinite_num_inj] >>
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

Theorem itself2_ecv_unit[simp]:
  itself2_ecv (:unit) = ONE_EDGE
Proof
  simp[itself2_ecv_def, itself2_4_def]
QED

(* generic graphs
*)
Datatype:
  graphrep = <| nodes : ('a+num) set ;
                  (* useful to have countable space to expand into *)
                edges : ('a,'el) core_edge bag ;
                hyperp : 'hyperp itself;
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
    edge_cst grep.edgecst grep.edges ∧
    dirhypcst grep.dircst grep.hyperp grep.slcst grep.edges ∧
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

Theorem dirhypcst_EMPTY[simp]:
  dirhypcst x y z EMPTY_BAG
Proof
  rw[dirhypcst_def]
QED

Theorem edge_cst_EMPTY[simp]:
  edge_cst w EMPTY_BAG
Proof
  rw[edge_cst_def, finite_edges_per_nodeset_def, only_one_edge_per_label_def,
     only_one_edge_def] >>
  rename [‘itself2_ecv X’] >> Cases_on ‘itself2_ecv X’ >> simp[]
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

Theorem dirhypcst_DELETE:
  dirhypcst x y z es0 ∧ BAG_DELETE es0 e es ⇒ dirhypcst x y z es
Proof
  rw[dirhypcst_def, BAG_DELETE]
QED

Theorem edge_cst_DELETE:
  edge_cst w es0 ∧ BAG_DELETE es0 e es ⇒ edge_cst w es
Proof
  simp[edge_cst_def] >> rw[] >>
  rename [‘itself2_ecv ecst’] >> Cases_on ‘itself2_ecv ecst’ >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM, BAG_DELETE] >>~-
  ([‘only_one_edge_per_label (BAG_INSERT e es)’, ‘only_one_edge_per_label es’],
   drule only_one_edge_per_label_BAG_INSERT >> simp[]) >>~-
  ([‘only_one_edge (BAG_INSERT e es)’, ‘only_one_edge es’],
   drule only_one_edge_BAG_INSERT >> simp[])
QED

Theorem graphs_exist[local]:
  ∃g. wfgraph g
Proof
  qexists ‘<| nodes := {};
              edges := EMPTY_BAG;
              hyperp := ARB;
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

Definition AR_def:
  AR r a ⇔ wfgraph r ∧ r = graph_REP a
End

Definition ceq_def:
  ceq gr1 gr2 ⇔ gr1 = gr2 ∧ wfgraph gr1
End

Theorem wfgraph_relates[transfer_rule]:
  (AR ===> (=)) wfgraph (K T)
Proof
  simp[FUN_REL_def, AR_def]
QED

Theorem AReq_relates[transfer_rule]:
  (AR ===> AR ===> (=)) (=) (=)
Proof
  simp[AR_def, FUN_REL_def, #termP_term_REP tydefrec, #term_REP_11 tydefrec]
QED

Theorem right_unique_AR[transfer_simp]:
  right_unique AR
Proof
  simp[right_unique_def, AR_def, #term_REP_11 tydefrec]
QED

Theorem surj_AR[transfer_simp]:
  surj AR
Proof
  simp[surj_def, AR_def, #termP_term_REP tydefrec]
QED

Theorem RDOM_AR[transfer_simp]:
  RDOM AR = {gr | wfgraph gr}
Proof
  simp[relationTheory.RDOM_DEF, Once FUN_EQ_THM, AR_def, SF CONJ_ss,
       #termP_term_REP tydefrec] >>
  metis_tac[#termP_term_REP tydefrec, #repabs_pseudo_id tydefrec]
QED


Theorem Qt_graphs:
  Qt ceq graph_ABS graph_REP AR
Proof
  simp[Qt_alt, AR_def, #absrep_id tydefrec, ceq_def, #termP_term_REP tydefrec]>>
  simp[SF CONJ_ss, #term_ABS_pseudo11 tydefrec] >>
  simp[SF CONJ_ss, FUN_EQ_THM, AR_def, #termP_term_REP tydefrec,
       CONJ_COMM] >>
  simp[EQ_IMP_THM, #termP_term_REP tydefrec, #absrep_id tydefrec,
       #repabs_pseudo_id tydefrec]
QED

(* any undirected (non-hyper) graph *)
Type udgraph[pp] = “:('a,undirectedG,'ec,'el,unhyperG,'nf,'nl,'sl)graph”

(* finite directed graph with labels on nodes and edges, possibility of
   multiple, but finitely many edges, and with self-loops allowed *)
Type fdirgraph[pp] = “:('NodeEnum,
                        directedG,
                        finiteEdges (* finitely many edges between nodes *),
                        'edgelabel,
                        unhyperG,
                        finiteG (* finitely many nodes *),
                        'NodeLabel (* capitalised to precede 'edge *),
                        SL_OK (* self-loops OK *)
                       ) graph”

Type allokdirgraph[pp] = “:('NodeEnum,
                            directedG,
                            allEdgesOK,
                            'edgelabel,
                            hyperG,
                            INF_OK,
                            'NodeLabel,
                            SL_OK) graph”

(* unlabelled graph *)
Type ulabgraph[pp] = “:(α,
                        δ (* undirected? *),
                        oneedgeG,
                        unit (* edge label *),
                        'h,
                        ν (* infinite nodes allowed? *),
                        unit (* node label *),
                        σ (* self-loops? *)) graph”
Type ulabgraphrep[local] = “:(α,δ,oneedgeG,unit,'h,ν,unit,σ) graphrep”

(* undirected+unhyper version of the same *)
Type udulgraph[pp] = “:(α, undirectedG, unhyperG, ν, σ)ulabgraph”
Type udulgraphrep[local] = “:(α,undirectedG,unhyperG, ν,σ)ulabgraphrep”

(* a relation graph; stripped such are in bijection with binary relations.
   (The stripping makes a canonical, minimal choice of node set in the graph.)
 *)
Type relgraph[pp] = “:(α, directedG, unhyperG, INF_OK, SL_OK) ulabgraph”


Theorem funQ'[local] = SRULE[GSYM AND_IMP_INTRO] funQ |> GEN_ALL

Theorem HK_thm2'[local] = HK_thm2 |> GEN_ALL |> SRULE[]

fun grt th1 th2 = resolve_then.gen_resolve_then Any th1 th2 I

fun tidy_tyvars th =
  let val tyvs = type_vars_in_term (concl th)
      val newvs =
        List.tabulate(length tyvs,
                      fn i => mk_vartype("'" ^ str (Char.chr(i + 97))))
  in
      INST_TYPE (ListPair.map(fn (ty1,ty2) => ty1 |-> ty2) (tyvs, newvs)) th
  end

fun opxfer res_th =
  grt res_th HK_thm2 |> repeat (grt funQ') |> repeat (grt Qt_graphs)
                     |> repeat (grt idQ) |> tidy_tyvars
                     |> CONV_RULE Unwind.UNWIND_FORALL_CONV

Definition emptyG0_def:
    emptyG0 : (α,δ,'ec,'el,'h, ν,'nl,σ) graphrep =
     <| nodes := {} ; edges := {||}; nlab := K ARB;
        nfincst := (:ν); dircst := (:δ); slcst := (:σ);
        edgecst := (:'ec) |>
End

fun liftdef respth nm =
  let
    val xfer = opxfer respth
    val defrhs = rand (concl xfer)
    val cvar = mk_var(nm, type_of defrhs)
    val def = new_definition (nm ^ "_def", mk_eq(cvar, defrhs))
    val relates = save_thm(nm ^ "_relates[transfer_rule]",
                           REWRITE_RULE [SYM def] xfer)
  in
    (def, relates)
  end

Theorem emptyG0_respects:
  ceq emptyG0 emptyG0
Proof
  simp[ceq_def, wfgraph_def, emptyG0_def, finite_cst_def]
QED
val _ = liftdef emptyG0_respects "emptyG"

Theorem nodes_respects:
  (ceq ===> (=)) graphrep_nodes graphrep_nodes
Proof
  simp[ceq_def, FUN_REL_def]
QED
val _ = liftdef nodes_respects "nodes"


Theorem edges_respects:
  (ceq ===> (=) ===> (=)) graphrep_edges graphrep_edges
Proof
  simp[ceq_def, FUN_REL_def]
QED
val (e1,e2) = liftdef edges_respects "edgebag"

Definition edges_def:
  edges (G:(α,directedG,'ec,'el,'h,ν,'nl,σ) graph) =
  {de | cDE de ∈ set $ edgebag G}
End

Definition udedges_def:
  udedges (G:(α,'ec,'el,'nf,'nl,'sl) udgraph) = {he | cUDE he ∈ set (edgebag G)}
End

Theorem incident_SUBSET_nodes:
  ∀g e n. e ∈ edges g ∧ n ∈ incident e ⇒ n ∈ nodes g
Proof
  simp[edges_def] >> xfer_back_tac[] >>
  rw[wfgraph_def, SUBSET_DEF] >> first_x_assum irule >>
  first_assum $ irule_at Any >> simp[]
QED

Theorem incident_udedges_SUBSET_nodes:
  ∀g e n. e ∈ udedges g ∧ n ∈ incident e ⇒ n ∈ nodes g
Proof
  simp[udedges_def] >> xfer_back_tac [] >>
  rw[wfgraph_def, SUBSET_DEF, ITSELF_UNIQUE] >>
  first_x_assum irule >> first_assum $ irule_at Any >> simp[]
QED

Theorem nlabelfun_respects:
  (ceq ===> (=) ===> (=)) graphrep_nlab graphrep_nlab
Proof
  simp[ceq_def, FUN_REL_def]
QED
val (nl1,nl2) = liftdef nlabelfun_respects "nlabelfun"

Theorem nlabelfun_EQ_ARB[simp]:
  ∀g n. n ∉ nodes g ⇒ nlabelfun g n = ARB
Proof
  xfer_back_tac[] >> rw[wfgraph_def]
QED

Theorem nodes_empty[simp]:
  nodes emptyG = ∅
Proof
  xfer_back_tac[] >> simp[emptyG0_def]
QED

Theorem edgebag_empty[simp]:
  edgebag emptyG = {||}
Proof
  xfer_back_tac [] >> simp[emptyG0_def]
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
  xfer_back_tac[] >> simp[emptyG0_def, FUN_EQ_THM]
QED

Definition adjacent_def:
  adjacent G m n ⇔
    ∃e ms ns.
      e ∈ set (edgebag G) ∧
      (enodes e = INL (ms,ns) ∧ m ∈ ms ∧ n ∈ ns ∨
       enodes e = INR {m;n})
End

Theorem dirhypcst_directedG:
  dirhypcst (:directedG) hypp slcst ebag ⇒
  ∀e. e ∈ set ebag ⇒ is_directed_edge e
Proof
  gvs[dirhypcst_def] >> rw[] >> first_x_assum drule >>
  simp[PULL_EXISTS]
QED

Theorem dirhypcst_undirectedG:
  dirhypcst (:undirectedG) (:unhyperG) slcst ebag ⇒
  ∀e. e ∈ set ebag ⇒ ¬is_directed_edge e ∧
                     ∃m n. core_incident e = {m;n}
Proof
  simp[dirhypcst_def] >> rw[COND_EXPAND_OR] >>
  first_x_assum drule >>
  dsimp[PULL_EXISTS, INSERT2_lemma] >> rw[]
QED

Theorem adjacent_directed:
  ∀G m n.
    adjacent (G : (α,directedG,'ec,'el,'h,'nf,'nl,'sl)graph) m n ⇔
    ∃ms ns l. directed ms ns l ∈ edges G ∧ m ∈ ms ∧ n ∈ ns
Proof
  simp[adjacent_def, edges_def] >> xfer_back_tac[] >>
  rw[wfgraph_def, ITSELF_UNIQUE] >>
  drule_then strip_assume_tac dirhypcst_directedG >> iff_tac >> rw[] >>
  gvs[IN_SET_OF_BAG, enodesEQ, SF SFY_ss]
  >- (first_x_assum drule >> simp[]) >>
  first_assum $ irule_at Any >> simp[]
QED

Theorem adjacent_undirected:
  ∀G m n.
    adjacent (G : ('a,'ec,'el,'nf,'nl,'sl)udgraph) m n ⇔
      ∃l. undirected {m;n} l ∈ udedges G
Proof
  simp[adjacent_def, udedges_def] >> xfer_back_tac[] >>
  rw[wfgraph_def, ITSELF_UNIQUE] >>
  drule_then strip_assume_tac dirhypcst_undirectedG >> iff_tac >> rw[] >>
  gvs[IN_SET_OF_BAG, enodesEQ, SF SFY_ss]
  >- (first_x_assum drule >> simp[]) >>
  metis_tac[]
QED

Theorem adjacent_SYM:
  adjacent (G:('a,'ec,'el,'nf,'nl,'sl)udgraph) m n ⇔ adjacent G n m
Proof
  simp[adjacent_undirected] >> metis_tac[INSERT_COMM]
QED

Theorem adjacent_empty[simp]:
  adjacent emptyG m n ⇔ F
Proof
  simp[adjacent_def]
QED

Theorem edges_irrefl[simp]:
  ∀a l G. directed a a l ∉ edges (G:('a,directedG,'ec,'el,'h,'nf,'nl,noSL)graph)
Proof
  simp[edges_def] >> xfer_back_tac[] >>
  rw[wfgraph_def, ITSELF_UNIQUE, FORALL_PROD, dirhypcst_def] >>
  strip_tac >> first_x_assum drule >> simp[SF CONJ_ss]
QED

Theorem adjacent_irrefl[simp]:
  ∀a G. adjacent (G:('a,'dir,'ec,'el,'h,'nf,'nl,noSL)graph) a a = F
Proof
  simp[adjacent_def] >> xfer_back_tac [] >>
  rw[wfgraph_def, ITSELF_UNIQUE, FORALL_PROD, dirhypcst_def] >>
  rename [‘¬BAG_IN e G.edges’] >> Cases_on ‘BAG_IN e G.edges’ >> simp[] >>
  first_x_assum drule >> simp[PULL_EXISTS] >> SET_TAC[]
QED

Definition addNode0_def:
  addNode0 n lab grep = grep with <| nodes updated_by (λs. n INSERT s);
                                     nlab := grep.nlab⦇n ↦ lab⦈ |>
End
Theorem addNode_respects:
  ((=) ===> (=) ===> ceq ===> ceq) addNode0 addNode0
Proof
  simp[FUN_REL_def, ceq_def] >>
  simp[wfgraph_def, addNode0_def] >>
  rw[finite_cst_def, SUBSET_DEF, combinTheory.UPDATE_APPLY] >> metis_tac[]
QED
val (an1,an2) = liftdef addNode_respects "addNode"

Theorem nodes_addNode[simp]:
  ∀n l G. nodes (addNode n l G) = n INSERT nodes G
Proof
  xfer_back_tac [] >> simp[addNode0_def]
QED

Theorem edgebag_addNode[simp]:
  ∀n l G. edgebag (addNode n l G) = edgebag G
Proof
  xfer_back_tac [] >> simp[addNode0_def]
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
  ∀n l g. nlabelfun (addNode n l g) = (nlabelfun g)⦇ n ↦ l ⦈
Proof
  xfer_back_tac[] >> simp[addNode0_def]
QED

Theorem adjacent_addNode[simp]:
  adjacent (addNode n l G) = adjacent G
Proof
  simp[adjacent_def, FUN_EQ_THM]
QED

Definition udfilter_insertedge_def:
  udfilter_insertedge ns lab ecst ebag =
  let e = UDE ns lab
  in
    case itself2_ecv ecst of
    | ONE_EDGE=> BAG_INSERT e $ BAG_FILTER (λe. core_incident e ≠ ns) ebag
    | ONE_EDGE_PERLABEL => if BAG_IN e ebag then ebag else BAG_INSERT e ebag
    | FINITE_EDGES => BAG_INSERT e ebag
    | UNC_EDGES => BAG_INSERT e ebag
End

Theorem BAG_IN_udfilter_insertedge:
  BAG_IN e (udfilter_insertedge ns lab ecst ebag) ⇒
  core_incident e = ns ∧ ¬is_directed_edge e ∨ BAG_IN e ebag
Proof
  simp[udfilter_insertedge_def] >> Cases_on ‘itself2_ecv ecst’ >>
  gvs[DISJ_IMP_THM] >> rw[] >> simp[]
QED

Theorem finite_edges_per_nodeset_udfilter_insertedge[local]:
  itself2_ecv(:'ec) = FINITE_EDGES ∧ finite_edges_per_nodeset ebag ⇒
  finite_edges_per_nodeset (udfilter_insertedge ns lab (:'ec) ebag)
Proof
  dsimp[finite_edges_per_nodeset_def, udfilter_insertedge_def, GSPEC_OR] >>
  simp[GSPEC_AND]
QED

Theorem only_one_edge_per_label_udfilter_insertedge[local]:
  itself2_ecv(:'ec) = ONE_EDGE_PERLABEL ∧ only_one_edge_per_label ebag ⇒
  only_one_edge_per_label (udfilter_insertedge ns lab (:'ec) ebag)
Proof
  dsimp[only_one_edge_per_label_def, udfilter_insertedge_def, GSPEC_OR] >>
  rw[BAG_IN, BAG_INN, BAG_INSERT] >>
  gvs[DECIDE “¬(x >= 1) ⇔ x = 0”] >> rw[] >> gvs[]
QED

Theorem only_one_edge_udfilter_insertedge[local]:
  itself2_ecv (:'ec) = ONE_EDGE ∧ only_one_edge ebag ⇒
  only_one_edge (udfilter_insertedge ns lab (:'ec) ebag)
Proof
  simp[only_one_edge_def, udfilter_insertedge_def] >> rw[] >> gvs[] >>
  simp[BAG_FILTER_DEF, BAG_INSERT, AllCaseEqs()] >>
  rename [‘enodes e’] >> Cases_on ‘e’ >> gvs[]
QED

Definition addUDEdge0_def:
  addUDEdge0 m n lab (G:('a,undirectedG,'ec,'el,'h,'nf,'nl,'sl)graphrep) =
  if m = n ∧ ¬itself2bool(:'sl) then G
  else
    G with <| nodes := {m;n} ∪ G.nodes ;
              edges := udfilter_insertedge {m;n} lab (:'ec) G.edges
           |>
End
Theorem addUDEdge_respects:
  ((=) ===> (=) ===> (=) ===> ceq ===> ceq) addUDEdge0 addUDEdge0
Proof
  simp[FUN_REL_def, ceq_def] >>
  simp[addUDEdge0_def, wfgraph_def, ITSELF_UNIQUE] >>
  Cases_on ‘m = n’ >> rw[finite_cst_UNION] >>~-
  ([‘BAG_IN e $ udfilter_insertedge _ _ _ _’],
   drule_then strip_assume_tac BAG_IN_udfilter_insertedge >> simp[] >>
   first_x_assum drule >> simp[SUBSET_DEF]) >>~-
  ([‘edge_cst _ _’, ‘edge_cst _ (udfilter_insertedge _ _ _ _)’],
   qpat_x_assum ‘edge_cst _ _’ mp_tac >>
   simp[edge_cst_def] >>
   rename [‘itself2_ecv ecst’] >>
   Cases_on ‘itself2_ecv ecst’ >>
   gvs[finite_edges_per_nodeset_udfilter_insertedge,
        only_one_edge_per_label_udfilter_insertedge,
        only_one_edge_udfilter_insertedge, ITSELF_UNIQUE]) >>
  gvs[dirhypcst_def] >>
  rw[] >>
  drule_then strip_assume_tac BAG_IN_udfilter_insertedge >>~-
  ([‘BAG_IN e g.edges (* a *)’], metis_tac[]) >>~-
  ([‘core_incident e = {m;n}’],
   Cases_on ‘e’ >> gvs[] >> irule_at Any EQ_REFL >> simp[])
QED
val (aud1,aud2) = liftdef addUDEdge_respects "addUDEdge"

Definition edge0_def:
  edge0 m n lab ecst edges =
  let e = DE {m} {n} lab
  in
    case itself2_ecv ecst of
      ONE_EDGE => BAG_INSERT e $ BAG_FILTER (λe. enodes e ≠ INL ({m},{n})) edges
    | ONE_EDGE_PERLABEL => if BAG_IN e edges then edges else BAG_INSERT e edges
    | FINITE_EDGES => BAG_INSERT e edges
    | UNC_EDGES => BAG_INSERT e edges
End

Theorem edge0_preserves_dirhypcst:
  (m ≠ n ∨ itself2bool slp) ∧ dirhypcst (:directedG) hyp slp eb ⇒
  dirhypcst (:directedG) hyp slp (edge0 m n lab ecst eb)
Proof
  rw[dirhypcst_def, edge0_def] >>
  Cases_on ‘itself2_ecv ecst’ >> gvs[ITSELF_UNIQUE]
QED

Theorem edge0_preserves_edge_cst:
  edge_cst ecst ebag ⇒
  edge_cst ecst (edge0 m n lab ecst ebag)
Proof
  rw[edge_cst_def, edge0_def] >> gvs[] >>
  Cases_on ‘itself2_ecv ecst’ >> gvs[] >>~-
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

Theorem IN_edge0:
  BAG_IN e (edge0 m n lab ecst ebag) ⇒ e = DE {m} {n} lab ∨ BAG_IN e ebag
Proof
  rw[edge0_def] >> Cases_on ‘itself2_ecv ecst’ >> gvs[]
QED

Definition addEdge0_def:
  addEdge0 m n (lab:'el) (G : ('ne,directedG,'ec,'el,'h,'nf,'nl,'sl) graphrep) =
  if m = n ∧ ¬itself2bool (:'sl) then G
  else
    G with <|
        nodes := G.nodes ∪ {m;n} ;
        edges := edge0 m n lab (:'ec) G.edges
    |>
End
Theorem addEdge_respects:
  ((=) ===> (=) ===> (=) ===> ceq ===> ceq) addEdge0 addEdge0
Proof
  simp[ceq_def, FUN_REL_def] >>
  simp[addEdge0_def, ITSELF_UNIQUE, finite_cst_UNION] >>
  rw[wfgraph_def, finite_cst_UNION] >>~-
  ([‘core_incident _ ⊆ _ ∪ _’],
   drule IN_edge0 >> simp[DISJ_IMP_THM] >> ASM_SET_TAC[]) >>
  gvs[ITSELF_UNIQUE] >~
  [‘edge_cst _ (edge0 _ _ _ _ _ )’]
  >- (irule edge0_preserves_edge_cst >> simp[]) >>
  irule edge0_preserves_dirhypcst >> metis_tac[]
QED
val (ae1,ae2) = liftdef addEdge_respects "addEdge"

Definition selfloops_ok_def[simp]:
  selfloops_ok (G : (α,'d,'ec,'el,'h,'nf,'nl,'sl) graph) = itself2bool (:'sl)
End

Theorem selfloop_edges_E:
  ∀m l G. directed m m l ∈ edges G ⇒ selfloops_ok G
Proof
  simp[selfloops_ok_def, edges_def] >> xfer_back_tac [] >>
  gvs[wfgraph_def, ITSELF_UNIQUE, dirhypcst_def, COND_EXPAND_OR]>>
  rw[] >> first_x_assum drule >> simp[]
QED

Definition oneEdge_max_def:
  oneEdge_max (G: (α,'d,'ec,'el,'h, 'nf,'nl,'sl) graph) ⇔
  itself2_ecv (:'ec) = ONE_EDGE
End

Theorem oneEdge_max_graph[simp]:
  oneEdge_max (g : ('a,'d,oneedgeG,'el,'h,'nf,'nl,'sl) graph)
Proof
  simp[oneEdge_max_def]
QED

Definition oneEdge_perlabel_def:
  oneEdge_perlabel (G: (α,'d,'ec,'el,'h,'nf,'nl,'sl) graph) ⇔
    itself2_ecv (:'ec) = ONE_EDGE_PERLABEL
End

Theorem oneEdge_max_fdirgraph[simp]:
  ¬oneEdge_max (g : (α,β,γ)fdirgraph)
Proof
  simp[oneEdge_max_def, itself2set_def]
QED

Theorem selfloops_ok_graph[simp]:
  selfloops_ok (g1 : ('a,'d,'ec,'el,'h,'nf,'nl,unit) graph) ∧
  selfloops_ok (g2 : ('a,'d,'ec,'el,'h,'nf,'nl,SL_OK) graph)
Proof
  simp[selfloops_ok_def]
QED

Theorem wrong_edgetype[simp]:
  ¬(BAG_IN (DE a b l)
           (edgebag (G:('a,undirectedG,'ec, 'el, 'h, 'nf, 'nl, 'sl) graph))) ∧
  (edgebag G (DE a b l) = 0) ∧
  ¬(BAG_IN (UDE ns l)
           (edgebag (H:('a,directedG,'ec, 'el, 'h, 'nf, 'nl, 'sl) graph))) ∧
  (edgebag H (UDE ns l) = 0)
Proof
  xfer_back_tac [] >> rw[wfgraph_def, dirhypcst_def] >>
  rpt strip_tac >>
  gvs[COND_EXPAND_OR, ITSELF_UNIQUE, BAG_IN, BAG_INN,
      DECIDE “x ≥ 1 ⇔ x ≠ 0”] >> CCONTR_TAC >>
  first_x_assum drule >> simp[]
QED

Theorem edgebag_addEdge:
  ∀m n l G.
    edgebag (addEdge m n l (G:('a,directedG,'ec,'ef,'h,'nf,'nl,'sl)graph)) =
    if m = n ∧ ¬selfloops_ok G then edgebag G
    else edge0 m n l (:'ec) (edgebag G)
Proof
  simp[selfloops_ok_def] >> xfer_back_tac[] >>
  rw[addEdge0_def]
QED

Theorem adjacent_REFL_E:
  ∀G m. adjacent G m m ⇒ selfloops_ok G
Proof
  simp[adjacent_def, selfloops_ok_def] >> xfer_back_tac[] >>
  rw[wfgraph_def, dirhypcst_def] >>
  gvs[ITSELF_UNIQUE, enodesEQ] >>
  first_x_assum drule >> simp[] >> ASM_SET_TAC[]
QED

Theorem edges_addEdge:
  ∀m n lab G.
  edges (addEdge m n lab (G:('a,directedG,'ecst,'el,'h, 'nf,'nl,'sl)graph)) =
    (edges G DIFF
     (if adjacent G m n ∧ oneEdge_max G then
        { directed {m} {n} l | l | directed {m} {n} l ∈ edges G }
      else {})) ∪
    (if m ≠ n ∨ selfloops_ok G then {directed {m} {n} lab} else {})
Proof
  rw[edges_def, edgebag_addEdge] >> gvs[oneEdge_max_def]
  >- (drule_then strip_assume_tac adjacent_REFL_E >> gvs[])
  >- (simp[EXTENSION, edge0_def] >> qx_gen_tac ‘e’ >> Cases_on ‘e’ >> simp[] >>
      iff_tac >> rw[] >> simp[] >> rw[])
  >- (simp[EXTENSION, edge0_def] >>
      qx_gen_tac ‘e’ >>
      Cases_on ‘itself2_ecv (:'ecst)’ >> gvs[] >> rw[] >>
      iff_tac >> rw[] >> simp[] >>
      gvs[adjacent_def, DISJ_EQ_IMP] >> first_x_assum drule >> simp[] >>
      Cases_on ‘e’ >> rw[] >> gvs[])
QED

Theorem directed_oneEdge_max:
  oneEdge_max (G : ('a,directedG,'ecst,'el,'h,'nf, 'nl, 'sl) graph) ∧
  directed a b l1 ∈ edges G ∧ directed a b l2 ∈ edges G ⇒ l1 = l2
Proof
  simp[oneEdge_max_def, edges_def] >>
  map_every qid_spec_tac [‘G’, ‘a’, ‘b’, ‘l1’, ‘l2’] >>
  xfer_back_tac[] >>
  gvs[wfgraph_def, edge_cst_def, ITSELF_UNIQUE, only_one_edge_def] >> rw[] >>
  gvs[] >>
  first_x_assum (dxrule_then drule o cj 2)>> simp[]
QED

Theorem adjacent_addEdge[simp]:
  adjacent (addEdge m n lab G) a b ⇔
    (m ≠ n ∨ selfloops_ok G) ∧ m = a ∧ n = b ∨ adjacent G a b
Proof
  simp[adjacent_directed, edges_addEdge] >> rw[EQ_IMP_THM] >> gvs[] >>
  metis_tac[directed_oneEdge_max, selfloop_edges_E, selfloops_ok_def,
            IN_INSERT]
QED
(*
val _ = show_assums := true
val rdb = global_ruledb()
val cleftp = false
val cfg = {force_imp = false, cleftp = cleftp,
           hints = [ ]  :string list}
val base = transfer_skeleton rdb cfg (#2 (top_goal()))
val th = base


fun fpow f n x = if n <= 0 then x else fpow f (n - 1) (f x)

fun F th = seq.hd $ resolve_relhyps [] cleftp rdb th

    fpow F 4 base
*)
Theorem addUDEdge_COMM:
  addUDEdge m n lab G = addUDEdge n m lab G
Proof
  Cases_on ‘m = n’ >> simp[] >>
  time (xfer_back_tac []) >> simp[addUDEdge0_def, INSERT_COMM]
QED

Theorem nodes_addUDEdge[simp]:
  ∀m n lab G.
    nodes (addUDEdge m n lab G) =
    (if m ≠ n ∨ selfloops_ok G then {m; n} else ∅) ∪ nodes G
Proof
  simp[] >> xfer_back_tac[] >> simp[addUDEdge0_def] >> rw[] >> gvs[]
QED

Theorem udedges_addUDEdge:
  udedges (addUDEdge m n lab G) =
  if m ≠ n ∨ selfloops_ok G then
    if oneEdge_max G then
      {undirected {m;n} lab} ∪ { ude | ude ∈ udedges G ∧ udenodes ude ≠ {m;n} }
    else
      {undirected {m;n} lab} ∪ udedges G
  else udedges G
Proof
  simp[udedges_def, oneEdge_max_def] >>
  map_every qid_spec_tac [‘m’, ‘n’, ‘G’, ‘lab’] >>
  xfer_back_tac[] >> simp[addUDEdge0_def] >> rw[] >> rw[] >> gvs[]
  >- (simp[udfilter_insertedge_def, Once EXTENSION] >> metis_tac[]) >>
  rename [‘itself2_ecv x’] >> Cases_on ‘itself2_ecv x’ >> gvs[] >>
  simp[udfilter_insertedge_def] >> simp[Once EXTENSION] >> rw[] >>
  metis_tac[]
QED

Theorem adjacent_addUDEdge[simp]:
  adjacent (addUDEdge m n lab G : ('a,'b,'c,'d,'e,'f)udgraph) a b ⇔
    (m ≠ n ∨ selfloops_ok G) ∧ {a;b} = {m;n} ∨ adjacent G a b
Proof
  simp[adjacent_undirected, udedges_addUDEdge] >> rw[] >>
  dsimp[INSERT2_lemma] >> metis_tac[]
QED

Theorem nodes_addEdge[simp]:
  nodes (addEdge m n lab g) =
  nodes g ∪ (if selfloops_ok g ∨ m ≠ n then {m;n} else {})
Proof
  simp[selfloops_ok_def] >> xfer_back_tac [] >>
  rw[addEdge0_def] >> gvs[]
QED

Theorem nlabelfun_addEdge[simp]:
  nlabelfun (addEdge m n l g) = nlabelfun g
Proof
  xfer_back_tac [] >> rw[addEdge0_def]
QED

(* adding undirected self-edge from n to n in a no-selfloop graph is an
   identity operation *)
Theorem addUDEdge_addNode[simp]:
  addUDEdge n n lab (G:(α,'ec,'el,'nf,'nl,noSL) udgraph) = G
Proof
  xfer_back_tac [] >> rw[addUDEdge0_def]
QED

(* "similarly" for addEdge: *)
Theorem addEdge_addNode[simp]:
  addEdge n n lab (G : (α,directedG,'ec,'el,'h, 'nf,'nl,noSL)graph) = G
Proof
  xfer_back_tac [] >> rw[addEdge0_def]
QED

Theorem gengraph_component_equality:
  g1 = g2 ⇔ nodes g1 = nodes g2 ∧ edgebag g1 = edgebag g2 ∧
            nlabelfun g1 = nlabelfun g2
Proof
  xfer_back_tac [] >>
  simp[theorem "graphrep_component_equality", ITSELF_UNIQUE]
QED

Theorem addEdge_LCOMM_fdirg:
  addEdge m n l1 (addEdge p q l2 (G:('n,'el,'nl)fdirgraph)) =
  addEdge p q l2 (addEdge m n l1 G)
Proof
  simp[gengraph_component_equality, edgebag_addEdge] >> conj_tac
  >- SET_TAC [] >>
  simp[edge0_def, BAG_INSERT_commutes]
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

Theorem oneEdge_max_BAG_INN_edgebag[simp]:
  oneEdge_max g ⇒
  (BAG_INN e c (edgebag g) ⇔ c = 0 ∨ BAG_IN e (edgebag g) ∧ c = 1)
Proof
  simp[EQ_IMP_THM, DISJ_IMP_THM, oneEdge_max_def] >> xfer_back_tac [] >>
  gvs[ITSELF_UNIQUE, wfgraph_def, edge_cst_def, COND_EXPAND_OR,
      only_one_edge_def, BAG_INN, BAG_IN] >> rw[] >>
  Cases_on ‘c = 0’ >> gvs[] >>
  rename [‘g.edges e ≥ c’] >>
  ‘g.edges e ≥ 1’ by simp[] >>
  ‘g.edges e = 1’ by simp[] >> simp[]
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
  BAG_IN (DE m n l1)(edgebag (g1:('a1,'d,'ec1,'el1,'h1,'nf1,'nl1,'sl1) graph)) ⇒
  BAG_IN (UDE ns l2)(edgebag (g2:('a2,'d,'ec2,'el2,'h2,'nf2,'nl2,'sl2) graph)) ⇒
  F
Proof
  xfer_back_tac [] >> rw[] >>
  gvs[wfgraph_def, edge_cst_def, dirhypcst_def, ITSELF_UNIQUE, optelim,
      COND_EXPAND_OR] >>
  rpt strip_tac >> res_tac >> gvs[]
QED

Definition is_hypergraph_def:
  is_hypergraph (g:(α,'d,'ecst,'el,'h,'nf,'nl,'sl) graph) ⇔
  itself2bool(:'h)
End

Theorem nonhypergraph_edges:
  ¬is_hypergraph g ∧ BAG_IN e (edgebag g) ⇒
  (∃m n l. e = UDE {m;n} l) ∨ ∃m n l. e = DE {m} {n} l
Proof
  simp[is_hypergraph_def] >> xfer_back_tac [] >>
  rw[wfgraph_def, edge_cst_def, dirhypcst_def, ITSELF_UNIQUE] >>
  first_x_assum drule >> dsimp[PULL_EXISTS, INSERT2_lemma]
QED

Theorem ulabgraph_component_equality:
  ¬is_hypergraph g1 ⇒
  (g1 : (α,δ,'h,ν,σ) ulabgraph = g2 ⇔
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
      gvs[PULL_EXISTS] >>
      first_x_assum drule >> simp[DISJ_IMP_THM, PULL_EXISTS] >>
      drule_at_then Any (simp o single) diffedge_types_impossible >>
      rpt strip_tac >>
      qpat_assum ‘BAG_IN (DE _ _ _) (edgebag _)’
                 (mp_then Any (drule_all_then strip_assume_tac)
                          nonhypergraph_edges) >> gvs[]) >>
  simp[FUN_EQ_THM, EQ_IMP_THM]
QED

Definition nrelabel0_def:
  nrelabel0 n l grep = if n ∈ grep.nodes then
                         grep with nlab := grep.nlab⦇ n ↦ l ⦈
                       else grep
End

Theorem nrelabel_respect:
  ((=) ===> (=) ===> ceq ===> ceq) nrelabel0 nrelabel0
Proof
  simp[FUN_REL_def, ceq_def] >>
  simp[wfgraph_def, nrelabel0_def] >> rw[] >>
  simp[combinTheory.APPLY_UPDATE_THM, AllCaseEqs()] >> strip_tac >> gvs[]
QED
val (nrl1,nrl2) = liftdef nrelabel_respect "nrelabel"

Theorem nodes_nrelabel[simp]:
  nodes (nrelabel n l G) = nodes G
Proof
  xfer_back_tac [] >> rw[nrelabel0_def]
QED

Theorem edgebag_nrelabel[simp]:
  edgebag (nrelabel n l G) = edgebag G
Proof
  xfer_back_tac [] >> rw[nrelabel0_def]
QED

Theorem nlabelfun_nrelabel[simp]:
  n ∈ nodes G ⇒
  nlabelfun (nrelabel n l G) = (nlabelfun G) ⦇ n ↦ l ⦈
Proof
  xfer_back_tac[] >> rw[nrelabel0_def] >>
  simp[theorem "graphrep_component_equality"]
QED

Theorem nrelabel_id[simp]:
  nrelabel n l (G:(α,'d,'ecs,'el,'h,'nf,unit,'sl) graph) = G
Proof
  simp[gengraph_component_equality] >>
  simp[FUN_EQ_THM]
QED

Theorem adjacent_nrelabel[simp]:
  adjacent (nrelabel n l G) = adjacent G
Proof
  simp[adjacent_def, FUN_EQ_THM]
QED

Theorem edges_nrelabel[simp]:
  edges (nrelabel n l G) = edges G
Proof
  simp[edges_def]
QED

Theorem udedges_nrelabel[simp]:
  udedges (nrelabel n l G) = udedges G
Proof
  simp[udedges_def]
QED

Theorem addNode_idem:
  n ∈ nodes G ⇒ addNode n l G = nrelabel n l G
Proof
  simp[gengraph_component_equality, ABSORPTION_RWT]
QED

Theorem core_incident_NOT_EMPTY[simp]:
  BAG_IN e (edgebag g) ⇒ core_incident e ≠ {}
Proof
  xfer_back_tac[] >> rw[wfgraph_def] >>
  gvs[edge_cst_def, dirhypcst_def, optelim, COND_EXPAND_OR, ITSELF_UNIQUE] >>
  first_x_assum drule >> rpt strip_tac >> gvs[] >>
  Cases_on ‘e’ >> gvs[]
QED

Theorem core_incident_SUBSET_nodes:
  BAG_IN e (edgebag g) ⇒ core_incident e ⊆ nodes g
Proof
  xfer_back_tac []>> gvs[wfgraph_def]
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
  drule core_incident_SUBSET_nodes >> gvs[core_incident_def, enodesEQ] >>
  ASM_SET_TAC[]
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
    edges := BAG_OF_SET {DE {INL m} {INL n} () | R m n};
    hyperp := (:unhyperG);
    nlab := K ();
    nfincst := (:INF_OK);
    dircst := (:directedG) ;
    slcst := (:SL_OK) ; (* self-loops allowed *)
    edgecst := (:oneedgeG)
  |>
End

Theorem univR_graph_respect:
  (((=) ===> (=) ===> (=)) ===> ceq) univR_graph0 univR_graph0
Proof
  simp[FUN_REL_def, ceq_def] >> simp[GSYM FUN_EQ_THM, SF ETA_ss] >>
  simp[wfgraph_def, univR_graph0_def, itself2set_def, finite_cst_def,
       dirhypcst_def, edge_cst_def, PULL_EXISTS, INSERT2_lemma, SF CONJ_ss,
       SF DNF_ss] >>
  simp[itself2_ecv_def, itself2_4_def, only_one_edge_def, PULL_EXISTS,
       BAG_OF_SET]
QED
val (urg1,urg2) = liftdef univR_graph_respect "univR_graph"

Definition restrR_graph0_def:
  restrR_graph0 R = <|
                     nodes := { INL a | ∃b. R a b ∨ R b a };
                     edges := BAG_OF_SET {DE {INL a} {INL b} () | R a b};
                     hyperp := (:unhyperG);
                     nlab := K ();
                     nfincst := (:INF_OK);
                     dircst := (:directedG) ;
                     slcst := (:SL_OK) ; (* self-loops allowed *)
                     edgecst := (:oneedgeG)
                   |>
End
Theorem restrR_graph_respect:
  (((=) ===> (=) ===> (=)) ===> ceq) restrR_graph0 restrR_graph0
Proof
  simp[FUN_REL_def, ceq_def] >> simp[GSYM FUN_EQ_THM, SF ETA_ss] >>
  simp[wfgraph_def, restrR_graph0_def, itself2set_def, finite_cst_def,
       edge_cst_def, PULL_EXISTS, INSERT2_lemma, SF CONJ_ss, SF DNF_ss,
       dirhypcst_def] >>
  conj_tac >- metis_tac[] >>
  simp[itself2_ecv_def, itself2_4_def, only_one_edge_def, PULL_EXISTS,
       BAG_OF_SET]
QED
val (rrg1,rrg2) = liftdef restrR_graph_respect "restrR_graph"

Theorem nodes_univR_graph[simp]:
  nodes (univR_graph R) = IMAGE INL UNIV
Proof
  xfer_back_tac [] >>
  simp[univR_graph0_def, EXTENSION]
QED

Theorem edges_univR_graph[simp]:
  edges (univR_graph R) = { directed {INL x} {INL y} () | R x y }
Proof
  simp[edges_def] >> xfer_back_tac [] >>
  simp[univR_graph0_def, Once EXTENSION]
QED

Theorem adjacent_univR_graph[simp]:
  adjacent (univR_graph R) a b = ∃a0 b0. a = INL a0 ∧ b = INL b0 ∧ R a0 b0
Proof
  simp[adjacent_directed, PULL_EXISTS, AC CONJ_ASSOC CONJ_COMM]
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
  xfer_back_tac [] >>
  simp[restrR_graph0_def, EXTENSION] >> metis_tac[]
QED

Theorem edges_restrR_graph[simp]:
  edges (restrR_graph R) = { directed {INL x} {INL y} () | R x y }
Proof
  simp[edges_def] >> xfer_back_tac [] >>
  simp[restrR_graph0_def, EXTENSION]
QED

Theorem adjacent_restrR_graph[simp]:
  adjacent (restrR_graph R) a b = ∃a0 b0. a = INL a0 ∧ b = INL b0 ∧ R a0 b0
Proof
  simp[adjacent_directed, PULL_EXISTS, AC CONJ_COMM CONJ_ASSOC]
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
  adjacent (g1 : α relgraph) = adjacent (g2: α relgraph) ⇔
  edges g1 = edges g2
Proof
  simp[SimpLHS, FUN_EQ_THM] >>
  simp[adjacent_directed, FORALL_PROD, enodesEQ, SF CONJ_ss,
       SF DNF_ss] >>
  simp[Once EQ_IMP_THM] >>
  simp[edges_def] >> strip_tac >>
  simp[EXTENSION, EQ_IMP_THM] >>
  gvs[EQ_IMP_THM, PULL_EXISTS, FORALL_AND_THM] >>
  rpt strip_tac >>
  drule_at Any nonhypergraph_edges >> simp[is_hypergraph_def] >>
  rw[] >> first_x_assum drule >> simp[] >> rpt strip_tac >>
  drule_at Any nonhypergraph_edges >>
  simp[is_hypergraph_def] >> rw[] >> gvs[]
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
  simp[univnodes_def, adjacent_undirected, udedges_def] >>
  xfer_back_tac[] >> rpt strip_tac >>
  qexists ‘<| nodes := IMAGE INL UNIV;
              edges := BAG_OF_SET { UDE {INL x; INL y} () | R x y };
              nlab := K ();
              hyperp := (:unhyperG);
              nfincst := (:INF_OK);
              dircst := (:undirectedG) ;
              slcst := (:SL_OK) ; (* self-loops allowed *)
              edgecst := (:oneedgeG);
           |>’ >>
  simp[] >> conj_tac
  >- (simp[wfgraph_def, ITSELF_UNIQUE, itself2set_def, finite_cst_def] >>
      simp[PULL_EXISTS] >>
      dsimp[edge_cst_def, SF CONJ_ss, PULL_EXISTS, INSERT2_lemma,
            itself2_4_def, itself2_ecv_def, dirhypcst_def] >>
      simp[only_one_edge_def, PULL_EXISTS, BAG_OF_SET, AllCaseEqs()]) >>
  simp[INSERT2_lemma] >> metis_tac[]
QED

(* ----------------------------------------------------------------------
    graph measurements
   ---------------------------------------------------------------------- *)

Definition gsize_def:
  gsize (g : (α,δ,'ec,'ei,'h,finiteG,'nl,σ)graph) = CARD $ nodes g
End

Overload order = “gsize”

Theorem FINITE_nodes[simp]:
  FINITE (nodes (G:('a,'dir,'ec,'el,'h,finiteG,'nl,'sl)graph))
Proof
  xfer_back_tac [] >> simp[wfgraph_def, ITSELF_UNIQUE, finite_cst_def]
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
  FINITE $ edges (g : (α,directedG,'h,finiteG,σ)ulabgraph)
Proof
  irule SUBSET_FINITE >>
  qexists ‘IMAGE (λ(m,n). directed m n ()) (POW (nodes g) × POW (nodes g))’ >>
  simp[] >>
  simp[SUBSET_DEF, FORALL_PROD, EXISTS_PROD] >> Cases >> simp[IN_POW] >>
  rpt strip_tac >> rw[SUBSET_DEF] >> irule incident_SUBSET_nodes >>
  first_assum $ irule_at Any >> simp[]
QED

Theorem IN_udedges_E:
  undirected f l ∈ udedges g ⇒ ∃m n. f = {m;n}
Proof
  simp[udedges_def] >> strip_tac >> drule_at Any nonhypergraph_edges >>
  simp[is_hypergraph_def]
QED

Theorem FINITE_udedges_UL:
  FINITE $ udedges (g:(α,undirectedG,'ef,unit,unhyperG,finiteG,'nl,'sl)graph)
Proof
  irule SUBSET_FINITE >>
  qexists ‘IMAGE (λ(m,n). undirected {m; n} ()) (nodes g × nodes g)’ >> simp[]>>
  simp[SUBSET_DEF, FORALL_PROD, EXISTS_PROD] >> Cases >> simp[] >>
  strip_tac >> drule IN_udedges_E >> simp[PULL_EXISTS] >> rw[] >>
  irule_at Any EQ_REFL >> drule incident_udedges_SUBSET_nodes >> simp[]
QED

Theorem FINITE_udedges_onemax:
  oneEdge_max g ⇒
  FINITE $ udedges (g:(α,undirectedG,'ef,'el,unhyperG,finiteG,'nl,'sl)graph)
Proof
  strip_tac >>
  ‘INJ udenodes (udedges g) (POW (nodes g))’
    by (simp[INJ_IFF] >> conj_tac
        >- (rw[udedges_def] >> drule core_incident_SUBSET_nodes >>
            simp[IN_POW]) >>
        drule_then assume_tac oneEdge_max_BAG_INN_edgebag  >>
        simp[udedges_def, EQ_IMP_THM] >> Cases >> Cases >> simp[] >>
        gvs[oneEdge_max_def] >>
        xfer_back_tac[] >> rw[wfgraph_def] >>
        gvs[edge_cst_def, ITSELF_UNIQUE, only_one_edge_def] >>
        first_x_assum (dxrule_then drule o cj 2) >> simp[]) >>
  drule_at_then Any irule FINITE_INJ >> simp[]
QED

Definition edgesize_def:
  edgesize (g : (α,directedG,unhyperG,finiteG,σ) ulabgraph) = CARD $ edges g
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
  addEdges0 eset0 (g: (α,directedG,'ec,'ei,'h,ν,'nl,σ) graphrep) =
  let
      slokp = itself2bool (:σ) ;
      eset1 = { directed m n l | directed m n l ∈ eset0 ∧ m ≠ ∅ ∧ n ≠ ∅ ∧
                                 (itself2bool (:'h) ∨ SING m ∧ SING n) } ;
      deset = if slokp then eset1 else { e | e ∈ eset1 ∧ ¬selfloop e } ;
      eset = IMAGE cDE deset ;
      ns = { n | ∃e. e ∈ deset ∧ n ∈ incidentDE e } ;
  in
    if itself2bool(:ν) ∧ INFINITE ns then g
    else
      case itself2_ecv (:'ec) of
        ONE_EDGE =>
          let edges_to_add =
              { directed m n l | directed m n l ∈ deset ∧
                                 ∀l'. directed m n l' ∈ deset ⇒ l' = l }
          in
            g with <| edges :=
                        BAG_OF_SET
                        (IMAGE cDE edges_to_add ∪
                         (SET_OF_BAG g.edges DIFF
                          { cDE e | ∃f. f ∈ deset ∧ denodes e = denodes f}));
                      nodes := g.nodes ∪ ns |>
      | ONE_EDGE_PERLABEL =>
          g with <| edges := BAG_OF_SET (eset ∪ SET_OF_BAG g.edges);
                    nodes := g.nodes ∪ ns |>
      | FINITE_EDGES =>
          g with <|
            edges :=
              BAG_UNION g.edges
                  (BAG_OF_SET {
                      DE m n l |
                      DE m n l ∈ eset ∧
                      FINITE {de | de ∈ deset ∧ incidentDE de = m ∪ n}});
            nodes := g.nodes ∪ ns
          |>
      | UNC_EDGES =>
          g with <| edges := BAG_UNION g.edges (BAG_OF_SET eset);
                    nodes := g.nodes ∪ ns |>
End

Theorem addEdges_respects:
  ((=) ===> ceq ===> ceq) addEdges0 addEdges0
Proof
  simp[FUN_REL_def, ceq_def] >>
  REWRITE_TAC[addEdges0_def] >> BasicProvers.LET_ELIM_TAC >>
  COND_CASES_TAC >> simp[] >>
  rename [‘itself2bool nfincst ∧ INFINITE ns’, ‘g.edges’] >>
  ‘finite_cst (univ nfincst) (g.nodes ∪ ns)’
    by gs[itself2bool_def, finite_cst_def, wfgraph_def, ITSELF_UNIQUE] >>
  ‘¬slokp ⇒ ∀e. e ∈ deset ⇒ ¬selfloop e’ by simp[Abbr‘deset’] >>
  ‘∀e. e ∈ set g.edges ⇒ core_incident e ⊆ g.nodes ∪ ns’
    by (gs[wfgraph_def] >> metis_tac[SUBSET_TRANS, SUBSET_UNION]) >>
  ‘∀e. e ∈ eset ⇒ core_incident e ⊆ g.nodes ∪ ns’
    by (simp[Abbr‘eset’, Abbr‘ns’, FORALL_PROD, Abbr‘deset’] >> rw[] >>
        simp[SUBSET_DEF] >>
        metis_tac[]) >>
  rename [‘itself2_ecv ecst’] >>
  qpat_x_assum ‘wfgraph g’ mp_tac >> simp[wfgraph_def] >>
  rpt strip_tac >> Cases_on ‘itself2_ecv ecst’ >> gvs[ITSELF_UNIQUE] >>~-
  ([‘e ∈ edges_to_add’, ‘incident e ⊆ g.nodes ∪ nds’],
   qpat_x_assum ‘e ∈ edges_to_add’ mp_tac >>
   simp[Abbr‘edges_to_add’, PULL_EXISTS] >>
   rpt gen_tac >> strip_tac >>
   rename [‘directed ms ns lab ∈ deset’, ‘g.nodes ∪ nds’] >>
   ‘DE ms ns lab ∈ eset’ by simp[Abbr‘eset’] >>
   first_assum (pop_assum o mp_then Any mp_tac) >> simp[]) >>~-
  ([‘ONE_EDGE’, ‘edge_cst _ (BAG_OF_SET _)’],
   qpat_x_assum ‘edge_cst _ _’ mp_tac >>
   simp[edge_cst_def, DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS] >>
   simp[only_one_edge_def] >> rw[] >> simp[BAG_OF_SET] >~
   [‘e1 ∈ edges_to_add’, ‘e2 ∈ edges_to_add’, ‘e1 = e2’]
   >- (rpt (qpat_x_assum ‘_ ∈ edges_to_add’ mp_tac) >>
       simp[Abbr‘edges_to_add’] >> map_every Cases_on [‘e1’, ‘e2’] >> simp[] >>
       gvs[]) >~
   [‘ce = cDE de’, ‘enodes ce = enodes (cDE de)’]
   >- (map_every Cases_on [‘ce’, ‘de’] >> gvs[] >>
       gvs[Abbr‘edges_to_add’]) >~
   [‘cDE de = ce’, ‘enodes (cDE de) = enodes ce’]
   >- (map_every Cases_on [‘ce’, ‘de’] >> gvs[] >>
       gvs[Abbr‘edges_to_add’])) >>~-
  ([‘ONE_EDGE_PERLABEL’, ‘edge_cst _ (BAG_OF_SET _)’],
   qpat_x_assum ‘edge_cst _ _’ mp_tac >>
   simp[edge_cst_def, only_one_edge_per_label_def] >>
   simp[BAG_OF_SET]) >>~-
  ([‘FINITE_EDGES’,  ‘edge_cst _ (BAG_UNION _ _)’],
   qpat_x_assum ‘edge_cst _ _’ mp_tac >>
   simp[edge_cst_def, finite_edges_per_nodeset_def] >>
   dsimp[GSPEC_OR] >>
   simp[Abbr‘eset’, SF CONJ_ss] >> rw[] >> simp[SF CONJ_ss] >>
   qabbrev_tac ‘ACs = {de | de ∈ deset ∧ incident de = A}’ >>
   Cases_on ‘FINITE ACs’ >> simp[] >> irule SUBSET_FINITE >>
   qexists ‘IMAGE cDE ACs’ >> simp[IMAGE_FINITE] >>
   simp[SUBSET_DEF, PULL_EXISTS] >> simp[Abbr‘ACs’]) >>~-
  ([‘UNC_EDGES’, ‘edge_cst _ (BAG_UNION _ _)’],
   qpat_x_assum ‘edge_cst _ _’ mp_tac >>
   simp[edge_cst_def]) >>~-
  ([‘_ ⊆ g.nodes ∪ _ ∧ _ ⊆ g.nodes ∪ _’],
   first_assum (qpat_x_assum ‘_ ∈ eset’ o mp_then Any mp_tac) >>
   simp[]) >>
  qpat_x_assum ‘dirhypcst _ _ _ _ ’ mp_tac >>
  simp[dirhypcst_def] >> rw[] >>~-
  ([‘BAG_IN e g.edges’], first_x_assum irule >> simp[]) >>
  TRY (qunabbrev_tac ‘edges_to_add’) >>
  gvs[Abbr‘deset’, Abbr‘eset1’, SING_DEF, Abbr‘eset’]
QED
val (aes1,aes2) = liftdef addEdges_respects "addEdges"

Definition validEdge_def:
  (validEdge hyp slp (cDE de) ⇔
     case de of
       directed m n l =>
         m ≠ ∅ ∧ n ≠ ∅ ∧ (¬slp ⇒ DISJOINT m n) ∧
         (¬hyp ⇒ SING m ∧ SING n)) ∧
  (validEdge hyp slp (cUDE ude) ⇔
     case ude of
       undirected ns l =>
         ns ≠ ∅ ∧ (¬slp ∧ FINITE ns ⇒ 2 ≤ CARD ns) ∧
         (¬hyp ⇒ ∃m n. ns = {m;n}))
End


Theorem nodes_addEdges_allokgraph:
  nodes (addEdges es0 g : (α,β,γ) allokdirgraph) =
  nodes g ∪ BIGUNION (IMAGE incident (es0 ∩ { e | validEdge T T (cDE e)}))
Proof
  xfer_back_tac[] >>
  simp[addEdges0_def] >>
  simp[Once EXTENSION, PULL_EXISTS, EXISTS_PROD] >> rpt strip_tac >>
  iff_tac >> rw[] >> simp[] >>~-
  ([‘directed ms ns l ∈ es0’], disj2_tac >> first_assum $ irule_at Any>>
                               simp[validEdge_def]) >>
  gvs[validEdge_def] >> rename [‘e ∈ es0’, ‘n ∈ incident e’] >>
  Cases_on ‘e’ >> gvs[] >> disj2_tac >>
  first_assum $ irule_at (Pat ‘directed _ _ _ ∈ es0’) >>
  simp[]
QED

Theorem nodes_addEdges_fdirg:
  FINITE es ⇒
  nodes (addEdges es g : (α,β,γ) fdirgraph) =
  nodes g ∪ BIGUNION (IMAGE incident (es ∩ {e | validEdge F T (cDE e)}))
Proof
  xfer_back_tac [] >> simp[addEdges0_def] >> rw[] >> rw[] >~
  [‘INFINITE _’]
  >- (‘F’ suffices_by simp[] >> qpat_x_assum ‘INFINITE _’ mp_tac >> simp[] >>
      irule SUBSET_FINITE >>
      qexists ‘BIGUNION (IMAGE incident (es ∩ {e | validEdge F T (cDE e)}))’ >>
      simp[PULL_EXISTS, validEdge_def] >> rpt conj_tac
      >- (Cases >> simp[SING_DEF, PULL_EXISTS]) >>
      simp[SUBSET_DEF, PULL_EXISTS] >> rw[SING_DEF] >> gvs[] >>
      first_assum $ irule_at Any >> simp[]) >>
  simp[Once EXTENSION, validEdge_def, PULL_EXISTS] >>
  rw[EQ_IMP_THM] >> simp[] >> disj2_tac >> gvs[SING_DEF] >>~-
  ([‘directed {m} {n} l ∈ es’], first_assum $ irule_at Any >> simp[]) >>
  rename [‘n ∈ incident e’] >> Cases_on ‘e’ >> gvs[] >>
  first_assum $ irule_at Any >> simp[]
QED

Theorem nodes_addEdges_f1edgedir:
  FINITE es ⇒
  nodes (addEdges es g :
           (α,directedG,oneedgeG,'el,unhyperG,finiteG,'nl,'sl)graph) =
  nodes g ∪
  BIGUNION
    (IMAGE incident (es ∩ { e | validEdge F (itself2bool(:'sl)) (cDE e)}))
Proof
  xfer_back_tac [] >> simp[addEdges0_def] >> rw[] >> rw[] >~
  [‘INFINITE _’]
  >- (‘F’ suffices_by simp[] >> qpat_x_assum ‘INFINITE _’ mp_tac >> simp[] >>
      irule SUBSET_FINITE >>
      qexists ‘BIGUNION
               (IMAGE incident
                      (es ∩ {e | validEdge F (itself2bool(:'sl)) (cDE e)}))’ >>
      simp[PULL_EXISTS, validEdge_def] >> rpt conj_tac
      >- (Cases >> simp[SING_DEF, PULL_EXISTS]) >>
      simp[SUBSET_DEF, PULL_EXISTS] >> rw[SING_DEF] >> gvs[] >>
      first_assum $ irule_at Any >> simp[]) >>
  gvs[] >>
  dsimp[Once EXTENSION, SING_DEF, PULL_EXISTS, validEdge_def] >>
  qx_gen_tac ‘n’ >> Cases_on ‘n ∈ g.nodes’ >> simp[]>> iff_tac >> rw[] >>~-
  ([‘_ ∨ _’, ‘de ∈ es’, ‘n ∈ incident de’],
   Cases_on ‘de’ >> gvs[] >> metis_tac[]) >>
  first_assum $ irule_at Any >> simp[]
QED

Theorem edges_addEdges_f1edgedir:
  FINITE es ⇒
  edges (addEdges es g :
           (α,directedG,oneedgeG,'el,unhyperG,finiteG,'nl,'sl)graph) =
  (es ∩ { e | validEdge F (itself2bool(:'sl)) (cDE e) ∧
              ∀f. f ∈ es ∧ denodes f = denodes e ⇒ f = e}) ∪
  (edges g DIFF { e | ∃e0. e0 ∈ es ∧ denodes e0 = denodes e })
Proof
  simp[edges_def] >> xfer_back_tac [] >> simp[addEdges0_def] >> rw[] >> rw[] >~
  [‘INFINITE _’]
  >- (‘F’ suffices_by simp[] >> qpat_x_assum ‘INFINITE _’ mp_tac >> simp[] >>
      irule SUBSET_FINITE >>
      qexists ‘BIGUNION
               (IMAGE incident
                      (es ∩ {e | validEdge F (itself2bool(:'sl)) (cDE e)}))’ >>
      simp[PULL_EXISTS, validEdge_def] >> rpt conj_tac
      >- (Cases >> simp[SING_DEF, PULL_EXISTS]) >>
      simp[SUBSET_DEF, PULL_EXISTS] >> rw[SING_DEF] >> gvs[] >>
      first_assum $ irule_at Any >> simp[]) >>
  dsimp[Once EXTENSION, SING_DEF, PULL_EXISTS, validEdge_def] >>
  qx_gen_tac ‘de1’ >> simp[] >>
  (Cases_on ‘BAG_IN (cDE de1) g.edges’ >> simp[]
   >- (Cases_on ‘de1’ >> simp[] >>
       gvs[wfgraph_def, dirhypcst_def, ITSELF_UNIQUE] >>
       first_x_assum $ drule_then strip_assume_tac >> gvs[] >>
       rename [‘directed {m} {n} lab ∈ es’] >>
       Cases_on ‘directed {m} {n} lab ∈ es’ >> simp[FORALL_DIREDGE]) >>
   Cases_on ‘de1’ >> csimp[PULL_EXISTS, FORALL_DIREDGE] >> metis_tac[])
QED

Theorem nlabelfun_addEdges[simp]:
  nlabelfun (addEdges es g) = nlabelfun g
Proof
  xfer_back_tac [] >> simp[addEdges0_def] >> rw[] >>
  rename [‘itself2_ecv x’]>> Cases_on ‘itself2_ecv x’ >> rw[ITSELF_UNIQUE]
QED

Theorem addEdges_EMPTY[simp]:
  addEdges ∅ g = g
Proof
  xfer_back_tac [] >> simp[addEdges0_def] >>
  rw[wfgraph_def]>>
  rename [‘itself2_ecv x’]>> Cases_on ‘itself2_ecv x’ >> rw[ITSELF_UNIQUE] >>
  gvs[ITSELF_UNIQUE, theorem "graphrep_component_equality"] >>
  qpat_x_assum ‘edge_cst _ _ ’ mp_tac >>
  simp[edge_cst_def, only_one_edge_per_label_def, only_one_edge_def,
       FUN_EQ_THM, BAG_OF_SET] >>
  simp[AllCaseEqs(), BAG_IN, BAG_INN] >> rw[] >>
  rename [‘g.edges e = 1’] >> Cases_on ‘g.edges e = 0’ >> simp[]
QED

Theorem addEdges_SING[simp]:
  addEdges {directed {m} {n} l} g =
  addEdge m n l (g: (α,directedG,'ec,'el,'h,ν,'nl,σ) graph)
Proof
  xfer_back_tac[] >> simp[addEdges0_def, addEdge0_def] >>
  rename [‘itself2_ecv ecst’] >> Cases_on ‘itself2_ecv ecst’ >> rw[] >>
  gvs[] >> simp[GSPEC_OR, INSERT_UNION_EQ] >>~-
  ([‘INFINITE _’],
   ‘F’ suffices_by simp[] >> qpat_x_assum ‘INFINITE _’ mp_tac >> simp[] >>
   simp[SF CONJ_ss] >> irule SUBSET_FINITE >> qexists ‘{m;n}’ >>
   simp[SUBSET_DEF, PULL_EXISTS] >> rw[] >> gvs[]) >>
  simp[theorem "graphrep_component_equality"] >>~-
  ([‘BAG_OF_SET _ = edge0 _ _ _ _ _’],
   simp[edge0_def, FUN_EQ_THM, BAG_OF_SET, BAG_INSERT, BAG_FILTER_DEF,
        PULL_EXISTS] >>
   simp[AllCaseEqs()] >> Cases >> rw[BAG_IN, BAG_INN] >>~-
   ([‘g.edges (UDE ns l)’],
    ‘g.edges (UDE ns l) = 0’ suffices_by simp[] >>
    gvs[wfgraph_def, dirhypcst_def, ITSELF_UNIQUE] >>
    gvs[COND_EXPAND_OR, BAG_IN, BAG_INN] >>
    CCONTR_TAC >> ‘g.edges (UDE ns l) >= 1’ by simp[] >>
    first_x_assum drule >> simp[]) >>
   simp[SF CONJ_ss, arithmeticTheory.GREATER_EQ] >>~-
   ([‘ONE_EDGE’],
    rename [‘m' = {m} ∧ n' = {n} ∧ lab' = lab’] >>
    map_every Cases_on [‘m' = {m}’, ‘n' = {n}’] >>
    simp[arithmeticTheory.GREATER_EQ] >> csimp[] >>
    gvs[wfgraph_def, ITSELF_UNIQUE, edge_cst_def, only_one_edge_def] >>
    gvs[BAG_IN, BAG_INN] >> qmatch_abbrev_tac ‘g.edges e = 1 ∨ _’ >>
    first_x_assum $ qspec_then ‘e’ (mp_tac o cj 1) >> simp[]) >>~-
   ([‘ONE_EDGE_PERLABEL’],
    rename [‘DE {m} {n} lab’, ‘m' = {m}’, ‘n' = {n}’, ‘lab' = lab’] >>
    map_every Cases_on [‘m' = {m}’, ‘n' = {n}’, ‘lab' = lab’] >>
    simp[arithmeticTheory.GREATER_EQ] >>
    gvs[wfgraph_def, ITSELF_UNIQUE, edge_cst_def, only_one_edge_per_label_def]>>
    gvs[BAG_IN, BAG_INN] >> csimp[] >>
    qmatch_abbrev_tac ‘g.edges e = 1 ∨ _’ >>
    first_x_assum $ qspec_then ‘e’ (mp_tac o cj 1) >> simp[])) >~
  [‘BAG_OF_SET _ = g.edges’, ‘ONE_EDGE’]
  >- (simp[FUN_EQ_THM, BAG_OF_SET] >>
      gvs[wfgraph_def, edge_cst_def, ITSELF_UNIQUE, only_one_edge_def, BAG_IN,
          BAG_INN] >>
      qx_gen_tac ‘e’ >> first_x_assum $ qspec_then ‘e’ (mp_tac o cj 1) >>
      simp[]) >~
  [‘BAG_OF_SET _ = g.edges’, ‘ONE_EDGE_PERLABEL’]
  >- (simp[FUN_EQ_THM, BAG_OF_SET] >>
      gvs[wfgraph_def, edge_cst_def, ITSELF_UNIQUE,
          only_one_edge_per_label_def, BAG_IN, BAG_INN] >>
      qx_gen_tac ‘e’ >> first_x_assum $ qspec_then ‘e’ (mp_tac o cj 1) >>
      simp[]) >>~-
  ([‘BAG_UNION _ _ = _ ’],
   csimp[edge0_def, Once FUN_EQ_THM, BAG_UNION, BAG_INSERT, BAG_OF_SET] >>
   rw[])
QED

Theorem edges_addEdges_allokdirgraph:
  edges (addEdges es (g : (α,β,γ)allokdirgraph)) =
  (es ∩ { e | validEdge T T (cDE e)}) ∪ edges g
Proof
  simp[edges_def] >> xfer_back_tac [] >>
  simp[addEdges0_def, validEdge_def] >>
  simp[Once EXTENSION] >> rpt strip_tac >> rename [‘BAG_IN (cDE e) _’] >>
  Cases_on ‘e’ >> simp[AC DISJ_ASSOC DISJ_COMM, AC CONJ_ASSOC CONJ_COMM]
QED

Theorem edgebag_addEdges_fdirgraph:
  FINITE es ⇒
  edgebag (addEdges es (g : (α,β,γ) fdirgraph)) =
  BAG_OF_SET (IMAGE cDE (es ∩ {e | validEdge F T (cDE e)})) ⊎ edgebag g
Proof
  xfer_back_tac [] >>
  simp[validEdge_def, addEdges0_def] >> rpt strip_tac >> rw[] >~
  [‘INFINITE _’]
  >- (‘F’ suffices_by simp[] >> qpat_x_assum ‘INFINITE _’ mp_tac >> simp[] >>
      irule SUBSET_FINITE >>
      qexists
        ‘BIGUNION (IMAGE incident { e | e ∈ es ∧ validEdge F T (cDE e)})’ >>
      simp[PULL_EXISTS, validEdge_def] >> rpt strip_tac >~
      [‘FINITE (incident e)’]
      >- (Cases_on ‘e’ >> gvs[SING_DEF]) >~
      [‘FINITE (IMAGE incident _)’]
      >- (irule IMAGE_FINITE >> simp[GSPEC_AND]) >>
      simp[SUBSET_DEF, PULL_EXISTS] >> rpt strip_tac >>
      first_assum $ irule_at Any >> simp[]) >>
  simp[Once FUN_EQ_THM, BAG_OF_SET, BAG_UNION] >>
  Cases >> simp[] >> rw[] >> gvs[] >>
  qpat_x_assum ‘INFINITE _’ mp_tac >> simp[] >>
  irule SUBSET_FINITE >> qexists ‘es’ >> simp[SUBSET_DEF, PULL_EXISTS]
QED

Theorem edges_addEdges_fdirgraph:
  FINITE es ⇒
  edges (addEdges es (g : (α,β,γ) fdirgraph)) =
  (es ∩ {e | validEdge F T (cDE e)}) ∪ edges g
Proof
  simp[edges_def, edgebag_addEdges_fdirgraph, GSPEC_OR] >> SET_TAC[]
QED

Theorem addEdges_INSERT_fdirG:
  ∀es m n l g.
    FINITE es ⇒
    addEdges (directed {m} {n} l INSERT es) (g:(α,β,γ)fdirgraph) =
    addEdge m n l (addEdges (es DELETE directed {m} {n} l) g)
Proof
  simp[gengraph_component_equality, edgebag_addEdges_fdirgraph,
       edgebag_addEdge, nodes_addEdges_fdirg] >>
  rpt strip_tac >~
  [‘nodes g ∪ _ = nodes g ∪ _ ∪ _’]
  >- (dsimp[Once EXTENSION, PULL_EXISTS] >> gen_tac >> iff_tac >> rw[] >>
      simp[]
      >- (rename [‘e ∈ es’, ‘n ∈ incident e’] >>
          Cases_on ‘e’ >> gvs[validEdge_def, SING_DEF, PULL_EXISTS]
          >- (Cases_on ‘m = n’ >> simp[] >> disj1_tac >> disj2_tac >>
              first_assum $ irule_at Any >> simp[]) >>
          rename [‘directed {m1} {n1} _ ∈ es’, ‘_ ≠ directed {m2} {n2} _’] >>
          Cases_on ‘n1 = n2’ >> simp[] >> disj1_tac >> disj2_tac >>
          first_assum $ irule_at Any >> simp[])
      >- metis_tac[] >>
      simp[validEdge_def]) >>
  simp[Once FUN_EQ_THM, BAG_OF_SET, BAG_UNION, edge0_def, BAG_INSERT] >>
  Cases >> simp[] >> rw[] >> gvs[validEdge_def]
QED

Theorem addEdges_INSERT_invalidEdge_fdirgraph:
  FINITE es ∧ ¬validEdge F T (cDE e) ⇒
  addEdges (e INSERT es) (g:(α,β,γ)fdirgraph) = addEdges es g
Proof
  simp[gengraph_component_equality] >>
  simp[nodes_addEdges_fdirg, edgebag_addEdges_fdirgraph, INSERT_INTER]
QED

Theorem addEdges_addEdges_fdirG:
  ∀es1 es2.
    FINITE es1 ∧ FINITE es2 ∧ DISJOINT es1 es2 ⇒
    addEdges es1 (addEdges es2 (G:(α,β,γ)fdirgraph)) =
    addEdges (es1 ∪ es2) G
Proof
  Induct_on ‘FINITE’ >> simp[INSERT_UNION_EQ] >> rpt strip_tac >>
  rename [‘e INSERT (es1 ∪ es2)’] >>
  Cases_on ‘validEdge F T (cDE e)’ >>
  simp[addEdges_INSERT_invalidEdge_fdirgraph] >>
  gvs[validEdge_def, SING_DEF] >> Cases_on ‘e’ >> gvs[] >>
  simp[addEdges_INSERT_fdirG, DELETE_NON_ELEMENT_RWT]
QED

Definition removeNode0_def:
  removeNode0 n grep =
  grep with <| nodes := grep.nodes DELETE n ;
               edges := BAG_FILTER { e | n ∉ core_incident e } grep.edges ;
               nlab := grep.nlab ⦇ n ↦ ARB ⦈ |>
End

Theorem removeNode_respect:
  ((=) ===> ceq ===> ceq) removeNode0 removeNode0
Proof
  simp[FUN_REL_def, ceq_def] >>
  simp[wfgraph_def, removeNode0_def, ITSELF_UNIQUE, DISJ_IMP_THM,
       FORALL_AND_THM, combinTheory.APPLY_UPDATE_THM] >>
  rw[SUBSET_DEF, finite_cst_def] >> rpt strip_tac >> gs[] >~
  [‘edge_cst _ (BAG_FILTER _ _)’]
  >- (gs[edge_cst_def] >> rw[] >> gs[SF CONJ_ss] >>
      rename [‘itself2_ecv ecst’] >> Cases_on ‘itself2_ecv ecst’ >>
      gvs[] >>
      gvs[only_one_edge_def, BAG_FILTER_DEF, only_one_edge_per_label_def,
          BAG_IN, BAG_INN, finite_edges_per_nodeset_def] >>
      qx_gen_tac ‘A’ >> first_x_assum $ qspec_then ‘A’ mp_tac >>
      qmatch_abbrev_tac ‘FINITE es1 ⇒ FINITE es2’ >>
      strip_tac >> irule SUBSET_FINITE >> qexists ‘es1’ >> simp[] >>
      simp[Abbr‘es1’, Abbr‘es2’, SUBSET_DEF] >> rw[]) >~
  [‘dirhypcst _ _ _ (BAG_FILTER _ _)’]
  >- (qpat_x_assum ‘dirhypcst _ _ _ _ ’ mp_tac >> simp[dirhypcst_def] >>
      rw[]) >>
  metis_tac[]
QED
val (rn1,rn2) = liftdef removeNode_respect "removeNode"

Theorem nodes_removeNode[simp]:
  nodes (removeNode n g) = nodes g DELETE n
Proof
  xfer_back_tac [] >> simp[removeNode0_def]
QED

Theorem gsize_removeNode[simp]:
  n ∈ nodes g ⇒ gsize (removeNode n g) = gsize g - 1
Proof
  simp[gsize_def]
QED

Theorem edgebag_removeNode[simp]:
  edgebag (removeNode n g) = BAG_FILTER {e | n ∉ core_incident e} (edgebag g)
Proof
  xfer_back_tac [] >> simp[removeNode0_def]
QED

Theorem edges_removeNode[simp]:
  edges (removeNode n g) = edges g DIFF { e | n ∈ incident e}
Proof
  simp[edges_def, Once EXTENSION, AC CONJ_ASSOC CONJ_COMM]
QED

Theorem nlabelfun_removeNode[simp]:
  nlabelfun (removeNode n g) = (nlabelfun g)⦇ n ↦ ARB ⦈
Proof
  xfer_back_tac [] >> simp[removeNode0_def]
QED

Theorem removeNode_addNode[simp]:
  n ∉ nodes g ⇒ removeNode n (addNode n l g) = g
Proof
  simp[gengraph_component_equality] >>
  simp[EXTENSION, SF CONJ_ss] >> rpt strip_tac
  >- metis_tac[] >>
  simp[BAG_FILTER_DEF, FUN_EQ_THM] >> rw[] >>
  drule_at Concl (SRULE[SUBSET_DEF] core_incident_SUBSET_nodes) >>
  disch_then $ drule_at Any >> simp[BAG_IN, BAG_INN]
QED

Theorem removeNode_NONMEMBER:
  n ∉ nodes g ⇒ (removeNode n g = g)
Proof
  simp[gengraph_component_equality, DELETE_NON_ELEMENT_RWT] >>
  rw[FUN_EQ_THM, BAG_FILTER_DEF] >> rw[] >>
  drule_at Concl (SRULE[SUBSET_DEF] core_incident_SUBSET_nodes) >>
  disch_then $ drule_at Any >> simp[BAG_IN, BAG_INN]
QED

Theorem removeNode_LCOMM:
  removeNode m (removeNode n g) = removeNode n (removeNode m g)
Proof
  simp[gengraph_component_equality, DELETE_COMM, DIFF_COMM] >>
  simp[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >> rw[] >>
  simp[BAG_FILTER_DEF] >> rw[]
QED

Definition removeNodes_def:
  removeNodes G N = ITSET removeNode N G
End

Definition removeEdge0_def:
  removeEdge0 e grep = grep with edges := BAG_DIFF grep.edges {|e|}
End

Theorem removeEdge_respect:
  ((=) ===> ceq ===> ceq) removeEdge0 removeEdge0
Proof
  simp[FUN_REL_def, ceq_def, wfgraph_def, removeEdge0_def] >>
  rw[] >~
  [‘BAG_IN e (_ - _)’]
  >- (drule BAG_IN_DIFF_E >> simp[]) >~
  [‘edge_cst _ (_ - _)’]
  >- (qpat_x_assum ‘edge_cst _ _’ mp_tac >> simp[edge_cst_def] >>
      rename [‘itself2_ecv ecst’] >> Cases_on ‘itself2_ecv ecst’ >>
      simp[only_one_edge_per_label_def, only_one_edge_def,
           finite_edges_per_nodeset_def, BAG_IN, BAG_INN, BAG_DIFF,
           DECIDE “1 - x = 1 ⇔ x = 0”, BAG_INSERT, EMPTY_BAG, AllCaseEqs()] >>
      strip_tac >> gen_tac >> rw[] >>~-
      ([‘¬(g.edges e ≥ 2)’],
       first_x_assum $ qspec_then ‘e’ (mp_tac o cj 1) >> simp[]) >~
      [‘enodes f = enodes e’]
      >- (first_x_assum (irule o cj 2) >> qpat_x_assum ‘a.edges f ≥ _’ mp_tac >>
          rw[]) >>
      rename [‘core_incident _ = A’] >>
      first_x_assum $ qspec_then ‘A’ assume_tac >>
      irule SUBSET_FINITE >> first_assum $ irule_at Any >>
      simp[SUBSET_DEF] >> rw[]) >>
  qpat_x_assum ‘dirhypcst _ _ _ _’ mp_tac >>
  rw[dirhypcst_def] >> drule BAG_IN_DIFF_E >> metis_tac[]
QED
val (re1,re2) = liftdef removeEdge_respect "removeEdge"

Theorem nodes_removeEdge[simp]:
  nodes (removeEdge e g) = nodes g
Proof
  xfer_back_tac [] >> rw[removeEdge0_def]
QED

Theorem edgebag_removeEdge[simp]:
  edgebag (removeEdge e g) = edgebag g - {|e|}
Proof
  xfer_back_tac [] >> rw[removeEdge0_def]
QED

Theorem diredges_removeEdge[simp]:
  oneEdge_max g ⇒
  edges (removeEdge (cDE e) g) = edges g DELETE e
Proof
  simp[edges_def, EXTENSION, oneEdge_max_def] >> xfer_back_tac [] >>
  simp[wfgraph_def, edge_cst_def, ITSELF_UNIQUE] >> rw[] >>
  gvs[only_one_edge_def] >>
  rename [‘BAG_IN (cDE x) (_ - _) ’] >>
  first_x_assum $ qspec_then ‘cDE x’ (mp_tac o cj 1) >>
  simp[BAG_IN, BAG_INN, BAG_DIFF, BAG_INSERT, EMPTY_BAG] >> rw[]
QED

Theorem nlabelfun_removeEdge[simp]:
  nlabelfun (removeEdge e g) = nlabelfun g
Proof
  xfer_back_tac [] >> simp[removeEdge0_def]
QED

Definition isolated_def:
  isolated g ns ⇔
    ns ⊆ nodes g ∧
    ∀e. BAG_IN e (edgebag g) ∧ ¬DISJOINT (core_incident e) ns ⇒
        core_incident e ⊆ ns
End

Theorem BAG_FILTER_EQ:
  BAG_FILTER P b = b ⇔ ∀e. BAG_IN e b ⇒ P e
Proof
  simp[BAG_FILTER_DEF, BAG_IN, BAG_INN, FUN_EQ_THM, AllCaseEqs()] >>
  metis_tac[DECIDE “x = 0 ⇔ ¬(x ≥ 1)”]
QED

Theorem DEs_non_empty:
  BAG_IN (DE m n l) (edgebag g) ⇒ m ≠ ∅ ∧ n ≠ ∅
Proof
  xfer_back_tac [] >> simp[wfgraph_def, dirhypcst_def] >> rw[] >>
  first_x_assum drule >> simp[PULL_EXISTS]
QED

Theorem isolated_addNode_removeNode:
  ¬selfloops_ok g ⇒
  (isolated g {n} ⇔ addNode n (nlabelfun g n) (removeNode n g) = g)
Proof
  strip_tac >>
  drule_at Concl adjacent_REFL_E >>
  rw[isolated_def, gengraph_component_equality, EQ_IMP_THM, BAG_FILTER_EQ] >~
  [‘n ∉ core_incident e’]
  >- (strip_tac >> first_x_assum $ drule_all_then assume_tac >>
      ‘core_incident e = {n}’ by ASM_SET_TAC[] >> gvs[] >>
      first_x_assum $ qspec_then ‘n’ mp_tac >> simp[adjacent_def] >>
      qexists ‘e’ >> Cases_on ‘e’ >> gvs[] >> drule DEs_non_empty >>
      ASM_SET_TAC[])
  >- ASM_SET_TAC[]
  >- metis_tac[]
QED

Theorem FINITE_edges_fdir[simp]:
  FINITE (edges (g : (α,β,γ) fdirgraph))
Proof
  simp[edges_def] >> xfer_back_tac [] >>
  simp[wfgraph_def, ITSELF_UNIQUE, finite_cst_def, edge_cst_def,
       finite_edges_per_nodeset_def] >>
  rpt strip_tac >>
  irule SUBSET_FINITE >>
  qexists
    ‘BIGUNION (IMAGE (λA. { e | BAG_IN (cDE e) g.edges ∧
                                incident e = A })
                     (POW g.nodes))’ >>
  simp[SUBSET_DEF, PULL_EXISTS] >> simp[IN_POW] >> rpt strip_tac >~
  [‘incident e ⊆ g.nodes’]
  >- (first_x_assum drule >> simp[]) >>
  qspec_then ‘cDE’ (irule o iffLR) INJECTIVE_IMAGE_FINITE >>
  conj_tac >- simp[] >> irule SUBSET_FINITE >>
  rename [‘A ⊆ g.nodes’] >>
  first_x_assum $ qspec_then ‘A’ assume_tac >> first_assum $ irule_at Any >>
  simp[SUBSET_DEF, PULL_EXISTS]
QED

Theorem FINITE_edges_f1edgedir[simp]:
  FINITE (edges (g:(α,directedG,oneedgeG,'el,'h,finiteG,'nl,'sl)graph))
Proof
  simp[edges_def] >> xfer_back_tac [] >>
  simp[wfgraph_def, ITSELF_UNIQUE, finite_cst_def, edge_cst_def,
       only_one_edge_def, itself2_ecv_def, itself2_4_def] >> rw[] >>
  irule SUBSET_FINITE >>
  qexists
    ‘BIGUNION (IMAGE (λ(A,B). { e | BAG_IN (cDE e) g.edges ∧
                                    denodes e = (A,B) })
                     (POW g.nodes × POW g.nodes))’ >>
  simp[PULL_EXISTS, SUBSET_DEF] >>
  simp[IN_POW, EXISTS_PROD, FORALL_PROD] >> rpt strip_tac >~
  [‘_ ⊆ g.nodes ∧ _ ⊆ g.nodes’, ‘BAG_IN (cDE de) g.edges’]
  >- (‘core_incident (cDE de) ⊆ g.nodes’ by simp[] >>
      Cases_on ‘de’ >> fs[]) >>
  qmatch_abbrev_tac ‘FINITE B’ >> Cases_on ‘B = ∅’ >> simp[] >>
  ‘∃e. B = {e}’ suffices_by simp[PULL_EXISTS] >>
  simp[Abbr‘B’, Once EXTENSION] >> gvs[GSYM MEMBER_NOT_EMPTY] >>
  rename [‘BAG_IN (cDE e) g.edges’] >> qexists ‘e’>> simp[EQ_IMP_THM] >>
  qx_gen_tac ‘f’ >> strip_tac >>
  first_x_assum $ qspec_then ‘cDE f’ (mp_tac o cj 2) >>
  simp[PULL_EXISTS] >> disch_then $ qspec_then ‘cDE e’ mp_tac >> simp[]
QED

Theorem edgebag_1edge:
  edgebag (g : (α,directedG,oneedgeG,'el,'h,'nf,'nl,'sl)graph) =
  BAG_OF_SET {cDE e | e ∈ edges g}
Proof
  simp[edges_def] >> xfer_back_tac [] >>
  simp[FUN_EQ_THM] >>
  simp[BAG_OF_SET,wfgraph_def,ITSELF_UNIQUE, dirhypcst_def, edge_cst_def,
       BAG_IN, BAG_INN, only_one_edge_def] >> gen_tac >> strip_tac >>
  Cases >> simp[] >> gvs[DECIDE “x ≥ 1 ⇔ x ≠ 0n”]
  >- metis_tac[] >>
  CCONTR_TAC >> gvs[COND_EXPAND_OR] >> first_x_assum drule >> simp[]
QED

Theorem edgebag_1udedge:
  edgebag (g : (α, undirectedG,oneedgeG,'el,unhyperG,'nf,'nl,'sl)graph) =
  BAG_OF_SET {cUDE ud | ud ∈ udedges g}
Proof
  simp[udedges_def] >> xfer_back_tac [] >> simp[FUN_EQ_THM] >>
  simp[BAG_OF_SET,wfgraph_def,ITSELF_UNIQUE, dirhypcst_def, edge_cst_def,
       BAG_IN, BAG_INN, only_one_edge_def] >> gen_tac >> strip_tac >>
  Cases >> simp[] >> gvs[DECIDE “x ≥ 1 ⇔ x ≠ 0n”]
  >- (CCONTR_TAC >> gvs[COND_EXPAND_OR] >> first_x_assum drule >> simp[]) >>
  metis_tac[]
QED

Theorem IN_edges_valid:
  de ∈ edges (g : (α,directedG,'ec,'el,'h,'nf,'nl,'sl) graph) ⇒
  validEdge (itself2bool (:'h)) (itself2bool(:'sl)) (cDE de)
Proof
  simp[edges_def, validEdge_def] >> xfer_back_tac [] >>
  simp[FORALL_DIREDGE, wfgraph_def, ITSELF_UNIQUE] >>
  simp[dirhypcst_def] >> rw[] >> first_x_assum drule >> simp[PULL_EXISTS]
QED

Theorem decomposition_f1edgedir:
  ∀g. g = emptyG ∨
      ∃n l es g0 : (α,directedG,oneedgeG,'el,unhyperG,finiteG,'nl,'sl) graph.
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
  simp[gengraph_component_equality, nodes_addEdges_f1edgedir,
       edgebag_addEdges_fdirgraph] >> conj_tac
  >- (simp[Once EXTENSION, PULL_EXISTS, Abbr‘es’, validEdge_def] >>
      metis_tac[incident_SUBSET_nodes]) >>
  simp[edgebag_1edge] >> simp[edges_addEdges_f1edgedir] >>
  simp[validEdge_def, Once EXTENSION] >> Cases >> simp[] >>
  rename [‘directed ms ns lab ∈ edges g’] >>
  Cases_on ‘directed ms ns lab ∈ edges g’ >> simp[]
  >- (drule IN_edges_valid >>
      simp[validEdge_def, SING_DEF, PULL_EXISTS, FORALL_DIREDGE] >> rw[] >>
      simp[Abbr‘es’] >> gvs[] >>
      rename [‘directed {m} {p} lab ∈ edges g’, ‘n = m ∨ n = p’] >>
      Cases_on ‘n = m’ >> gvs[]
      >- (‘oneEdge_max g’ by simp[] >> metis_tac[directed_oneEdge_max]) >>
      Cases_on ‘n = p’ >> gvs[] >>
      ‘oneEdge_max g’ by simp[] >> metis_tac[directed_oneEdge_max]) >>
  Cases_on ‘ms = ∅’ >> simp[] >> Cases_on ‘ns = ∅’ >> simp[] >>
  Cases_on ‘SING ms’ >> simp[] >>
  Cases_on ‘SING ns’ >> simp[] >> gvs[SING_DEF] >>
  rename [‘directed {m} {p} lab ∈ es’] >>
  Cases_on ‘directed {m} {p} lab ∈ es’ >> simp[] >>
  gvs[Abbr‘es’]
QED

Theorem f1edgedirG_induction:
  ∀P. P emptyG ∧
      (∀n l es g0. n ∉ nodes g0 ∧ FINITE es ∧
                   (∀e. e ∈ es ⇒ n ∈ incident e) ∧
                   (∀e m. e ∈ es ∧ m ∈ incident e ⇒ m = n ∨ m ∈ nodes g0) ∧
                   P g0 ⇒ P (addEdges es (addNode n l g0))) ⇒
      ∀g : (α,directedG,oneedgeG,'el,unhyperG,finiteG,'nl,'sl) graph. P g
Proof
  rpt strip_tac >>
  Induct_on ‘gsize g’ >> rw[] >>
  ‘g ≠ emptyG’ by (strip_tac >> gs[]) >>
  qspec_then ‘g’ strip_assume_tac decomposition_f1edgedir >> gs[] >>
  last_x_assum irule >> simp[] >> metis_tac[]
QED

val fdirtyq = ty_antiq “:('n,'el,'nl) fdirgraph”

Theorem fdirgraph_decomposition:
  ∀g:^fdirtyq.
    g = emptyG ∨
    (∃g0 n nl. g = addNode n nl g0 ∧ n ∉ nodes g0) ∨
    ∃g0 m n l. m ∈ nodes g0 ∧ n ∈ nodes g0 ∧ g = addEdge m n l g0
Proof
  gen_tac >> Cases_on ‘g = emptyG’ >> simp[] >>
  Cases_on ‘edgebag g = EMPTY_BAG’
  >- (‘nodes g ≠ ∅’ by simp[] >>
      gvs[GSYM MEMBER_NOT_EMPTY] >> rename [‘n ∈ nodes g’] >>
      disj1_tac >>
      qexistsl [‘removeNode n g’, ‘n’, ‘nlabelfun g n’] >> simp[] >>
      simp[gengraph_component_equality]) >>
  ‘∃e eb0. edgebag g = BAG_INSERT e eb0’ by metis_tac[BAG_cases] >>
  ‘BAG_IN e (edgebag g)’ by simp[] >>
  Cases_on ‘e’ >> fs[] >> rename [‘BAG_INSERT (DE m n l) eb0’] >>
  drule_at (Pos last) nonhypergraph_edges >> simp[is_hypergraph_def] >>
  strip_tac >> fs[] >> rename [‘DE {src} {tgt} lab’] >>
  ntac 2 (pop_assum SUBST_ALL_TAC) >>
  drule core_incident_SUBSET_nodes >> simp[] >> strip_tac >>
  disj2_tac >>
  qexistsl [‘removeEdge (DE {src} {tgt} lab) g’, ‘src’, ‘tgt’, ‘lab’] >>
  simp[] >>
  simp[gengraph_component_equality, edgebag_addEdge, edge0_def] >>
  ASM_SET_TAC[]
QED

Theorem FINITE_edgebag_fdirg[simp]:
  FINITE_BAG (edgebag (g:^fdirtyq))
Proof
  xfer_back_tac[] >>
  simp[wfgraph_def, ITSELF_UNIQUE, edge_cst_def, finite_edges_per_nodeset_def,
       finite_cst_def] >> rpt strip_tac >>
  REWRITE_TAC[GSYM FINITE_SET_OF_BAG] >> irule SUBSET_FINITE >>
  qexists ‘BIGUNION
           (IMAGE (λ(src,tgt).
                     { e | BAG_IN e g.edges ∧ core_incident e = {src;tgt}})
                  (g.nodes × g.nodes))’ >>
  simp[FORALL_PROD, PULL_EXISTS] >>
  simp[SUBSET_DEF, PULL_EXISTS, FORALL_PROD, EXISTS_PROD] >>
  Cases >> gvs[dirhypcst_def] >> strip_tac >> first_x_assum drule >>
  simp[PULL_EXISTS, INSERT_UNION_EQ] >>
  simp[INSERT2_lemma] >> rpt strip_tac >> gvs[] >> first_x_assum drule >>
  simp[SUBSET_DEF] >> metis_tac[]
QED

Theorem fdirgraph_induction:
  ∀P.
    P emptyG ∧ (∀g n nl. P g ⇒ P (addNode n nl g)) ∧
    (∀m n el g. m ∈ nodes g ∧ n ∈ nodes g ∧ P g ⇒ P (addEdge m n el g)) ⇒
    ∀g:^fdirtyq. P g
Proof
  gen_tac >> strip_tac >>
  ‘WF (inv_image ($< LEX $<) (λg:^fdirtyq. (gsize g, BAG_CARD (edgebag g))))’
    by simp[WF_LEX, relationTheory.WF_inv_image] >>
  drule_then irule relationTheory.WF_INDUCTION_THM >>
  simp[LEX_DEF, DISJ_IMP_THM, FORALL_AND_THM] >> qx_gen_tac ‘G’ >> strip_tac >>
  qspec_then ‘G’ strip_assume_tac fdirgraph_decomposition >> gvs[]
  >- (last_x_assum irule >> gvs[gsize_addNode]) >>
  gvs[edgebag_addEdge, edge0_def, BAG_CARD_THM] >>
  gvs[gsize_def] >> last_x_assum irule >> simp[] >>
  ‘nodes g0 ∪ {m;n} = nodes g0’  by ASM_SET_TAC[] >> gvs[]
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

Theorem addUDEdge_udul_LCOMM:
  addUDEdge m n l1 (addUDEdge a b l2 g : (α,ν,σ)udulgraph) =
  addUDEdge a b l2 (addUDEdge m n l1 g)
Proof
  simp[gengraph_component_equality] >> rw[]
  >- SET_TAC[]
  >- (simp[edgebag_1udedge, udedges_addUDEdge] >> rw[] >> gvs[] >>
      simp[Once EXTENSION] >> Cases >> simp[] >> metis_tac[]) >>
  simp[FUN_EQ_THM]
QED

Theorem edges_ITSET_addUDEdge_udul:
  ∀A g : (α,ν,σ) udulgraph.
    FINITE A ∧ (∀m n. (m,n) ∈ A ⇒ m ∈ nodes g ∧ n ∈ nodes g) ∧
    (¬selfloops_ok g ⇒ ∀m n. (m,n) ∈ A ⇒ m ≠ n)
    ⇒
    udedges (ITSET (λ(m,n) g. addUDEdge m n () g) A g) =
    { undirected {m;n} () | (m,n) ∈ A } ∪ udedges g
Proof
  Induct_on ‘FINITE’ >>
  simp[COMMUTING_ITSET_RECURSES, FORALL_PROD, addUDEdge_udul_LCOMM,
       DELETE_NON_ELEMENT_RWT, udedges_addUDEdge] >> rw[] >>
  gs[DISJ_IMP_THM, FORALL_AND_THM] >> rw[] >> simp[] >>
  first_x_assum $ drule_then strip_assume_tac >> simp[] >> rw[] >>
  simp[Once EXTENSION] >> Cases >> iff_tac >> rw[] >>
  metis_tac[]
QED

Theorem BAG_ALL_DISTINCT_edgebag:
  BAG_ALL_DISTINCT (edgebag (g:(α,β,oneedgeG,'el,'h,'nf,'nl,'sl)graph)) ∧
  BAG_ALL_DISTINCT (edgebag (h:(α,β,oneedgeplG,'el,'h,'nf,'nl,'sl)graph))
Proof
  simp[BAG_ALL_DISTINCT] >> xfer_back_tac [] >>
  simp[wfgraph_def, edge_cst_def, ITSELF_UNIQUE, only_one_edge_def,
       only_one_edge_per_label_def, BAG_IN, BAG_INN, DECIDE “x ≥ 1 ⇔ x ≠ 0”,
       DECIDE “x ≠ 0 ⇒ x = 1 ⇔ x ≤ 1”, IMP_CONJ_THM, FORALL_AND_THM
      ]
QED

Theorem udedges_removeEdge:
  udedges (removeEdge e
              (g:(α,undirectedG,oneedgeG,'el,unhyperG,'nf,'nl,'sl)graph))=
  case e of
    cDE d => udedges g
  | cUDE ude => udedges g DELETE ude
Proof
  simp[udedges_def] >> Cases_on ‘e’ >> simp[] >>
  simp[Once EXTENSION] >>
  simp[BAG_IN_BAG_DIFF_ALL_DISTINCT, BAG_ALL_DISTINCT_edgebag]
QED

Theorem removeEdge_LCOMM:
  removeEdge e1 (removeEdge e2 g) = removeEdge e2 (removeEdge e1 g)
Proof
  simp[gengraph_component_equality] >>
  simp[Once FUN_EQ_THM, BAG_DIFF]
QED

val _ = export_theory();
val _ = html_theory "genericGraph";
