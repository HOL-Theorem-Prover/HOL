(*===========================================================================*)
(* Topologies and metric spaces, including metric on real line               *)
(*===========================================================================*)

structure topologyScript =
struct

(*
app load ["hol88Lib",
          "numLib",
          "PairedLambda",
          "jrhUtils",
          "realTheory"];
*)

open HolKernel Parse boolLib
     hol88Lib pairLib jrhUtils realTheory;

infix THEN THENL ORELSE ORELSEC ##;


val _ = new_theory "topology";


(*---------------------------------------------------------------------------*)
(* Minimal amount of set notation is convenient                              *)
(*---------------------------------------------------------------------------*)

val re_Union = new_definition("re_Union",
  (--`re_Union P = \x:'a. ?s. P s /\ s x`--));

val re_union = new_infixl_definition("re_union",
  (--`$re_union P Q = \x:'a. P x \/ Q x`--), 500);

val re_intersect = new_infixl_definition("re_intersect",
  (--`$re_intersect P Q = \x:'a. P x /\ Q x`--), 600);

val re_null = new_definition("re_null",
  (--`re_null = \x:'a. F`--));

val re_universe = new_definition("re_universe",
  (--`re_universe = \x:'a. T`--));

val re_subset = new_definition("re_subset",
  (--`$re_subset P Q = !x:'a. P x ==> Q x`--));
val _ = set_fixity "re_subset" (Infix(NONASSOC, 450))

val re_compl = new_definition("re_compl",
  (--`re_compl P = \x:'a. ~(P x):bool`--));

val SUBSET_REFL = prove_thm("SUBSET_REFL",
  (--`!P:'a->bool. P re_subset P`--),
  GEN_TAC THEN REWRITE_TAC[re_subset]);

val COMPL_MEM = prove_thm("COMPL_MEM",
  (--`!P:'a->bool. !x. P x = ~(re_compl P x)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[re_compl] THEN
  BETA_TAC THEN REWRITE_TAC[]);

val SUBSET_ANTISYM = prove_thm("SUBSET_ANTISYM",
  (--`!P:'a->bool. !Q. P re_subset Q /\ Q re_subset P = (P = Q)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[re_subset] THEN
  CONV_TAC(ONCE_DEPTH_CONV AND_FORALL_CONV) THEN
  REWRITE_TAC[TAUT_CONV (--`(a ==> b) /\ (b ==> a) = (a = b)`--)] THEN
  CONV_TAC(RAND_CONV FUN_EQ_CONV) THEN REFL_TAC);

val SUBSET_TRANS = prove_thm("SUBSET_TRANS",
  (--`!P:'a->bool. !Q R. P re_subset Q /\ Q re_subset R ==> P re_subset R`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[re_subset] THEN
  CONV_TAC(ONCE_DEPTH_CONV AND_FORALL_CONV) THEN
  DISCH_THEN(MATCH_ACCEPT_TAC o GEN (--`x:'a`--) o end_itlist IMP_TRANS o
    CONJUNCTS o SPEC (--`x:'a`--)));

(*---------------------------------------------------------------------------*)
(* Characterize an (alpha)topology                                           *)
(*---------------------------------------------------------------------------*)

val istopology = new_definition("istopology",
  (--`!L. istopology L =
              L re_null /\
              L re_universe /\
             (!a b. L a /\ L b ==> L (a re_intersect b)) /\
             (!P. P re_subset L ==> L (re_Union P))`--));

val topology_tydef = new_type_definition
 ("topology",
  PROVE((--`?t. istopology t`--),
        EXISTS_TAC (--`re_universe:('a->bool)->bool`--) THEN
        REWRITE_TAC[istopology, re_universe]));

val topology_tybij = define_new_type_bijections
    {name="topology_tybij",
     ABS="topology", REP="open",tyax=topology_tydef};

val TOPOLOGY = prove_thm("TOPOLOGY",
  (--`!L. open(L) re_null /\
          open(L) re_universe /\
          (!x y. open(L) x /\ open(L) y ==> open(L) (x re_intersect y)) /\
          (!P. P re_subset (open L) ==> open(L) (re_Union P))`--),
  GEN_TAC THEN REWRITE_TAC[GSYM istopology] THEN
  REWRITE_TAC[topology_tybij]);

val TOPOLOGY_UNION = prove_thm("TOPOLOGY_UNION",
  (--`!L. !P. P re_subset (open L) ==> open(L) (re_Union P)`--),
  REWRITE_TAC[TOPOLOGY]);


(*---------------------------------------------------------------------------*)
(* Characterize a neighbourhood of a point relative to a topology            *)
(*---------------------------------------------------------------------------*)

val neigh = new_definition("neigh",
  (--`neigh(top)(N,(x:'a)) = ?P. open(top) P /\ P re_subset N /\ P x`--));

(*---------------------------------------------------------------------------*)
(* Prove various properties / characterizations of open sets                 *)
(*---------------------------------------------------------------------------*)

val OPEN_OWN_NEIGH = prove_thm("OPEN_OWN_NEIGH",
  (--`!S' top. !x:'a. open(top) S' /\ S' x ==> neigh(top)(S',x)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[neigh] THEN
  EXISTS_TAC (--`S':'a->bool`--) THEN ASM_REWRITE_TAC[SUBSET_REFL]);

val OPEN_UNOPEN = prove_thm("OPEN_UNOPEN",
  (--`!S' top. open(top) S' = (re_Union (\P:'a->bool. open(top) P
                               /\ P re_subset S') = S')`--),
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM SUBSET_ANTISYM] THEN
    REWRITE_TAC[re_Union, re_subset] THEN BETA_TAC THEN CONJ_TAC THEN GEN_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN (--`s:'a->bool`--) STRIP_ASSUME_TAC) THEN
      FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC,
      DISCH_TAC THEN EXISTS_TAC (--`S':'a->bool`--) THEN ASM_REWRITE_TAC[]],
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC TOPOLOGY_UNION THEN
    REWRITE_TAC[re_subset] THEN BETA_TAC THEN
    GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]]);

val OPEN_SUBOPEN = prove_thm("OPEN_SUBOPEN",
  (--`!S' top. open(top) S' = !x:'a. S' x ==> ?P. P x /\ open(top) P /\ P re_subset S'`--),
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    EXISTS_TAC (--`S':'a->bool`--) THEN ASM_REWRITE_TAC[SUBSET_REFL],
    DISCH_TAC THEN C SUBGOAL_THEN SUBST1_TAC
     (--`S' = re_Union (\P:'a->bool. open(top) P /\ P re_subset S')`--) THENL
     [ONCE_REWRITE_TAC[GSYM SUBSET_ANTISYM] THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[re_subset] THEN REWRITE_TAC [re_Union] THEN BETA_TAC THEN
        GEN_TAC THEN DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
        DISCH_THEN(X_CHOOSE_TAC (--`P:'a->bool`--)) THEN EXISTS_TAC (--`P:'a->bool`--) THEN
        ASM_REWRITE_TAC[],
        REWRITE_TAC[re_subset, re_Union] THEN BETA_TAC THEN GEN_TAC THEN
        DISCH_THEN(CHOOSE_THEN STRIP_ASSUME_TAC) THEN
        FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC],
      MATCH_MP_TAC TOPOLOGY_UNION THEN ONCE_REWRITE_TAC[re_subset] THEN
      GEN_TAC THEN BETA_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]]]);

val OPEN_NEIGH = prove_thm("OPEN_NEIGH",
  (--`!S' top. open(top) S' = !x:'a. S' x ==> ?N. neigh(top)(N,x) /\ N re_subset S'`--),
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC (--`S':'a->bool`--) THEN
    REWRITE_TAC[SUBSET_REFL, neigh] THEN
    EXISTS_TAC (--`S':'a->bool`--) THEN ASM_REWRITE_TAC[SUBSET_REFL],
    DISCH_TAC THEN ONCE_REWRITE_TAC[OPEN_SUBOPEN] THEN
    GEN_TAC THEN DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN(X_CHOOSE_THEN (--`N:'a->bool`--) (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC))
    THEN REWRITE_TAC[neigh] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`P:'a->bool`--) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (--`P:'a->bool`--) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC (--`N:'a->bool`--) THEN
    ASM_REWRITE_TAC[]]);

(*---------------------------------------------------------------------------*)
(* Characterize closed sets in a topological space                           *)
(*---------------------------------------------------------------------------*)

val closed = new_definition("closed",
  (--`closed(L:('a)topology) S' = open(L)(re_compl S')`--));

(*---------------------------------------------------------------------------*)
(* Define limit point in topological space                                   *)
(*---------------------------------------------------------------------------*)

val limpt = new_definition("limpt",
  (--`limpt(top) x S' =
      !N:'a->bool. neigh(top)(N,x) ==> ?y. ~(x = y) /\ S' y /\ N y`--));

(*---------------------------------------------------------------------------*)
(* Prove that a set is closed iff it contains all its limit points           *)
(*---------------------------------------------------------------------------*)

val CLOSED_LIMPT = prove_thm("CLOSED_LIMPT",
  (--`!top S'. closed(top) S' = (!x:'a. limpt(top) x S' ==> S' x)`--),
  REPEAT GEN_TAC THEN CONV_TAC(ONCE_DEPTH_CONV CONTRAPOS_CONV) THEN
  REWRITE_TAC[closed, limpt] THEN
  CONV_TAC(ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
  FREEZE_THEN (fn th => ONCE_REWRITE_TAC[th]) (SPEC (--`S':'a->bool`--) COMPL_MEM) THEN
  REWRITE_TAC[] THEN
  SPEC_TAC((--`re_compl(S':'a->bool)`--),(--`S':'a->bool`--)) THEN
  GEN_TAC THEN REWRITE_TAC[NOT_IMP] THEN
  CONV_TAC(ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN
  REWRITE_TAC[OPEN_NEIGH, re_subset] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  ASM_CASES_TAC (--`(S':'a->bool) x`--) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[TAUT_CONV (--`a \/ b \/ ~c = c ==> a \/ b`--)] THEN
  EQUAL_TAC THEN
  REWRITE_TAC[TAUT_CONV (--`(a = b \/ a) = b ==> a`--)] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  POP_ASSUM ACCEPT_TAC);

(*---------------------------------------------------------------------------*)
(* Characterize an (alpha)metric                                             *)
(*---------------------------------------------------------------------------*)

val ismet = new_definition("ismet",
  (--`ismet (m:'a#'a->real)
        =
      (!x y. (m(x,y) = &0) = (x = y)) /\
      (!x y z. m(y,z) <= m(x,y) + m(x,z))`--));

val metric_tydef = new_type_definition
 ("metric",
  PROVE((--`?m:('a#'a->real). ismet m`--),
        EXISTS_TAC (--`\(x:'a,(y:'a)). if (x = y) then &0 else &1`--) THEN
        REWRITE_TAC[ismet] THEN
        CONV_TAC(ONCE_DEPTH_CONV PAIRED_BETA_CONV) THEN
        CONJ_TAC THEN REPEAT GEN_TAC THENL
         [BOOL_CASES_TAC (--`x:'a = y`--) THEN REWRITE_TAC[REAL_10],
          REPEAT COND_CASES_TAC THEN
          ASM_REWRITE_TAC[REAL_ADD_LID, REAL_ADD_RID, REAL_LE_REFL, REAL_LE_01]
          THEN GEN_REWR_TAC LAND_CONV  [GSYM REAL_ADD_LID] THEN
          TRY(MATCH_MP_TAC REAL_LE_ADD2) THEN
          REWRITE_TAC[REAL_LE_01, REAL_LE_REFL] THEN
          FIRST_ASSUM(UNDISCH_TAC o assert is_neg o concl) THEN
          EVERY_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[]]));

val metric_tybij = define_new_type_bijections
      {name="metric_tybij",
       ABS="metric", REP="dist", tyax=metric_tydef};

(*---------------------------------------------------------------------------*)
(* Derive the metric properties                                              *)
(*---------------------------------------------------------------------------*)

val METRIC_ISMET = prove_thm("METRIC_ISMET",
  (--`!m:('a)metric. ismet (dist m)`--),
  GEN_TAC THEN REWRITE_TAC[metric_tybij]);

val METRIC_ZERO = prove_thm("METRIC_ZERO",
  (--`!m:('a)metric. !x y. ((dist m)(x,y) = &0) = (x = y)`--),
  REPEAT GEN_TAC THEN ASSUME_TAC(SPEC (--`m:('a)metric`--) METRIC_ISMET) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ismet]) THEN ASM_REWRITE_TAC[]);

val METRIC_SAME = prove_thm("METRIC_SAME",
  (--`!m:('a)metric. !x. (dist m)(x,x) = &0`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[METRIC_ZERO]);

val METRIC_POS = prove_thm("METRIC_POS",
  (--`!m:('a)metric. !x y. &0 <= (dist m)(x,y)`--),
  REPEAT GEN_TAC THEN ASSUME_TAC(SPEC (--`m:('a)metric`--) METRIC_ISMET) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ismet]) THEN
  FIRST_ASSUM(MP_TAC o
             SPECL [(--`x:'a`--), (--`y:'a`--), (--`y:'a`--)] o CONJUNCT2) THEN
  REWRITE_TAC[REWRITE_RULE[]
             (SPECL [(--`m:('a)metric`--), (--`y:'a`--), (--`y:'a`--)]
                    METRIC_ZERO)]
  THEN CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[REAL_NOT_LE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_ADD2 o W CONJ) THEN
  REWRITE_TAC[REAL_ADD_LID]);

val METRIC_SYM = prove_thm("METRIC_SYM",
  (--`!m:('a)metric. !x y. (dist m)(x,y) = (dist m)(y,x)`--),
  REPEAT GEN_TAC THEN ASSUME_TAC(SPEC (--`m:('a)metric`--) METRIC_ISMET) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ismet]) THEN FIRST_ASSUM
   (MP_TAC o GENL [(--`y:'a`--), (--`z:'a`--)] o SPECL [(--`z:'a`--), (--`y:'a`--), (--`z:'a`--)] o CONJUNCT2)
  THEN REWRITE_TAC[METRIC_SAME, REAL_ADD_RID] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[GSYM REAL_LE_ANTISYM]);

val METRIC_TRIANGLE = prove_thm("METRIC_TRIANGLE",
  (--`!m:('a)metric. !x y z. (dist m)(x,z) <= (dist m)(x,y) + (dist m)(y,z)`--),
  REPEAT GEN_TAC THEN ASSUME_TAC(SPEC (--`m:('a)metric`--) METRIC_ISMET) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ismet]) THEN
  GEN_REWR_TAC (RAND_CONV o LAND_CONV)  [METRIC_SYM] THEN
  ASM_REWRITE_TAC[]);

val METRIC_NZ = prove_thm("METRIC_NZ",
  (--`!m:('a)metric. !x y. ~(x = y) ==> &0 < (dist m)(x,y)`--),
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [(--`m:('a)metric`--), (--`x:'a`--), (--`y:'a`--)] METRIC_ZERO)) THEN
  ONCE_REWRITE_TAC[TAUT_CONV (--`~a ==> b = b \/ a`--)] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN
  REWRITE_TAC[GSYM REAL_LE_LT, METRIC_POS]);

(*---------------------------------------------------------------------------*)
(* Now define metric topology and prove equivalent definition of "open"      *)
(*---------------------------------------------------------------------------*)

val mtop = new_definition("mtop",
  (--`!m:('a)metric. mtop m =
    topology(\S'. !x. S' x ==> ?e. &0 < e /\ (!y. (dist m)(x,y) < e ==> S' y))`--));

val mtop_istopology = prove_thm("mtop_istopology",
  (--`!m:('a)metric. istopology
    (\S'. !x. S' x ==> ?e. &0 < e /\ (!y. (dist m)(x,y) < e ==> S' y))`--),
  GEN_TAC THEN
  REWRITE_TAC[istopology, re_null, re_universe, re_Union, re_intersect, re_subset] THEN
  CONV_TAC(REDEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC (--`&1`--) THEN MATCH_ACCEPT_TAC REAL_LT_01,
        REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
    DISCH_THEN(fn th => POP_ASSUM(CONJUNCTS_THEN(MP_TAC o SPEC (--`x:'a`--)))
                    THEN REWRITE_TAC[th]) THEN
    DISCH_THEN(X_CHOOSE_TAC (--`e1:real`--)) THEN
    DISCH_THEN(X_CHOOSE_TAC (--`e2:real`--)) THEN
    REPEAT_TCL DISJ_CASES_THEN MP_TAC
        (SPECL [(--`e1:real`--), (--`e2:real`--)] REAL_LT_TOTAL) THENL
     [DISCH_THEN SUBST_ALL_TAC THEN EXISTS_TAC (--`e2:real`--) THEN
      ASM_REWRITE_TAC[] THEN GEN_TAC THEN
      DISCH_THEN(fn th => EVERY_ASSUM(ASSUME_TAC o C MATCH_MP th o CONJUNCT2))
      THEN ASM_REWRITE_TAC[],
      DISCH_THEN(curry op THEN (EXISTS_TAC (--`e1:real`--)) o MP_TAC),
      DISCH_THEN(curry op THEN (EXISTS_TAC (--`e2:real`--)) o MP_TAC)] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fn th2 => GEN_TAC THEN DISCH_THEN(fn th1 =>
      ASSUME_TAC th1 THEN ASSUME_TAC (MATCH_MP REAL_LT_TRANS (CONJ th1 th2))))
    THEN CONJ_TAC THEN FIRST_ASSUM (MATCH_MP_TAC o CONJUNCT2)
    THEN FIRST_ASSUM ACCEPT_TAC,
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN (--`y:'a->bool`--)
     (fn th => POP_ASSUM(X_CHOOSE_TAC (--`e:real`--) o C MATCH_MP (CONJUNCT2 th) o
                     C MATCH_MP (CONJUNCT1 th)) THEN ASSUME_TAC th)) THEN
    EXISTS_TAC (--`e:real`--) THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC (--`z:'a`--) THEN
    DISCH_THEN(fn th => FIRST_ASSUM(ASSUME_TAC o C MATCH_MP th o CONJUNCT2)) THEN
    EXISTS_TAC (--`y:'a->bool`--) THEN ASM_REWRITE_TAC[]]);

val MTOP_OPEN = prove_thm("MTOP_OPEN",
  (--`!S' (m:('a)metric). open(mtop m) S' =
      (!x. S' x ==> ?e. &0 < e /\ (!y. (dist m(x,y)) < e ==> S' y))`--),
  GEN_TAC THEN REWRITE_TAC[mtop] THEN
  REWRITE_TAC[REWRITE_RULE[topology_tybij] mtop_istopology] THEN
  BETA_TAC THEN REWRITE_TAC[]);

(*---------------------------------------------------------------------------*)
(* Define open ball in metric space + prove basic properties                 *)
(*---------------------------------------------------------------------------*)

val ball = new_definition("ball",
  (--`!m:('a)metric. !x e. B(m)(x,e) = \y. (dist m)(x,y) < e`--));

val BALL_OPEN = prove_thm("BALL_OPEN",
  (--`!m:('a)metric. !x e. &0 < e ==> open(mtop(m))(B(m)(x,e))`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[MTOP_OPEN] THEN
  X_GEN_TAC (--`z:'a`--) THEN REWRITE_TAC[ball] THEN BETA_TAC THEN
  DISCH_THEN(ASSUME_TAC o ONCE_REWRITE_RULE[GSYM REAL_SUB_LT]) THEN
  EXISTS_TAC (--`e - dist(m:('a)metric)(x,z)`--) THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC (--`y:'a`--) THEN REWRITE_TAC[REAL_LT_SUB_LADD] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC (--`dist(m)(x:'a,z) + dist(m)(z,y)`--) THEN
  ASM_REWRITE_TAC[METRIC_TRIANGLE]);

val BALL_NEIGH = prove_thm("BALL_NEIGH",
  (--`!m:('a)metric. !x e. &0 < e ==> neigh(mtop(m))(B(m)(x,e),x)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[neigh] THEN EXISTS_TAC (--`B(m)(x:'a,e)`--) THEN
  REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
   [MATCH_MP_TAC BALL_OPEN,
    REWRITE_TAC[ball] THEN BETA_TAC THEN REWRITE_TAC[METRIC_SAME]] THEN
  POP_ASSUM ACCEPT_TAC);

(*---------------------------------------------------------------------------*)
(* Characterize limit point in a metric topology                             *)
(*---------------------------------------------------------------------------*)

val MTOP_LIMPT = prove_thm("MTOP_LIMPT",
  (--`!m:('a)metric. !x S'. limpt(mtop m) x S' =
      !e. &0 < e ==> ?y. ~(x = y) /\ S' y /\ (dist m)(x,y) < e`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[limpt] THEN EQ_TAC THENL
   [DISCH_THEN(curry op THEN (GEN_TAC THEN DISCH_TAC) o MP_TAC o SPEC (--`B(m)(x:'a,e)`--))
    THEN FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP BALL_NEIGH th]) THEN
    REWRITE_TAC[ball] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC,
    DISCH_TAC THEN GEN_TAC THEN REWRITE_TAC[neigh] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`P:'a->bool`--)
      (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
    REWRITE_TAC[MTOP_OPEN] THEN
    DISCH_THEN(MP_TAC o SPEC (--`x:'a`--)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`e:real`--) (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPEC (--`e:real`--)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`y:'a`--) STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC (--`y:'a`--)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN EXISTS_TAC (--`y:'a`--) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC (--`(P:'a->bool) re_subset N`--) THEN
    REWRITE_TAC[re_subset] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC]);

(*---------------------------------------------------------------------------*)
(* Define the usual metric on the real line                                  *)
(*---------------------------------------------------------------------------*)

val ISMET_R1 = prove_thm("ISMET_R1",
  (--`ismet (\(x,y). abs(y - x:real))`--),
  REWRITE_TAC[ismet] THEN CONV_TAC(ONCE_DEPTH_CONV PAIRED_BETA_CONV) THEN
  CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[ABS_ZERO, REAL_SUB_0] THEN
    CONV_TAC(RAND_CONV SYM_CONV) THEN REFL_TAC,
    SUBST1_TAC(SYM(SPECL [(--`x:real`--), (--`y:real`--)] REAL_NEG_SUB)) THEN
    REWRITE_TAC[ABS_NEG] THEN
     SUBGOAL_THEN (--`z - y:real = (x - y) + (z - x)`--)
      (fn th => SUBST1_TAC th THEN MATCH_ACCEPT_TAC ABS_TRIANGLE) THEN
    REWRITE_TAC[real_sub] THEN
    ONCE_REWRITE_TAC[AC(REAL_ADD_ASSOC,REAL_ADD_SYM)
      (--`(a + b) + (c + d) = (d + a) + (c + b):real`--)] THEN
    REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_LID]]);

val mr1 = new_definition("mr1",
  (--`mr1 = metric(\(x,y). abs(y - x))`--));

val MR1_DEF = prove_thm("MR1_DEF",
  (--`!x y. (dist mr1)(x,y) = abs(y - x)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[mr1, REWRITE_RULE[metric_tybij] ISMET_R1]
  THEN CONV_TAC(ONCE_DEPTH_CONV PAIRED_BETA_CONV) THEN REFL_TAC);

val MR1_ADD = prove_thm("MR1_ADD",
  (--`!x d. (dist mr1)(x,x + d) = abs(d)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[MR1_DEF, REAL_ADD_SUB]);

val MR1_SUB = prove_thm("MR1_SUB",
  (--`!x d. (dist mr1)(x,x - d) = abs(d)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[MR1_DEF, REAL_SUB_SUB, ABS_NEG]);

val MR1_ADD_LE = prove_thm("MR1_ADD_POS",
  (--`!x d. &0 <= d ==> ((dist mr1)(x,x + d) = d)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[MR1_ADD, abs]);

val MR1_SUB_LE = prove_thm("MR1_SUB_LE",
  (--`!x d. &0 <= d ==> ((dist mr1)(x,x - d) = d)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[MR1_SUB, abs]);

val MR1_ADD_LT = prove_thm("MR1_ADD_LT",
  (--`!x d. &0 < d ==> ((dist mr1)(x,x + d) = d)`--),
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
  MATCH_ACCEPT_TAC MR1_ADD_LE);

val MR1_SUB_LT = prove_thm("MR1_SUB_LT",
  (--`!x d. &0 < d ==> ((dist mr1)(x,x - d) = d)`--),
   REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
  MATCH_ACCEPT_TAC MR1_SUB_LE);

val MR1_BETWEEN1 = prove_thm("MR1_BETWEEN1",
  (--`!x y z. x < z /\ (dist mr1)(x,y) < (z - x) ==> y < z`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[MR1_DEF, ABS_BETWEEN1]);

(*---------------------------------------------------------------------------*)
(* Every real is a limit point of the real line                              *)
(*---------------------------------------------------------------------------*)

val MR1_LIMPT = prove_thm("MR1_LIMPT",
  (--`!x. limpt(mtop mr1) x re_universe`--),
  GEN_TAC THEN REWRITE_TAC[MTOP_LIMPT, re_universe] THEN
  X_GEN_TAC (--`e:real`--) THEN DISCH_TAC THEN
  EXISTS_TAC (--`x + (e / &2)`--) THEN
  REWRITE_TAC[MR1_ADD] THEN
  SUBGOAL_THEN (--`&0 <= (e / &2)`--) ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN
    ASM_REWRITE_TAC[REAL_LT_HALF1], ALL_TAC] THEN
  ASM_REWRITE_TAC[abs, REAL_LT_HALF2] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN
  REWRITE_TAC[REAL_ADD_RID_UNIQ] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN
  MATCH_MP_TAC REAL_LT_IMP_NE THEN
  ASM_REWRITE_TAC[REAL_LT_HALF1]);


val _ = adjoin_to_theory
{sig_ps = NONE,
 struct_ps = SOME (fn ppstrm =>
   (PP.add_string ppstrm "val _ = Parse.hide \"B\";";
    PP.add_newline ppstrm))};

val _ = export_theory();

end;
