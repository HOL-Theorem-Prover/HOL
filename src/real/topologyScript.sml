(*===========================================================================*)
(* Topologies and metric spaces, including metric on real line               *)
(*===========================================================================*)

open HolKernel Parse bossLib boolLib BasicProvers boolSimps simpLib mesonLib
     metisLib jrhUtils pairTheory pairLib pred_setTheory quotientTheory
     realTheory;

val _ = new_theory "topology";


(*---------------------------------------------------------------------------*)
(* Minimal amount of set notation is convenient                              *)
(*---------------------------------------------------------------------------*)

val re_intersect = prove(
   “!P Q. P INTER Q = \x:'a. P x /\ Q x”,
    PROVE_TAC [INTER_applied, IN_DEF]);

val COMPL_MEM = prove(
  ``!P:'a->bool. !x. P x = ~(COMPL P x)``,
  REPEAT GEN_TAC THEN REWRITE_TAC[COMPL_applied, IN_DEF] THEN
  BETA_TAC THEN REWRITE_TAC[]);

fun MESON ths tm = prove(tm,MESON_TAC ths);
fun METIS ths tm = prove(tm,METIS_TAC ths);

fun K_TAC _ = ALL_TAC;
val DISC_RW_KILL = DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN 
                   POP_ASSUM K_TAC;

fun SET_TAC L = 
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT COND_CASES_TAC THEN
    REWRITE_TAC (append [EXTENSION, SUBSET_DEF, PSUBSET_DEF, DISJOINT_DEF,
    SING_DEF] L) THEN
    SIMP_TAC std_ss [NOT_IN_EMPTY, IN_UNIV, IN_UNION, IN_INTER, IN_DIFF, 
      IN_INSERT, IN_DELETE, IN_REST, IN_BIGINTER, IN_BIGUNION, IN_IMAGE, 
      GSPECIFICATION, IN_DEF, EXISTS_PROD] THEN METIS_TAC [];

fun SET_RULE tm = prove(tm,SET_TAC []);

(*---------------------------------------------------------------------------*)
(* Characterize an (alpha)topology                                           *)
(*---------------------------------------------------------------------------*)

(* localized notion of open sets (one set being open in another) *)
val istopology = new_definition("istopology",
  ``!L. istopology L =
             {} IN L /\
             (!s t. s IN L /\ t IN L ==> (s INTER t) IN L) /\
             (!k. k SUBSET L ==> (BIGUNION k) IN L)``);

val EXISTS_istopology = prove (``?t. istopology t``,
    EXISTS_TAC ``univ(:'a set)``
 >> REWRITE_TAC [istopology, IN_UNIV]);

val topology_tydef = new_type_definition
  ("topology", EXISTS_istopology);

val topology_tybij = define_new_type_bijections
   {name="topology_tybij",
    ABS="topology", REP="open_in",tyax=topology_tydef};

val ISTOPOLOGY_OPEN_IN = store_thm
  ("ISTOPOLOGY_OPEN_IN", ``!top. istopology (open_in top)``,
    PROVE_TAC [topology_tybij]);

val TOPOLOGY_EQ = store_thm ("TOPOLOGY_EQ",
  ``!top1 top2. (top1 = top2) <=> !s. (open_in top1) s <=> (open_in top2) s``,
    REPEAT GEN_TAC THEN GEN_REWR_TAC RAND_CONV [GSYM FUN_EQ_THM] THEN
    REWRITE_TAC[ETA_AX] THEN PROVE_TAC[topology_tybij]);

(* global (abstract) notion of open sets *)
val open_DEF = new_definition
  ("open_DEF", ``open (s :'a topology) = (open_in s) UNIV``);

(* ------------------------------------------------------------------------- *)
(* Infer the "universe" from union of all sets in the topology.              *)
(* ------------------------------------------------------------------------- *)

val topspace = new_definition ("topspace",
  ``topspace top = BIGUNION {s | (open_in top) s}``);

(* the "universe" of global topology is the universe itself *)
val open_topspace = store_thm
  ("open_topspace", ``!top. open top ==> (topspace top = UNIV)``,
    GEN_TAC >> REWRITE_TAC [open_DEF]
 >> DISCH_TAC >> REWRITE_TAC [EXTENSION]
 >> REWRITE_TAC [topspace, IN_UNIV, IN_BIGUNION]
 >> GEN_TAC >> Q.EXISTS_TAC `UNIV`
 >> REWRITE_TAC [IN_UNIV, GSPECIFICATION]
 >> Q.EXISTS_TAC `UNIV` >> BETA_TAC
 >> ASM_SIMP_TAC std_ss []);

(* ------------------------------------------------------------------------- *)
(* Main properties of open sets.                                             *)
(* ------------------------------------------------------------------------- *)

val OPEN_IN_CLAUSES = store_thm ("OPEN_IN_CLAUSES",
 ``!top.
        open_in top {} /\
        (!s t. open_in top s /\ open_in top t ==> open_in top (s INTER t)) /\
        (!k. (!s. s IN k ==> open_in top s) ==> open_in top (BIGUNION k))``,
  SIMP_TAC std_ss [IN_DEF, SUBSET_DEF, 
  SIMP_RULE std_ss [istopology, IN_DEF, SUBSET_DEF] ISTOPOLOGY_OPEN_IN]);

val OPEN_IN_SUBSET = store_thm ("OPEN_IN_SUBSET",
 ``!top s. open_in top s ==> s SUBSET (topspace top)``,
  REWRITE_TAC[topspace] THEN SET_TAC[]);

val OPEN_IN_EMPTY = store_thm ("OPEN_IN_EMPTY",
 ``!top. open_in top {}``,
  REWRITE_TAC[OPEN_IN_CLAUSES]);

val OPEN_IN_INTER = store_thm ("OPEN_IN_INTER",
 ``!top s t. open_in top s /\ open_in top t ==> open_in top (s INTER t)``,
  REWRITE_TAC[OPEN_IN_CLAUSES]);

val OPEN_IN_BIGUNION = store_thm ("OPEN_IN_BIGUNION",
 ``!top k. (!s. s IN k ==> open_in top s) ==> open_in top (BIGUNION k)``,
  REWRITE_TAC[OPEN_IN_CLAUSES]);

val BIGUNION_2 = store_thm ("BIGUNION_2",
 ``!s t. BIGUNION {s;t} = s UNION t``,
  SET_TAC[]);

val OPEN_IN_UNION = store_thm ("OPEN_IN_UNION",
 ``!top s t. open_in top s /\ open_in top t ==> open_in top (s UNION t)``,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM BIGUNION_2] THEN
  MATCH_MP_TAC OPEN_IN_BIGUNION THEN REPEAT (POP_ASSUM MP_TAC) THEN SET_TAC[]);

val OPEN_IN_TOPSPACE = store_thm ("OPEN_IN_TOPSPACE",
 ``!top. open_in top (topspace top)``,
  SIMP_TAC std_ss [topspace, OPEN_IN_BIGUNION, GSPECIFICATION]);

val OPEN_IN_BIGINTER = store_thm ("OPEN_IN_BIGINTER",
 ``!top s:('a->bool)->bool.
        FINITE s /\ ~(s = {}) /\ (!t. t IN s ==> open_in top t)
        ==> open_in top (BIGINTER s)``,
  GEN_TAC THEN REWRITE_TAC[GSYM AND_IMP_INTRO] THEN
  KNOW_TAC ``!s. (s <> {} ==> (!t. t IN s ==> open_in top t) ==>
                               open_in top (BIGINTER s)) =
             (\s. s <> {} ==> (!t. t IN s ==> open_in top t) ==>
                               open_in top (BIGINTER s)) s`` THENL
  [FULL_SIMP_TAC std_ss [], ALL_TAC] THEN DISC_RW_KILL THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  REWRITE_TAC[BIGINTER_INSERT, AND_IMP_INTRO, NOT_INSERT_EMPTY, FORALL_IN_INSERT] THEN
  SIMP_TAC std_ss [GSYM RIGHT_FORALL_IMP_THM] THEN
  MAP_EVERY X_GEN_TAC [``f:('a->bool)->bool``, ``s:'a->bool``] THEN
  ASM_CASES_TAC ``f:('a->bool)->bool = {}`` THEN
  ASM_SIMP_TAC std_ss [BIGINTER_EMPTY, INTER_UNIV] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC OPEN_IN_INTER THEN ASM_SIMP_TAC std_ss []);

val OPEN_IN_SUBOPEN = store_thm ("OPEN_IN_SUBOPEN",
 ``!top s:'a->bool.
        open_in top s <=>
        !x. x IN s ==> ?t. open_in top t /\ x IN t /\ t SUBSET s``,
  REPEAT GEN_TAC THEN EQ_TAC THENL [PROVE_TAC[SUBSET_REFL], ALL_TAC] THEN
  SIMP_TAC std_ss [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] THEN
  REWRITE_TAC[DECIDE ``a ==> b /\ c <=> (a ==> b) /\ (a ==> c)``] THEN
  SIMP_TAC std_ss [FORALL_AND_THM, GSYM LEFT_EXISTS_IMP_THM] THEN
  ONCE_REWRITE_TAC[GSYM FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_BIGUNION) THEN
  MATCH_MP_TAC EQ_IMPLIES THEN AP_TERM_TAC THEN REPEAT (POP_ASSUM MP_TAC) THEN SET_TAC[]);

(*---------------------------------------------------------------------------*)
(* Characterize a neighbourhood of a point relative to a topology            *)
(*---------------------------------------------------------------------------*)

val neigh = new_definition ("neigh",
   “neigh(top)(N,(x:'a)) = ?P. (open_in top) P /\ P SUBSET N /\ P x”);

(*---------------------------------------------------------------------------*)
(* Prove various properties / characterizations of open sets                 *)
(*---------------------------------------------------------------------------*)

val OPEN_OWN_NEIGH = store_thm("OPEN_OWN_NEIGH",
  “!S' top. !x:'a. open_in(top) S' /\ S' x ==> neigh(top)(S',x)”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[neigh] THEN
  EXISTS_TAC “S':'a->bool” THEN ASM_REWRITE_TAC[SUBSET_REFL]);

val OPEN_UNOPEN = store_thm(
  "OPEN_UNOPEN",
  ``!S' top.
       open_in(top) S' <=>
       (BIGUNION { P | open_in(top) P /\ P SUBSET S' } = S')``,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
    ASM_SIMP_TAC (srw_ss()) [BIGUNION_applied, SUBSET_applied] THEN CONJ_TAC THEN
    GEN_TAC THENL [
      DISCH_THEN(Q.X_CHOOSE_THEN `s` STRIP_ASSUME_TAC) THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      FULL_SIMP_TAC (srw_ss()) [IN_DEF],
      DISCH_TAC THEN EXISTS_TAC ``S':'a->bool`` THEN
      ASM_SIMP_TAC(srw_ss())[IN_DEF]
    ],
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC OPEN_IN_BIGUNION THEN
    SIMP_TAC (srw_ss()) []
  ]);

val OPEN_SUBOPEN = store_thm("OPEN_SUBOPEN",
  ``!S' top. open_in(top) S' <=>
             !x:'a. S' x ==> ?P. P x /\ open_in(top) P /\ P SUBSET S'``,
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    EXISTS_TAC “S':'a->bool” THEN ASM_REWRITE_TAC[SUBSET_REFL],
    DISCH_TAC THEN C SUBGOAL_THEN SUBST1_TAC
     ``S' = BIGUNION { P | open_in(top) P /\ P SUBSET S'}`` THENL
     [ONCE_REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[SUBSET_applied] THEN
        ASM_SIMP_TAC (srw_ss()) [] THEN
        ASM_SIMP_TAC (srw_ss()) [IN_DEF],
        SIMP_TAC (srw_ss()) [SUBSET_applied] THEN REPEAT STRIP_TAC THEN
        FULL_SIMP_TAC (srw_ss()) [IN_DEF]],
      MATCH_MP_TAC OPEN_IN_BIGUNION THEN
      SIMP_TAC (srw_ss()) []]]);

val OPEN_NEIGH = store_thm("OPEN_NEIGH",
  “!S' top. open_in(top) S' = !x:'a. S' x ==> ?N. neigh(top)(N,x) /\ N SUBSET S'”,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC “S':'a->bool” THEN
    REWRITE_TAC[SUBSET_REFL, neigh] THEN
    EXISTS_TAC “S':'a->bool” THEN ASM_REWRITE_TAC[SUBSET_REFL],
    DISCH_TAC THEN ONCE_REWRITE_TAC[OPEN_SUBOPEN] THEN
    GEN_TAC THEN DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN(X_CHOOSE_THEN “N:'a->bool” (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC))
    THEN REWRITE_TAC[neigh] THEN
    DISCH_THEN(X_CHOOSE_THEN “P:'a->bool” STRIP_ASSUME_TAC) THEN
    EXISTS_TAC “P:'a->bool” THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC “N:'a->bool” THEN
    ASM_REWRITE_TAC[]]);

(*---------------------------------------------------------------------------*)
(* Characterize closed sets in a topological space                           *)
(*---------------------------------------------------------------------------*)

val closed_in = new_definition ("closed_in",
  ``closed_in top s <=>
        s SUBSET (topspace top) /\ open_in top (topspace top DIFF s)``);

(* global (abstract) notion of closed sets *)
val closed_DEF = new_definition
  ("closed_DEF", ``closed (s :'a topology) = (closed_in s) UNIV``);

val closed_topspace = store_thm
  ("closed_topspace", ``!top. closed top ==> (topspace top = UNIV)``,
    GEN_TAC >> REWRITE_TAC [closed_DEF, closed_in]
 >> REWRITE_TAC [UNIV_SUBSET]
 >> STRIP_TAC >> ASM_REWRITE_TAC []);

(* original definition of "closed_in" in HOL4 *)
val CLOSED_IN_OPEN_IN_COMPL = store_thm
  ("CLOSED_IN_OPEN_IN_COMPL",
  ``!top. closed top ==> (!s. closed_in top s = open_in top (COMPL s))``,
    rpt STRIP_TAC
 >> IMP_RES_TAC closed_topspace
 >> ASM_REWRITE_TAC [closed_in, GSYM COMPL_DEF, SUBSET_UNIV]);

val CLOSED_IN_SUBSET = store_thm ("CLOSED_IN_SUBSET",
 ``!top s. closed_in top s ==> s SUBSET (topspace top)``,
  PROVE_TAC[closed_in]);

val CLOSED_IN_EMPTY = store_thm ("CLOSED_IN_EMPTY",
 ``!top. closed_in top {}``,
  REWRITE_TAC[closed_in, EMPTY_SUBSET, DIFF_EMPTY, OPEN_IN_TOPSPACE]);

val CLOSED_IN_TOPSPACE = store_thm ("CLOSED_IN_TOPSPACE",
 ``!top. closed_in top (topspace top)``,
  REWRITE_TAC[closed_in, SUBSET_REFL, DIFF_EQ_EMPTY, OPEN_IN_EMPTY]);

val CLOSED_IN_UNION = store_thm ("CLOSED_IN_UNION",
 ``!top s t. closed_in top s /\ closed_in top t ==> closed_in top (s UNION t)``,
  SIMP_TAC std_ss [closed_in, UNION_SUBSET, OPEN_IN_INTER,
           SET_RULE ``u DIFF (s UNION t) = (u DIFF s) INTER (u DIFF t)``]);

val CLOSED_IN_BIGINTER = store_thm ("CLOSED_IN_BIGINTER",
 ``!top k:('a->bool)->bool.
        ~(k = {}) /\ (!s. s IN k ==> closed_in top s)
        ==> closed_in top (BIGINTER k)``,
  REPEAT GEN_TAC THEN REWRITE_TAC[closed_in] THEN REPEAT STRIP_TAC THENL
   [REPEAT (POP_ASSUM MP_TAC) THEN SET_TAC[], ALL_TAC] THEN
  SUBGOAL_THEN ``topspace top DIFF BIGINTER k :'a->bool =
                BIGUNION {topspace top DIFF s | s IN k}`` SUBST1_TAC
  THENL [ALL_TAC, MATCH_MP_TAC OPEN_IN_BIGUNION THEN REPEAT (POP_ASSUM MP_TAC) THEN SET_TAC[]] THEN
  GEN_REWR_TAC I [EXTENSION] THEN
  KNOW_TAC ``{topspace top DIFF s | s IN k} = IMAGE (\s. topspace top DIFF s) k`` THENL
  [FULL_SIMP_TAC std_ss [GSYM IMAGE_DEF], ALL_TAC] THEN DISC_RW_KILL THEN
  REWRITE_TAC [IN_BIGUNION, IN_BIGINTER] THEN
  GEN_REWR_TAC (QUANT_CONV o RAND_CONV o QUANT_CONV o LAND_CONV) [SPECIFICATION] THEN 
  ONCE_REWRITE_TAC [CONJ_SYM] THEN SIMP_TAC std_ss [EXISTS_IN_IMAGE] THEN
  REWRITE_TAC [METIS [SPECIFICATION]``(topspace top DIFF s) x = x IN (topspace top DIFF s)``] THEN
  REWRITE_TAC [IN_DIFF, IN_BIGINTER] THEN PROVE_TAC[]);

val BIGINTER_2 = store_thm ("BIGINTER_2",
 ``!s t. BIGINTER {s; t} = s INTER t``,
  SET_TAC []);

val CLOSED_IN_INTER = store_thm ("CLOSED_IN_INTER",
 ``!top s t. closed_in top s /\ closed_in top t ==> closed_in top (s INTER t)``,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM BIGINTER_2] THEN
  MATCH_MP_TAC CLOSED_IN_BIGINTER THEN REPEAT (POP_ASSUM MP_TAC) THEN SET_TAC[]);

val OPEN_IN_CLOSED_IN_EQ = store_thm ("OPEN_IN_CLOSED_IN_EQ",
 ``!top s. open_in top s <=>
           s SUBSET topspace top /\ closed_in top (topspace top DIFF s)``,
  REWRITE_TAC[closed_in, SET_RULE ``(u DIFF s) SUBSET u``] THEN
  REWRITE_TAC[SET_RULE ``u DIFF (u DIFF s) = u INTER s``] THEN
  PROVE_TAC[OPEN_IN_SUBSET, SET_RULE ``s SUBSET t ==> (t INTER s = s)``]);

val OPEN_IN_CLOSED_IN = store_thm ("OPEN_IN_CLOSED_IN",
 ``!top s. s SUBSET topspace top
       ==> (open_in top s <=> closed_in top (topspace top DIFF s))``,
  SIMP_TAC std_ss [OPEN_IN_CLOSED_IN_EQ]);

val OPEN_IN_DIFF = store_thm ("OPEN_IN_DIFF",
 ``!top s t:'a->bool.
      open_in top s /\ closed_in top t ==> open_in top (s DIFF t)``,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN ``s DIFF t :'a->bool = s INTER (topspace top DIFF t)``
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[],
    MATCH_MP_TAC OPEN_IN_INTER THEN PROVE_TAC[closed_in]]);

val CLOSED_IN_DIFF = store_thm ("CLOSED_IN_DIFF",
 ``!top s t:'a->bool.
        closed_in top s /\ open_in top t ==> closed_in top (s DIFF t)``,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN ``s DIFF t :'a->bool = s INTER (topspace top DIFF t)``
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP CLOSED_IN_SUBSET) THEN SET_TAC[],
    MATCH_MP_TAC CLOSED_IN_INTER THEN PROVE_TAC[OPEN_IN_CLOSED_IN_EQ]]);

val CLOSED_IN_BIGUNION = store_thm ("CLOSED_IN_BIGUNION",
 ``!top s. FINITE s /\ (!t. t IN s ==> closed_in top t)
           ==> closed_in top (BIGUNION s)``,
  GEN_TAC THEN REWRITE_TAC[GSYM AND_IMP_INTRO] THEN
  KNOW_TAC ``!s. ((!t. t IN s ==> closed_in top t) ==>
                   closed_in top (BIGUNION s)) =
             (\s. (!t. t IN s ==> closed_in top t) ==>
                   closed_in top (BIGUNION s)) s`` THENL
  [FULL_SIMP_TAC std_ss [], ALL_TAC] THEN DISC_RW_KILL THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  REWRITE_TAC[BIGUNION_INSERT, BIGUNION_EMPTY, CLOSED_IN_EMPTY, IN_INSERT] THEN
  PROVE_TAC[CLOSED_IN_UNION]);

(*---------------------------------------------------------------------------*)
(* Define limit point in topological space                                   *)
(*---------------------------------------------------------------------------*)

val limpt = new_definition("limpt",
  “limpt(top) x S' =
      !N:'a->bool. neigh(top)(N,x) ==> ?y. ~(x = y) /\ S' y /\ N y”);

(*---------------------------------------------------------------------------*)
(* Prove that a set is closed iff it contains all its limit points           *)
(*---------------------------------------------------------------------------*)

val CLOSED_LIMPT = store_thm
  ("CLOSED_LIMPT",
  “!top. closed top ==> !S'. closed_in(top) S' = (!x:'a. limpt(top) x S' ==> S' x)”,
    GEN_TAC >> DISCH_TAC
 >> IMP_RES_TAC closed_topspace
 >> GEN_TAC >> CONV_TAC (ONCE_DEPTH_CONV CONTRAPOS_CONV)
 >> REWRITE_TAC[closed_in, limpt]
 >> ASM_REWRITE_TAC [SUBSET_UNIV, GSYM COMPL_DEF]
 >> CONV_TAC(ONCE_DEPTH_CONV NOT_FORALL_CONV)
 >> FREEZE_THEN (fn th => ONCE_REWRITE_TAC[th]) (SPEC “S':'a->bool” COMPL_MEM)
 >> REWRITE_TAC []
 >> SPEC_TAC(“COMPL(S':'a->bool)”,“S':'a->bool”)
 >> GEN_TAC >> REWRITE_TAC [NOT_IMP]
 >> CONV_TAC (ONCE_DEPTH_CONV NOT_EXISTS_CONV)
 >> REWRITE_TAC [DE_MORGAN_THM]
 >> REWRITE_TAC [OPEN_NEIGH, SUBSET_applied]
 >> AP_TERM_TAC >> ABS_TAC
 >> ASM_CASES_TAC “(S':'a->bool) x” >> ASM_REWRITE_TAC []
 >> REWRITE_TAC [TAUT_CONV “a \/ b \/ ~c = c ==> a \/ b”]
 >> EQUAL_TAC
 >> REWRITE_TAC [TAUT_CONV “(a = b \/ a) = b ==> a”]
 >> DISCH_THEN (SUBST1_TAC o SYM)
 >> POP_ASSUM ACCEPT_TAC);

(*---------------------------------------------------------------------------*)
(* Characterize an (alpha)metric                                             *)
(*---------------------------------------------------------------------------*)

val ismet = new_definition("ismet",
  “ismet (m:'a#'a->real)
        =
      (!x y. (m(x,y) = &0) = (x = y)) /\
      (!x y z. m(y,z) <= m(x,y) + m(x,z))”);

val metric_tydef = new_type_definition
 ("metric",
  prove (“?m:('a#'a->real). ismet m”,
        EXISTS_TAC “\(x:'a,(y:'a)). if (x = y) then &0 else &1” THEN
        REWRITE_TAC[ismet] THEN
        CONV_TAC(ONCE_DEPTH_CONV PAIRED_BETA_CONV) THEN
        CONJ_TAC THEN REPEAT GEN_TAC THENL
         [BOOL_CASES_TAC “x:'a = y” THEN REWRITE_TAC[REAL_10],
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

val METRIC_ISMET = store_thm("METRIC_ISMET",
  “!m:('a)metric. ismet (dist m)”,
  GEN_TAC THEN REWRITE_TAC[metric_tybij]);

val METRIC_ZERO = store_thm("METRIC_ZERO",
  “!m:('a)metric. !x y. ((dist m)(x,y) = &0) = (x = y)”,
  REPEAT GEN_TAC THEN ASSUME_TAC(SPEC “m:('a)metric” METRIC_ISMET) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ismet]) THEN ASM_REWRITE_TAC[]);

val METRIC_SAME = store_thm("METRIC_SAME",
  “!m:('a)metric. !x. (dist m)(x,x) = &0”,
  REPEAT GEN_TAC THEN REWRITE_TAC[METRIC_ZERO]);

val METRIC_POS = store_thm("METRIC_POS",
  “!m:('a)metric. !x y. &0 <= (dist m)(x,y)”,
  REPEAT GEN_TAC THEN ASSUME_TAC(SPEC “m:('a)metric” METRIC_ISMET) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ismet]) THEN
  FIRST_ASSUM(MP_TAC o
             SPECL [“x:'a”, “y:'a”, “y:'a”] o CONJUNCT2) THEN
  REWRITE_TAC[REWRITE_RULE[]
             (SPECL [“m:('a)metric”, “y:'a”, “y:'a”]
                    METRIC_ZERO)]
  THEN CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[REAL_NOT_LE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_ADD2 o W CONJ) THEN
  REWRITE_TAC[REAL_ADD_LID]);

val METRIC_SYM = store_thm("METRIC_SYM",
  “!m:('a)metric. !x y. (dist m)(x,y) = (dist m)(y,x)”,
  REPEAT GEN_TAC THEN ASSUME_TAC(SPEC “m:('a)metric” METRIC_ISMET) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ismet]) THEN FIRST_ASSUM
   (MP_TAC o GENL [“y:'a”, “z:'a”] o SPECL [“z:'a”, “y:'a”, “z:'a”] o CONJUNCT2)
  THEN REWRITE_TAC[METRIC_SAME, REAL_ADD_RID] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[GSYM REAL_LE_ANTISYM]);

val METRIC_TRIANGLE = store_thm("METRIC_TRIANGLE",
  “!m:('a)metric. !x y z. (dist m)(x,z) <= (dist m)(x,y) + (dist m)(y,z)”,
  REPEAT GEN_TAC THEN ASSUME_TAC(SPEC “m:('a)metric” METRIC_ISMET) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ismet]) THEN
  GEN_REWR_TAC (RAND_CONV o LAND_CONV)  [METRIC_SYM] THEN
  ASM_REWRITE_TAC[]);

val METRIC_NZ = store_thm("METRIC_NZ",
  “!m:('a)metric. !x y. ~(x = y) ==> &0 < (dist m)(x,y)”,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [“m:('a)metric”, “x:'a”, “y:'a”] METRIC_ZERO)) THEN
  ONCE_REWRITE_TAC[TAUT_CONV “~a ==> b = b \/ a”] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN
  REWRITE_TAC[GSYM REAL_LE_LT, METRIC_POS]);

(*---------------------------------------------------------------------------*)
(* Now define metric topology and prove equivalent definition of "open"      *)
(*---------------------------------------------------------------------------*)

val mtop = new_definition("mtop",
  “!m:('a)metric. mtop m =
    topology(\S'. !x. S' x ==> ?e. &0 < e /\ (!y. (dist m)(x,y) < e ==> S' y))”);

val mtop_istopology = store_thm("mtop_istopology",
  ``!m:('a)metric.
      istopology (\S'. !x. S' x ==>
                           ?e. &0 < e /\
                               (!y. (dist m)(x,y) < e ==> S' y))``,
  GEN_TAC THEN
  SIMP_TAC bool_ss [istopology, EMPTY_DEF, UNIV_DEF, BIGUNION_applied,
                    re_intersect, SUBSET_applied, IN_DEF] THEN
  REVERSE (REPEAT STRIP_TAC) THENL (* 2 subgoals *)
  [ (* goal 1 (of 2) *)
    RES_TAC >> Q.EXISTS_TAC `e` >> ASM_REWRITE_TAC [] \\
    rpt STRIP_TAC \\
    Q.EXISTS_TAC `s` >> ASM_REWRITE_TAC [] >> RES_TAC,
    (* goal 2 (of 2) *)
    RES_TAC \\
    REPEAT_TCL DISJ_CASES_THEN MP_TAC
        (SPECL [“e:real”, “e':real”] REAL_LT_TOTAL) >|
    [ (* goal 2.1 (of 3) *)
      DISCH_THEN SUBST_ALL_TAC THEN EXISTS_TAC “e':real” THEN
      ASM_REWRITE_TAC [] THEN GEN_TAC THEN
      DISCH_TAC >> PROVE_TAC [],
      (* goal 2.2 (of 3) *)
      DISCH_THEN(curry op THEN (EXISTS_TAC “e:real”) o MP_TAC) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (fn th2 => GEN_TAC THEN DISCH_THEN (fn th1 =>
                  ASSUME_TAC th1 THEN ASSUME_TAC (MATCH_MP REAL_LT_TRANS (CONJ th1 th2))))
      >> PROVE_TAC [],
      (* goal 2.3 (of 3) *)
      DISCH_THEN(curry op THEN (EXISTS_TAC “e':real”) o MP_TAC) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (fn th2 => GEN_TAC THEN DISCH_THEN(fn th1 =>
                  ASSUME_TAC th1 THEN ASSUME_TAC (MATCH_MP REAL_LT_TRANS (CONJ th1 th2))))
      >> PROVE_TAC [] ] ]);

val MTOP_OPEN = store_thm("MTOP_OPEN",
  “!S' (m:('a)metric). open_in(mtop m) S' =
      (!x. S' x ==> ?e. &0 < e /\ (!y. (dist m(x,y)) < e ==> S' y))”,
  GEN_TAC THEN REWRITE_TAC[mtop] THEN
  REWRITE_TAC[REWRITE_RULE[topology_tybij] mtop_istopology] THEN
  BETA_TAC THEN REWRITE_TAC[]);

(*---------------------------------------------------------------------------*)
(* Define open ball in metric space + prove basic properties                 *)
(*---------------------------------------------------------------------------*)

val ball = new_definition("ball",
  “!m:('a)metric. !x e. B(m)(x,e) = \y. (dist m)(x,y) < e”);

val BALL_OPEN = store_thm("BALL_OPEN",
  “!m:('a)metric. !x e. &0 < e ==> open_in(mtop(m))(B(m)(x,e))”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[MTOP_OPEN] THEN
  X_GEN_TAC “z:'a” THEN REWRITE_TAC[ball] THEN BETA_TAC THEN
  DISCH_THEN(ASSUME_TAC o ONCE_REWRITE_RULE[GSYM REAL_SUB_LT]) THEN
  EXISTS_TAC “e - dist(m:('a)metric)(x,z)” THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC “y:'a” THEN REWRITE_TAC[REAL_LT_SUB_LADD] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC “dist(m)(x:'a,z) + dist(m)(z,y)” THEN
  ASM_REWRITE_TAC[METRIC_TRIANGLE]);

val BALL_NEIGH = store_thm("BALL_NEIGH",
  “!m:('a)metric. !x e. &0 < e ==> neigh(mtop(m))(B(m)(x,e),x)”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[neigh] THEN EXISTS_TAC “B(m)(x:'a,e)” THEN
  REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
   [MATCH_MP_TAC BALL_OPEN,
    REWRITE_TAC[ball] THEN BETA_TAC THEN REWRITE_TAC[METRIC_SAME]] THEN
  POP_ASSUM ACCEPT_TAC);

(*---------------------------------------------------------------------------*)
(* Characterize limit point in a metric topology                             *)
(*---------------------------------------------------------------------------*)

val MTOP_LIMPT = store_thm("MTOP_LIMPT",
  “!m:('a)metric. !x S'. limpt(mtop m) x S' =
      !e. &0 < e ==> ?y. ~(x = y) /\ S' y /\ (dist m)(x,y) < e”,
  REPEAT GEN_TAC THEN REWRITE_TAC[limpt] THEN EQ_TAC THENL
   [DISCH_THEN(curry op THEN (GEN_TAC THEN DISCH_TAC) o MP_TAC o SPEC “B(m)(x:'a,e)”)
    THEN FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP BALL_NEIGH th]) THEN
    REWRITE_TAC[ball] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC,
    DISCH_TAC THEN GEN_TAC THEN REWRITE_TAC[neigh] THEN
    DISCH_THEN(X_CHOOSE_THEN “P:'a->bool”
      (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
    REWRITE_TAC[MTOP_OPEN] THEN
    DISCH_THEN(MP_TAC o SPEC “x:'a”) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN “e:real” (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPEC “e:real”) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN “y:'a” STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC “y:'a”) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN EXISTS_TAC “y:'a” THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC “(P:'a->bool) SUBSET N” THEN
    REWRITE_TAC[SUBSET_applied] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC]);

(*---------------------------------------------------------------------------*)
(* Define the usual metric on the real line                                  *)
(*---------------------------------------------------------------------------*)

val ISMET_R1 = store_thm("ISMET_R1",
  “ismet (\(x,y). abs(y - x:real))”,
  REWRITE_TAC[ismet] THEN CONV_TAC(ONCE_DEPTH_CONV PAIRED_BETA_CONV) THEN
  CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[ABS_ZERO, REAL_SUB_0] THEN
    CONV_TAC(RAND_CONV SYM_CONV) THEN REFL_TAC,
    SUBST1_TAC(SYM(SPECL [“x:real”, “y:real”] REAL_NEG_SUB)) THEN
    REWRITE_TAC[ABS_NEG] THEN
     SUBGOAL_THEN “z - y:real = (x - y) + (z - x)”
      (fn th => SUBST1_TAC th THEN MATCH_ACCEPT_TAC ABS_TRIANGLE) THEN
    REWRITE_TAC[real_sub] THEN
    ONCE_REWRITE_TAC[AC(REAL_ADD_ASSOC,REAL_ADD_SYM)
      “(a + b) + (c + d) = (d + a) + (c + b):real”] THEN
    REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_LID]]);

val mr1 = new_definition("mr1",
  “mr1 = metric(\(x,y). abs(y - x))”);

val MR1_DEF = store_thm("MR1_DEF",
  “!x y. (dist mr1)(x,y) = abs(y - x)”,
  REPEAT GEN_TAC THEN REWRITE_TAC[mr1, REWRITE_RULE[metric_tybij] ISMET_R1]
  THEN CONV_TAC(ONCE_DEPTH_CONV PAIRED_BETA_CONV) THEN REFL_TAC);

val MR1_ADD = store_thm("MR1_ADD",
  “!x d. (dist mr1)(x,x + d) = abs(d)”,
  REPEAT GEN_TAC THEN REWRITE_TAC[MR1_DEF, REAL_ADD_SUB]);

val MR1_SUB = store_thm("MR1_SUB",
  “!x d. (dist mr1)(x,x - d) = abs(d)”,
  REPEAT GEN_TAC THEN REWRITE_TAC[MR1_DEF, REAL_SUB_SUB, ABS_NEG]);

val MR1_ADD_LE = store_thm("MR1_ADD_POS",
  “!x d. &0 <= d ==> ((dist mr1)(x,x + d) = d)”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[MR1_ADD, abs]);

val MR1_SUB_LE = store_thm("MR1_SUB_LE",
  “!x d. &0 <= d ==> ((dist mr1)(x,x - d) = d)”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[MR1_SUB, abs]);

val MR1_ADD_LT = store_thm("MR1_ADD_LT",
  “!x d. &0 < d ==> ((dist mr1)(x,x + d) = d)”,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
  MATCH_ACCEPT_TAC MR1_ADD_LE);

val MR1_SUB_LT = store_thm("MR1_SUB_LT",
  “!x d. &0 < d ==> ((dist mr1)(x,x - d) = d)”,
   REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
  MATCH_ACCEPT_TAC MR1_SUB_LE);

val MR1_BETWEEN1 = store_thm("MR1_BETWEEN1",
  “!x y z. x < z /\ (dist mr1)(x,y) < (z - x) ==> y < z”,
  REPEAT GEN_TAC THEN REWRITE_TAC[MR1_DEF, ABS_BETWEEN1]);

(*---------------------------------------------------------------------------*)
(* Every real is a limit point of the real line                              *)
(*---------------------------------------------------------------------------*)

val MR1_LIMPT = store_thm("MR1_LIMPT",
  ``!x. limpt(mtop mr1) x univ(:real)``,
  GEN_TAC THEN REWRITE_TAC[MTOP_LIMPT, UNIV_DEF] THEN
  X_GEN_TAC “e:real” THEN DISCH_TAC THEN
  EXISTS_TAC “x + (e / &2)” THEN
  REWRITE_TAC[MR1_ADD] THEN
  SUBGOAL_THEN “&0 <= (e / &2)” ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN
    ASM_REWRITE_TAC[REAL_LT_HALF1], ALL_TAC] THEN
  ASM_REWRITE_TAC[abs, REAL_LT_HALF2] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN
  REWRITE_TAC[REAL_ADD_RID_UNIQ] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN
  MATCH_MP_TAC REAL_LT_IMP_NE THEN
  ASM_REWRITE_TAC[REAL_LT_HALF1]);


val _ = remove_ovl_mapping "B" {Name = "B", Thy = "topology"};

val _ = export_theory();
