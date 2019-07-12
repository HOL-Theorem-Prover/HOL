(*===========================================================================*)
(*  General Topology (from hol-light)                                        *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2015                       *)
(*                (c) Copyright, Valentina Bruno 2010                        *)
(*               (c) Copyright, Marco Maggesi 2014-2015                      *)
(* ========================================================================= *)

(* NOTE: this script is loaded after "integerTheory", before "realTheory", only
   general topology theorems without using real numbers should be put here.

   c.f. "rich_topologyTheory" for Elementary topology in Euclidean space.
 *)

open HolKernel Parse bossLib boolLib BasicProvers boolSimps simpLib mesonLib
     metisLib jrhUtils pairTheory pairLib pred_setTheory quotientTheory;

val _ = new_theory "topology";

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
(* Minimal amount of set notation is convenient                              *)
(*---------------------------------------------------------------------------*)

val re_intersect = prove (
   “!P Q. P INTER Q = \x:'a. P x /\ Q x”,
    PROVE_TAC [INTER_applied, IN_DEF]);

val COMPL_MEM = prove (
  ``!P:'a->bool. !x. P x = ~(COMPL P x)``,
    REPEAT GEN_TAC THEN REWRITE_TAC[COMPL_applied, IN_DEF] THEN
    BETA_TAC THEN REWRITE_TAC[]);

(*---------------------------------------------------------------------------*)
(* Characterize an (alpha)topology                                           *)
(*---------------------------------------------------------------------------*)

(* localized notion of open sets (one set being open in another) *)
val istopology = new_definition("istopology",
  ``!L. istopology L <=>
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
  REWRITE_TAC[BIGINTER_INSERT, AND_IMP_INTRO, NOT_INSERT_EMPTY,
              FORALL_IN_INSERT] THEN
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
  MATCH_MP_TAC EQ_IMPLIES THEN AP_TERM_TAC THEN REPEAT (POP_ASSUM MP_TAC) THEN
  SET_TAC[]);

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
   [DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM SUBSET_SUBSET_EQ] THEN
    ASM_SIMP_TAC (srw_ss()) [BIGUNION_applied, SUBSET_applied] THEN
    CONJ_TAC THEN GEN_TAC THENL [
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
     [ONCE_REWRITE_TAC[GSYM SUBSET_SUBSET_EQ] THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[SUBSET_applied] THEN
        ASM_SIMP_TAC (srw_ss()) [] THEN
        ASM_SIMP_TAC (srw_ss()) [IN_DEF],
        SIMP_TAC (srw_ss()) [SUBSET_applied] THEN REPEAT STRIP_TAC THEN
        FULL_SIMP_TAC (srw_ss()) [IN_DEF]],
      MATCH_MP_TAC OPEN_IN_BIGUNION THEN
      SIMP_TAC (srw_ss()) []]]);

val OPEN_NEIGH = store_thm("OPEN_NEIGH",
  “!S' top.
     open_in(top) S' = !x:'a. S' x ==> ?N. neigh(top)(N,x) /\ N SUBSET S'”,
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
  THENL [ALL_TAC,
         MATCH_MP_TAC OPEN_IN_BIGUNION THEN REPEAT (POP_ASSUM MP_TAC) THEN
         SET_TAC[]
  ] THEN GEN_REWR_TAC I [EXTENSION] THEN
  KNOW_TAC
    ``{topspace top DIFF s | s IN k} = IMAGE (\s. topspace top DIFF s) k`` THENL
  [FULL_SIMP_TAC std_ss [GSYM IMAGE_DEF], ALL_TAC] THEN DISC_RW_KILL THEN
  REWRITE_TAC [IN_BIGUNION, IN_BIGINTER] THEN
  GEN_REWR_TAC(QUANT_CONV o RAND_CONV o QUANT_CONV o LAND_CONV)[SPECIFICATION]>>
  ONCE_REWRITE_TAC [CONJ_SYM] THEN SIMP_TAC std_ss [EXISTS_IN_IMAGE] THEN
  REWRITE_TAC [
    METIS [SPECIFICATION]
          “(topspace top DIFF s) x <=> x IN (topspace top DIFF s)”] THEN
  REWRITE_TAC [IN_DIFF, IN_BIGINTER] THEN PROVE_TAC[]);

val BIGINTER_2 = store_thm ("BIGINTER_2",
 ``!s t. BIGINTER {s; t} = s INTER t``,
  SET_TAC []);

val CLOSED_IN_INTER = store_thm ("CLOSED_IN_INTER",
 ``!top s t. closed_in top s /\ closed_in top t ==> closed_in top (s INTER t)``,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM BIGINTER_2] THEN
  MATCH_MP_TAC CLOSED_IN_BIGINTER THEN REPEAT (POP_ASSUM MP_TAC) THEN
  SET_TAC[]);

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
  “!top. closed top ==>
         !S'. closed_in(top) S' = (!x:'a. limpt(top) x S' ==> S' x)”,
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
 >> REWRITE_TAC [TAUT_CONV “a \/ b \/ ~c <=> c ==> a \/ b”]
 >> EQUAL_TAC
 >> REWRITE_TAC [TAUT_CONV “(a <=> b \/ a) <=> b ==> a”]
 >> DISCH_THEN (SUBST1_TAC o SYM)
 >> POP_ASSUM ACCEPT_TAC);

(* ------------------------------------------------------------------------- *)
(* A generic notion of "hull" (convex, affine, conic hull and closure).      *)
(* ------------------------------------------------------------------------- *)

val _ = set_fixity "hull" (Infix(NONASSOC, 499));

val hull = new_definition ("hull",
  ``P hull s = BIGINTER {t | P t /\ s SUBSET t}``);

val HULL_P = store_thm ("HULL_P",
 ``!P s. P s ==> (P hull s = s)``,
  SIMP_TAC std_ss [hull, EXTENSION, IN_BIGINTER, GSPECIFICATION] THEN
  MESON_TAC[SUBSET_DEF]);

val P_HULL = store_thm ("P_HULL",
 ``!P s. (!f. (!s. s IN f ==> P s) ==> P(BIGINTER f)) ==> P(P hull s)``,
  REWRITE_TAC[hull] THEN SIMP_TAC std_ss [GSPECIFICATION]);

val HULL_EQ = store_thm ("HULL_EQ",
 ``!P s. (!f. (!s. s IN f ==> P s) ==> P(BIGINTER f))
         ==> ((P hull s = s) <=> P s)``,
  MESON_TAC[P_HULL, HULL_P]);

val HULL_HULL = store_thm ("HULL_HULL",
 ``!P s. P hull (P hull s) = P hull s``,
  SIMP_TAC std_ss [hull, EXTENSION, IN_BIGINTER, GSPECIFICATION, SUBSET_DEF] >>
  METIS_TAC[]);

val HULL_SUBSET = store_thm ("HULL_SUBSET",
 ``!P s. s SUBSET (P hull s)``,
  SIMP_TAC std_ss [hull,SUBSET_DEF,IN_BIGINTER,GSPECIFICATION] >> MESON_TAC[]);

val HULL_MONO = store_thm ("HULL_MONO",
 ``!P s t. s SUBSET t ==> (P hull s) SUBSET (P hull t)``,
   SIMP_TAC std_ss [hull, SUBSET_DEF, IN_BIGINTER, GSPECIFICATION] THEN
   METIS_TAC[]);

val HULL_ANTIMONO = store_thm ("HULL_ANTIMONO",
 ``!P Q s. P SUBSET Q ==> (Q hull s) SUBSET (P hull s)``,
  SIMP_TAC std_ss [SUBSET_DEF, hull, IN_BIGINTER, GSPECIFICATION] THEN
  MESON_TAC[IN_DEF]);

val HULL_MINIMAL = store_thm ("HULL_MINIMAL",
 ``!P s t. s SUBSET t /\ P t ==> (P hull s) SUBSET t``,
  SIMP_TAC std_ss [hull,SUBSET_DEF,IN_BIGINTER,GSPECIFICATION] >> METIS_TAC[]);

val SUBSET_HULL = store_thm ("SUBSET_HULL",
 ``!P s t. P t ==> ((P hull s) SUBSET t <=> s SUBSET t)``,
  SIMP_TAC std_ss [hull,SUBSET_DEF,IN_BIGINTER,GSPECIFICATION] >> METIS_TAC[]);

val HULL_UNIQUE = store_thm ("HULL_UNIQUE",
 ``!P s t. s SUBSET t /\ P t /\ (!t'. s SUBSET t' /\ P t' ==> t SUBSET t')
           ==> (P hull s = t)``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  SIMP_TAC std_ss [hull, SUBSET_DEF, IN_BIGINTER, GSPECIFICATION] THEN
  ASM_MESON_TAC[SUBSET_HULL, SUBSET_DEF]);

val HULL_UNION_SUBSET = store_thm ("HULL_UNION_SUBSET",
 ``!P s t. (P hull s) UNION (P hull t) SUBSET (P hull (s UNION t))``,
  SIMP_TAC std_ss [UNION_SUBSET, HULL_MONO, SUBSET_UNION]);

val HULL_UNION = store_thm ("HULL_UNION",
 ``!P s t. P hull (s UNION t) = P hull ((P hull s) UNION (P hull t))``,
  REPEAT STRIP_TAC >> ONCE_REWRITE_TAC[hull] >>
  AP_TERM_TAC >> SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, UNION_SUBSET] >>
  METIS_TAC[SUBSET_HULL]);

val HULL_UNION_LEFT = store_thm ("HULL_UNION_LEFT",
 ``!P s t:'a->bool.
        P hull (s UNION t) = P hull ((P hull s) UNION t)``,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[hull] THEN
  AP_TERM_TAC THEN SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, UNION_SUBSET] >>
  METIS_TAC[SUBSET_HULL]);

val HULL_UNION_RIGHT = store_thm ("HULL_UNION_RIGHT",
 ``!P s t:'a->bool.
        P hull (s UNION t) = P hull (s UNION (P hull t))``,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[hull] THEN
  AP_TERM_TAC THEN SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, UNION_SUBSET] >>
  MESON_TAC[SUBSET_HULL]);

val HULL_REDUNDANT_EQ = store_thm ("HULL_REDUNDANT_EQ",
 ``!P a s. a IN (P hull s) <=> (P hull (a INSERT s) = P hull s)``,
  REWRITE_TAC[hull] THEN SET_TAC[]);

val HULL_REDUNDANT = store_thm ("HULL_REDUNDANT",
 ``!P a s. a IN (P hull s) ==> (P hull (a INSERT s) = P hull s)``,
  REWRITE_TAC[HULL_REDUNDANT_EQ]);

val HULL_INDUCT = store_thm ("HULL_INDUCT",
 ``!P p s. (!x:'a. x IN s ==> p x) /\ P {x | p x}
           ==> !x. x IN P hull s ==> p x``,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [``P:('a->bool)->bool``, ``s:'a->bool``, ``{x:'a | p x}``]
                HULL_MINIMAL) THEN
  SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION]);

val HULL_INC = store_thm ("HULL_INC",
 ``!P s x. x IN s ==> x IN P hull s``,
  MESON_TAC[REWRITE_RULE[SUBSET_DEF] HULL_SUBSET]);

val HULL_IMAGE_SUBSET = store_thm ("HULL_IMAGE_SUBSET",
 ``!P f s. (P (P hull s)) /\ (!s. P s ==> P(IMAGE f s))
           ==> (P hull (IMAGE f s)) SUBSET ((IMAGE f (P hull s)))``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN
  ASM_SIMP_TAC std_ss [IMAGE_SUBSET, HULL_SUBSET]);

val HULL_IMAGE_GALOIS = store_thm ("HULL_IMAGE_GALOIS",
 ``!P f g s. (!s. P(P hull s)) /\
             (!s. P s ==> P(IMAGE f s)) /\ (!s. P s ==> P(IMAGE g s)) /\
             (!s t. s SUBSET IMAGE g t <=> IMAGE f s SUBSET t)
             ==> (P hull (IMAGE f s) = IMAGE f (P hull s))``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_SIMP_TAC std_ss [HULL_IMAGE_SUBSET] THEN
  FIRST_ASSUM(fn th => GEN_REWR_TAC I [GSYM th]) THEN
  MATCH_MP_TAC HULL_MINIMAL THEN
  ASM_SIMP_TAC std_ss [HULL_SUBSET]);

val HULL_IMAGE = store_thm ("HULL_IMAGE",
 ``!P f s. (!s. P(P hull s)) /\ (!s. P(IMAGE f s) <=> P s) /\
           (!x y:'a. (f x = f y) ==> (x = y)) /\ (!y. ?x. f x = y)
           ==> (P hull (IMAGE f s) = IMAGE f (P hull s))``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC [AND_IMP_INTRO] THEN
  SIMP_TAC std_ss [SET_RULE ``!f. (!x y. (f x = f y) ==> (x = y)) /\
   (!y. ?x. f x = y) <=> ?g. (!y. f (g y) = y) /\ !x. g (f x) = x``] THEN
  DISCH_THEN(X_CHOOSE_THEN ``g:'a->'a`` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC HULL_IMAGE_GALOIS THEN EXISTS_TAC ``g:'a->'a`` THEN
  ASM_REWRITE_TAC[] >> CONJ_TAC >| [ALL_TAC,
    REPEAT (POP_ASSUM MP_TAC) >> SET_TAC[]
  ] THEN X_GEN_TAC ``s:'a->bool`` THEN
  FIRST_X_ASSUM(fn th => GEN_REWR_TAC RAND_CONV [GSYM th]) THEN
  MATCH_MP_TAC EQ_IMPLIES THEN AP_TERM_TAC THEN REPEAT (POP_ASSUM MP_TAC) THEN
  SET_TAC[]);

val IS_HULL = store_thm ("IS_HULL",
 ``!P s. (!f. (!s. s IN f ==> P s) ==> P(BIGINTER f))
         ==> (P s <=> ?t. s = P hull t)``,
  MESON_TAC[HULL_P, P_HULL]);

val HULLS_EQ = store_thm ("HULLS_EQ",
 ``!P s t.
        (!f. (!s. s IN f ==> P s) ==> P (BIGINTER f)) /\
        s SUBSET (P hull t) /\ t SUBSET (P hull s)
        ==> (P hull s = P hull t)``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  CONJ_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN
  ASM_SIMP_TAC std_ss [P_HULL]);

val HULL_P_AND_Q = store_thm ("HULL_P_AND_Q",
 ``!P Q. (!f. (!s. s IN f ==> P s) ==> P(BIGINTER f)) /\
         (!f. (!s. s IN f ==> Q s) ==> Q(BIGINTER f)) /\
         (!s. Q s ==> Q(P hull s))
         ==> ((\x. P x /\ Q x) hull s = P hull (Q hull s))``,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HULL_UNIQUE THEN ASM_SIMP_TAC std_ss [HULL_INC, SUBSET_HULL] THEN
  ASM_MESON_TAC[P_HULL, HULL_SUBSET, SUBSET_TRANS]);

val _ = export_theory();
