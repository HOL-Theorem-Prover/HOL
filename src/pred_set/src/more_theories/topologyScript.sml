(* ========================================================================= *)
(*  General Topology in Euclidean space (from hol-light's topology.ml)       *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2017                       *)
(*                (c) Copyright, Valentina Bruno 2010                        *)
(*               (c) Copyright, Marco Maggesi 2014-2017                      *)
(*             (c) Copyright, Andrea Gabrielli 2016-2017                     *)
(* ========================================================================= *)
(*  Basic Set Theory (using predicates as sets) (from hol-light's sets.ml)   *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2016                       *)
(*              (c) Copyright, Marco Maggesi 2012-2017                       *)
(*             (c) Copyright, Andrea Gabrielli 2012-2017                     *)
(* ========================================================================= *)
(*  Formalization of general topological and metric spaces in HOL Light      *)
(*                     (from hol-light's metric.ml)                          *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2017                       *)
(*                (c) Copyright, Marco Maggesi 2014-2017                     *)
(*             (c) Copyright, Andrea Gabrielli  2016-2017                    *)
(* ========================================================================= *)

(* NOTE: this script is loaded after "integerTheory" and before "realTheory".
   General topology theorems without using real numbers should be put here.

   See src/real/analysis/real_topologyTheory for Elementary Topology of
   (one-dimensional) Euclidean space.
 *)

open HolKernel Parse bossLib boolLib;

open boolSimps simpLib mesonLib metisLib pairTheory pairLib tautLib combinTheory
     pred_setTheory arithmeticTheory relationTheory cardinalTheory hurdUtils;

val _ = new_theory "topology";

fun METIS ths tm = prove(tm,METIS_TAC ths);

val DISC_RW_KILL = DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
                   POP_ASSUM K_TAC;

(* Begin of minimal hol-light compatibility layer *)
Theorem IMP_CONJ      = cardinalTheory.CONJ_EQ_IMP
Theorem IMP_IMP       = boolTheory.AND_IMP_INTRO
Theorem FINITE_SUBSET = pred_setTheory.SUBSET_FINITE_I

Theorem FINITE_INDUCT_STRONG :
   !P:('a->bool)->bool.
        P {} /\ (!x s. P s /\ ~(x IN s) /\ FINITE s ==> P(x INSERT s))
        ==> !s. FINITE s ==> P s
Proof
   METIS_TAC [FINITE_INDUCT]
QED

val REPLICATE_TAC = NTAC;
(* End of minimal hol-light compatibility layer *)

(*---------------------------------------------------------------------------*)
(* Characterize an (alpha)topology                                           *)
(*---------------------------------------------------------------------------*)

(* localized notion of open sets (one set being open in another) *)
Definition istopology :
    istopology L =
      ({} IN L /\
       (!s t. s IN L /\ t IN L ==> (s INTER t) IN L) /\
       (!k. k SUBSET L ==> (BIGUNION k) IN L))
End

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

Theorem TOPOLOGY_EQ:
  !top1 top2. (top1 = top2) <=> !s. (open_in top1) s <=> (open_in top2) s
Proof
  REPEAT GEN_TAC THEN simp[GSYM FUN_EQ_THM] THEN
  REWRITE_TAC[ETA_AX] THEN PROVE_TAC[topology_tybij]
QED

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

Definition neigh:
  neigh(top)(N,(x:'a)) = ?P. (open_in top) P /\ P SUBSET N /\ P x /\
                             N SUBSET topspace top
End

(*---------------------------------------------------------------------------*)
(* Prove various properties / characterizations of open sets                 *)
(*---------------------------------------------------------------------------*)

Theorem OPEN_OWN_NEIGH:
  !A top. !x:'a. open_in(top) A /\ A x ==> neigh(top)(A,x)
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[neigh] THEN Q.EXISTS_TAC ‘A’ THEN
  simp[SUBSET_REFL, OPEN_IN_SUBSET]
QED

Theorem OPEN_UNOPEN :
    !S' top. open_in(top) S' <=>
             (BIGUNION {P | open_in(top) P /\ P SUBSET S'} = S')
Proof
    rpt GEN_TAC >> EQ_TAC >|
  [ DISCH_TAC THEN ONCE_REWRITE_TAC[SET_EQ_SUBSET] THEN
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
    SIMP_TAC (srw_ss()) [] ]
QED

val OPEN_SUBOPEN = store_thm("OPEN_SUBOPEN",
  ``!S' top. open_in(top) S' <=>
             !x:'a. S' x ==> ?P. P x /\ open_in(top) P /\ P SUBSET S'``,
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    EXISTS_TAC “S':'a->bool” THEN ASM_REWRITE_TAC[SUBSET_REFL],
    DISCH_TAC THEN C SUBGOAL_THEN SUBST1_TAC
     ``S' = BIGUNION { P | open_in(top) P /\ P SUBSET S'}`` THENL
     [ONCE_REWRITE_TAC[SET_EQ_SUBSET] THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[SUBSET_applied] THEN
        ASM_SIMP_TAC (srw_ss()) [] THEN
        ASM_SIMP_TAC (srw_ss()) [IN_DEF],
        SIMP_TAC (srw_ss()) [SUBSET_applied] THEN REPEAT STRIP_TAC THEN
        FULL_SIMP_TAC (srw_ss()) [IN_DEF]],
      MATCH_MP_TAC OPEN_IN_BIGUNION THEN
      SIMP_TAC (srw_ss()) []]]);

Theorem OPEN_NEIGH:
  !A top.
    open_in(top) A <=> !x:'a. A x ==> ?N. neigh(top)(N,x) /\ N SUBSET A
Proof
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    REPEAT STRIP_TAC THEN simp[neigh, PULL_EXISTS] THEN
    REPEAT (Q.EXISTS_TAC ‘A’) THEN simp[OPEN_IN_SUBSET]
    ,
    DISCH_TAC THEN ONCE_REWRITE_TAC[OPEN_SUBOPEN] THEN REPEAT STRIP_TAC THEN
    first_assum $ drule_then strip_assume_tac THEN gs[neigh] THEN
    metis_tac[SUBSET_TRANS]
  ]
QED

(*---------------------------------------------------------------------------*)
(* Characterize closed sets in a topological space                           *)
(*---------------------------------------------------------------------------*)

Definition closed_in:
  closed_in top s <=>
        s SUBSET (topspace top) /\ open_in top (topspace top DIFF s)
End

(* global (abstract) notion of closed sets *)
Definition closed_DEF: closed (s :'a topology) = (closed_in s) UNIV
End

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

Theorem CLOSED_IN_EMPTY[simp]: !top. closed_in top {}
Proof
  REWRITE_TAC[closed_in, EMPTY_SUBSET, DIFF_EMPTY, OPEN_IN_TOPSPACE]
QED

Theorem CLOSED_IN_TOPSPACE[simp]: !top. closed_in top (topspace top)
Proof
  REWRITE_TAC[closed_in, SUBSET_REFL, DIFF_EQ_EMPTY, OPEN_IN_EMPTY]
QED

Theorem CLOSED_IN_UNION:
 !top s t. closed_in top s /\ closed_in top t ==> closed_in top (s UNION t)
Proof
  SIMP_TAC std_ss [closed_in, UNION_SUBSET, OPEN_IN_INTER,
                   SET_RULE “u DIFF (s UNION t) = (u DIFF s) INTER (u DIFF t)”]
QED

Theorem CLOSED_IN_BIGINTER:
 !top k:('a->bool)->bool.
   k <> {} /\ (!s. s IN k ==> closed_in top s) ==> closed_in top (BIGINTER k)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[closed_in] THEN REPEAT STRIP_TAC THENL
   [REPEAT (POP_ASSUM MP_TAC) THEN SET_TAC[], ALL_TAC] THEN
  SUBGOAL_THEN “topspace top DIFF BIGINTER k :'a->bool =
                BIGUNION {topspace top DIFF s | s IN k}” SUBST1_TAC
  THENL [ALL_TAC,
         MATCH_MP_TAC OPEN_IN_BIGUNION THEN REPEAT (POP_ASSUM MP_TAC) THEN
         SET_TAC[]
  ] THEN simp[Once EXTENSION] THEN
  KNOW_TAC
    “{topspace top DIFF s | s IN k} = IMAGE (\s. topspace top DIFF s) k” THENL
  [FULL_SIMP_TAC std_ss [GSYM IMAGE_DEF], ALL_TAC] THEN DISC_RW_KILL THEN
  REWRITE_TAC [IN_BIGUNION, IN_BIGINTER] THEN
  simp[PULL_EXISTS] THEN METIS_TAC[]
QED

Theorem CLOSED_IN_INTER:
 !top s t. closed_in top s /\ closed_in top t ==> closed_in top (s INTER t)
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM BIGINTER_2] THEN
  MATCH_MP_TAC CLOSED_IN_BIGINTER THEN REPEAT (POP_ASSUM MP_TAC) THEN
  SET_TAC[]
QED

Theorem OPEN_IN_CLOSED_IN_EQ:
 !top s. open_in top s <=>
         s SUBSET topspace top /\ closed_in top (topspace top DIFF s)
Proof
  REWRITE_TAC[closed_in, SET_RULE ``(u DIFF s) SUBSET u``] THEN
  REWRITE_TAC[SET_RULE ``u DIFF (u DIFF s) = u INTER s``] THEN
  PROVE_TAC[OPEN_IN_SUBSET, SET_RULE ``s SUBSET t ==> (t INTER s = s)``]
QED

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

Definition limpt:
  limpt(top) x S' <=>
  x IN topspace top /\
  !N:'a->bool. neigh(top)(N,x) ==> ?y. ~(x = y) /\ S' y /\ N y
End

(* alternative characterisation without needing neigh, but using IN, rather
   than application
 *)
Theorem limpt_thm:
  limpt t x A <=>
  x IN topspace t /\
  !U. open_in t U /\ x IN U ==> ?y. y IN U /\ y IN A /\ y <> x
Proof
  rw[limpt, neigh, PULL_EXISTS] >> EQ_TAC >>
  rw[] >> fs[IN_DEF]
  >- metis_tac[SUBSET_REFL, OPEN_IN_SUBSET]
  >> metis_tac[SUBSET_DEF, IN_DEF]
QED

(*---------------------------------------------------------------------------*)
(* Prove that a set is closed iff it contains all its limit points           *)
(*---------------------------------------------------------------------------*)

Theorem CLOSED_LIMPT:
  !top. closed top ==>
        !S'. closed_in(top) S' <=> !x:'a. limpt(top) x S' ==> S' x
Proof
    GEN_TAC >> DISCH_TAC
 >> IMP_RES_TAC closed_topspace
 >> GEN_TAC >> CONV_TAC (ONCE_DEPTH_CONV CONTRAPOS_CONV)
 >> REWRITE_TAC[closed_in, limpt]
 >> ASM_REWRITE_TAC [SUBSET_UNIV, GSYM COMPL_DEF, IN_UNIV]
 >> CONV_TAC(ONCE_DEPTH_CONV NOT_FORALL_CONV)
 >> ‘!x. S' x = ~COMPL S' x’ by rw [COMPL_applied, IN_APP]
 >> ASM_REWRITE_TAC []
 >> SPEC_TAC(“COMPL(S':'a->bool)”,“S':'a->bool”)
 >> GEN_TAC >> REWRITE_TAC [NOT_IMP]
 >> CONV_TAC (ONCE_DEPTH_CONV NOT_EXISTS_CONV)
 >> REWRITE_TAC [DE_MORGAN_THM]
 >> REWRITE_TAC [OPEN_NEIGH, SUBSET_applied]
 >> AP_TERM_TAC >> ABS_TAC
 >> ASM_CASES_TAC “(S':'a->bool) x” >> ASM_REWRITE_TAC []
 >> METIS_TAC[]
QED

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

Theorem HULL_IMAGE_GALOIS:
  !P f g s. (!s. P(P hull s)) /\
            (!s. P s ==> P(IMAGE f s)) /\ (!s. P s ==> P(IMAGE g s)) /\
            (!s t. s SUBSET IMAGE g t <=> IMAGE f s SUBSET t) ==>
            P hull (IMAGE f s) = IMAGE f (P hull s)
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_SIMP_TAC std_ss [HULL_IMAGE_SUBSET] THEN
  first_assum (REWRITE_TAC o single o GSYM) THEN
  MATCH_MP_TAC HULL_MINIMAL THEN
  ASM_SIMP_TAC std_ss [HULL_SUBSET]
QED

Theorem HULL_IMAGE:
  !P f s. (!s. P(P hull s)) /\ (!s. P(IMAGE f s) <=> P s) /\
          (!x y:'a. (f x = f y) ==> (x = y)) /\ (!y. ?x. f x = y) ==>
          P hull (IMAGE f s) = IMAGE f (P hull s)
Proof
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
  FIRST_X_ASSUM(CONV_TAC o RAND_CONV o REWR_CONV o GSYM) THEN
  MATCH_MP_TAC EQ_IMPLIES THEN AP_TERM_TAC THEN REPEAT (POP_ASSUM MP_TAC) THEN
  SET_TAC[]
QED

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

(* ------------------------------------------------------------------------- *)
(* Subspace topology (from real_topologyTheory)                              *)
(* ------------------------------------------------------------------------- *)

Definition subtopology :
    subtopology top u = topology {s INTER u | open_in top s}
End

Theorem ISTOPOLOGY_SUBTOPOLOGY :
    !top u:'a->bool. istopology {s INTER u | open_in top s}
Proof
  REWRITE_TAC[istopology, SET_RULE
   ``{s INTER u | open_in top s} =
    IMAGE (\s. s INTER u) {s | open_in top s}``] THEN
  SIMP_TAC std_ss [GSYM AND_IMP_INTRO, FORALL_IN_IMAGE, RIGHT_FORALL_IMP_THM] >>
  SIMP_TAC std_ss [SUBSET_IMAGE, IN_IMAGE, GSPECIFICATION, SUBSET_DEF] THEN
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THENL [
    EXISTS_TAC ``{}:'a->bool`` THEN REWRITE_TAC[OPEN_IN_EMPTY, INTER_EMPTY],
    SIMP_TAC std_ss [
        SET_RULE ``(s INTER u) INTER (t INTER u) = (s INTER t) INTER u``] THEN
    ASM_MESON_TAC[OPEN_IN_INTER],
    X_GEN_TAC ``f:('a->bool)->bool`` THEN
    DISCH_THEN (X_CHOOSE_TAC ``g:('a->bool)->bool``) THEN
    EXISTS_TAC ``BIGUNION g :'a->bool`` THEN
    ASM_SIMP_TAC std_ss [OPEN_IN_BIGUNION, INTER_BIGUNION] THEN SET_TAC[]]
QED

Theorem OPEN_IN_SUBTOPOLOGY :
  !top u s. open_in (subtopology top u) s <=>
            ?t. open_in top t /\ (s = t INTER u)
Proof
  REWRITE_TAC[subtopology] THEN
  SIMP_TAC std_ss [
      REWRITE_RULE[CONJUNCT2 topology_tybij] ISTOPOLOGY_SUBTOPOLOGY] THEN
  simp[] THEN METIS_TAC []
QED

Theorem TOPSPACE_SUBTOPOLOGY[simp]:
  !top u. topspace(subtopology top u) = topspace top INTER u
Proof
  REWRITE_TAC[topspace, OPEN_IN_SUBTOPOLOGY, INTER_BIGUNION] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN simp[Once EXTENSION] THEN
  METIS_TAC []
QED

Theorem CLOSED_IN_SUBTOPOLOGY :
    !top u s. closed_in (subtopology top u) s <=>
              ?t:'a->bool. closed_in top t /\ (s = t INTER u)
Proof
  REWRITE_TAC[closed_in, TOPSPACE_SUBTOPOLOGY] THEN
  SIMP_TAC std_ss [SUBSET_INTER,OPEN_IN_SUBTOPOLOGY,GSYM RIGHT_EXISTS_AND_THM]>>
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN ``t:'a->bool`` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC ``topspace top DIFF t :'a->bool`` THEN
  ASM_SIMP_TAC std_ss [CLOSED_IN_TOPSPACE, OPEN_IN_DIFF, CLOSED_IN_DIFF,
               OPEN_IN_TOPSPACE] THEN
  REPEAT (POP_ASSUM MP_TAC) THEN SET_TAC[]
QED

Theorem OPEN_IN_SUBTOPOLOGY_EMPTY[simp]:
    !top s. open_in (subtopology top {}) s <=> (s = {})
Proof
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY, INTER_EMPTY] THEN
  MESON_TAC[OPEN_IN_EMPTY]
QED

Theorem CLOSED_IN_SUBTOPOLOGY_EMPTY[simp]:
    !top s. closed_in (subtopology top {}) s <=> (s = {})
Proof
  REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY, INTER_EMPTY] THEN
  MESON_TAC[CLOSED_IN_EMPTY]
QED

Theorem OPEN_IN_SUBTOPOLOGY_REFL[simp]:
    !top u:'a->bool. open_in (subtopology top u) u <=> u SUBSET topspace top
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE ``s SUBSET u ==> s INTER t SUBSET u``) THEN
    ASM_SIMP_TAC std_ss [OPEN_IN_SUBSET],
    DISCH_TAC THEN EXISTS_TAC ``topspace top:'a->bool`` THEN
    REWRITE_TAC[OPEN_IN_TOPSPACE] THEN REPEAT (POP_ASSUM MP_TAC) THEN SET_TAC[]]
QED

Theorem CLOSED_IN_SUBTOPOLOGY_REFL[simp]:
    !top u:'a->bool. closed_in (subtopology top u) u <=> u SUBSET topspace top
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY] THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE ``s SUBSET u ==> s INTER t SUBSET u``) THEN
    ASM_SIMP_TAC std_ss [CLOSED_IN_SUBSET],
    DISCH_TAC THEN EXISTS_TAC ``topspace top:'a->bool`` THEN
    REWRITE_TAC[CLOSED_IN_TOPSPACE] THEN REPEAT (POP_ASSUM MP_TAC) THEN
    SET_TAC[]]
QED

Theorem SUBTOPOLOGY_SUPERSET :
    !top s:'a->bool. topspace top SUBSET s ==> (subtopology top s = top)
Proof
  REPEAT GEN_TAC THEN SIMP_TAC std_ss [TOPOLOGY_EQ, OPEN_IN_SUBTOPOLOGY] THEN
  DISCH_TAC THEN X_GEN_TAC ``u:'a->bool`` THEN EQ_TAC THENL
   [DISCH_THEN(CHOOSE_THEN(CONJUNCTS_THEN2 MP_TAC SUBST1_TAC)) THEN
    DISCH_THEN(fn th => MP_TAC th THEN
      ASSUME_TAC(MATCH_MP OPEN_IN_SUBSET th)) THEN
    MATCH_MP_TAC EQ_IMPLIES THEN AP_TERM_TAC THEN REPEAT (POP_ASSUM MP_TAC) THEN
    SET_TAC[],
    DISCH_TAC THEN EXISTS_TAC ``u:'a->bool`` THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    REPEAT (POP_ASSUM MP_TAC) THEN SET_TAC[]]
QED

Theorem SUBTOPOLOGY_TOPSPACE[simp]:
    !top. subtopology top (topspace top) = top
Proof
  SIMP_TAC std_ss [SUBTOPOLOGY_SUPERSET, SUBSET_REFL]
QED

Theorem SUBTOPOLOGY_UNIV[simp]:
    !top. subtopology top UNIV = top
Proof
  SIMP_TAC std_ss [SUBTOPOLOGY_SUPERSET, SUBSET_UNIV]
QED

Theorem OPEN_IN_IMP_SUBSET :
    !top s t. open_in (subtopology top s) t ==> t SUBSET s
Proof
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN SET_TAC[]
QED

Theorem CLOSED_IN_IMP_SUBSET :
    !top s t. closed_in (subtopology top s) t ==> t SUBSET s
Proof
  REWRITE_TAC[closed_in, TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[]
QED

Theorem OPEN_IN_SUBTOPOLOGY_UNION :
   !top s t u:'a->bool.
        open_in (subtopology top t) s /\ open_in (subtopology top u) s
        ==> open_in (subtopology top (t UNION u)) s
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN ``s':'a->bool`` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN ``t':'a->bool`` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC ``s' INTER t':'a->bool`` >> ASM_SIMP_TAC std_ss [OPEN_IN_INTER] >>
  REPEAT (POP_ASSUM MP_TAC) THEN SET_TAC[]
QED

Theorem CLOSED_IN_SUBTOPOLOGY_UNION :
    !top s t u:'a->bool.
        closed_in (subtopology top t) s /\ closed_in (subtopology top u) s
        ==> closed_in (subtopology top (t UNION u)) s
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN ``s':'a->bool`` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN ``t':'a->bool`` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC ``s' INTER t':'a->bool`` >> ASM_SIMP_TAC std_ss [CLOSED_IN_INTER]>>
  REPEAT (POP_ASSUM MP_TAC) THEN SET_TAC[]
QED

Theorem SUBTOPOLOGY_SUBTOPOLOGY[simp] :
   !top s t:'a->bool.
        subtopology (subtopology top s) t = subtopology top (s INTER t)
Proof
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[subtopology] THEN
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
  SIMP_TAC std_ss [SET_RULE ``{f x | ?y. P y /\ x = g y} = {f(g y) | P y}``] THEN
  REWRITE_TAC[INTER_ASSOC]
QED

(* ------------------------------------------------------------------------- *)
(* HOL Light compatibility layer (sets.ml)                                   *)
(* ------------------------------------------------------------------------- *)

(* moved here from util_probTheory *)
Theorem EXT_SKOLEM_THM :
    !P Q. (!x. x IN P ==> ?y. Q x y) <=> ?f. !x. x IN P ==> Q x (f x)
Proof
    rpt STRIP_TAC
 >> reverse EQ_TAC >> rpt STRIP_TAC
 >- (Q.EXISTS_TAC `f x` \\
     FIRST_X_ASSUM MATCH_MP_TAC >> rw [])
 >> fs [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]
 >> Q.EXISTS_TAC `f` >> rw []
QED

(* applied version, used in ‘example/probability’ *)
Theorem EXT_SKOLEM_THM' = REWRITE_RULE [IN_APP] EXT_SKOLEM_THM

(* HOL Light compatibility layer (sets.ml) *)
Overload UNIONS[inferior] = “BIGUNION”
Overload INTERS[inferior] = “BIGINTER”

Theorem COUNTABLE_SUBSET_NUM = COUNTABLE_NUM
Theorem FINITE_IMAGE         = IMAGE_FINITE
Theorem IN_INTERS            = IN_BIGINTER
Theorem IN_UNIONS            = IN_BIGUNION
Theorem INTER_UNIONS         = INTER_BIGUNION
Theorem INTERS_0             = BIGINTER_EMPTY
Theorem INTERS_1             = BIGINTER_SING
Theorem INTERS_2             = BIGINTER_2
Theorem INTERS_INSERT        = BIGINTER_INSERT
Theorem UNIONS_0             = BIGUNION_EMPTY
Theorem UNIONS_1             = BIGUNION_SING
Theorem UNIONS_2             = BIGUNION_2
Theorem UNIONS_UNION         = BIGUNION_UNION
Theorem UNIONS_INSERT        = BIGUNION_INSERT
Theorem UNIONS_SUBSET        = BIGUNION_SUBSET

Theorem EMPTY_GSPEC :
   {x | F} = {}
Proof SET_TAC[]
QED

Theorem UNIV_GSPEC :
   {x | T} = UNIV
Proof SET_TAC[]
QED

Theorem SING_GSPEC :
   (!a. {x | x = a} = {a}) /\ (!a. {x | a = x} = {a})
Proof SET_TAC[]
QED

Theorem IN_GSPEC :
   !s. {x | x IN s} = s
Proof SET_TAC[]
QED

Theorem SUBSET_RESTRICT :
   !s P. {x | x IN s /\ P x} SUBSET s
Proof SET_TAC []
QED

(* This version is considered as "applied" as ‘COMPL’ itself doesn't appear:

   |- !s. univ(:'a) DIFF (univ(:'a) DIFF s) = s
 *)
Theorem COMPL_COMPL_applied = REWRITE_RULE [COMPL_DEF] COMPL_COMPL

(* |- !f s. {f x | x IN s} = IMAGE f s *)
Theorem SIMPLE_IMAGE = GSYM IMAGE_DEF

Theorem UNIONS_IMAGE :
   !f s. UNIONS (IMAGE f s) = {y | ?x. x IN s /\ y IN f x}
Proof
    rpt GEN_TAC
 >> rw [Once EXTENSION]
 >> EQ_TAC >> rw [] >> rename1 ‘x IN f t’
 >- (Q.EXISTS_TAC ‘t’ >> rw [])
 >> Q.EXISTS_TAC ‘f t’ >> rw []
 >> Q.EXISTS_TAC ‘t’ >> rw []
QED

Theorem INTERS_IMAGE :
   !f s. INTERS (IMAGE f s) = {y | !x. x IN s ==> y IN f x}
Proof
    rpt GEN_TAC
 >> rw [Once EXTENSION]
 >> EQ_TAC >> rw [] >> rename1 ‘x IN f t’
 >- (FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘t’ >> rw [])
 >> FIRST_X_ASSUM MATCH_MP_TAC >> rw []
QED

Theorem DIFF_INTERS :
   !u s. u DIFF INTERS s = UNIONS {u DIFF t | t IN s}
Proof
    rpt GEN_TAC
 >> rw [Once EXTENSION]
 >> EQ_TAC >> rw []
 >- (Q.EXISTS_TAC ‘u DIFF P’ >> rw [] \\
     Q.EXISTS_TAC ‘P’ >> rw [])
 >- fs []
 >> Q.EXISTS_TAC ‘t’ >> fs []
QED

Theorem INTERS_GSPEC :
   (!P f. INTERS {f x | P x} = {a | !x. P x ==> a IN (f x)}) /\
   (!P f. INTERS {f x y | P x y} = {a | !x y. P x y ==> a IN (f x y)}) /\
   (!P f. INTERS {f x y z | P x y z} =
                {a | !x y z. P x y z ==> a IN (f x y z)})
Proof
  rpt STRIP_TAC >> GEN_REWRITE_TAC I empty_rewrites [EXTENSION] \\
  rw [IN_INTERS] >> MESON_TAC []
QED

Theorem UNIONS_GSPEC :
   (!P f. UNIONS {f x | P x} = {a | ?x. P x /\ a IN (f x)}) /\
   (!P f. UNIONS {f x y | P x y} = {a | ?x y. P x y /\ a IN (f x y)}) /\
   (!P f. UNIONS {f x y z | P x y z} =
            {a | ?x y z. P x y z /\ a IN (f x y z)})
Proof
  rpt STRIP_TAC >> GEN_REWRITE_TAC I empty_rewrites [EXTENSION] \\
  rw [IN_UNIONS] >> MESON_TAC []
QED

Theorem INTER_INTERS :
   (!f s:'a->bool. s INTER INTERS f =
           if f = {} then s else INTERS {s INTER t | t IN f}) /\
   (!f s:'a->bool. INTERS f INTER s =
           if f = {} then s else INTERS {t INTER s | t IN f})
Proof
    CONJ_ASM1_TAC
 >- (rpt STRIP_TAC THEN COND_CASES_TAC THEN
     ASM_SIMP_TAC std_ss [INTERS_0, INTER_UNIV, INTERS_GSPEC] THEN
     rw [Once EXTENSION, IN_INTERS] \\
     EQ_TAC >> rw [] \\
     fs [GSYM MEMBER_NOT_EMPTY] >> PROVE_TAC [])
 >> POP_ASSUM (ACCEPT_TAC o (ONCE_REWRITE_RULE [INTER_COMM]))
QED

Theorem INTERS_UNIONS :
   !s. INTERS s = UNIV DIFF (UNIONS {UNIV DIFF t | t IN s})
Proof
  REWRITE_TAC[GSYM DIFF_INTERS] THEN SET_TAC[]
QED

Theorem UNIONS_INTERS :
   !s. UNIONS s = UNIV DIFF (INTERS {UNIV DIFF t | t IN s})
Proof
    GEN_TAC
 >> rw [Once EXTENSION]
 >> EQ_TAC >> rw []
 >- (rename1 ‘x IN t’ \\
     Q.EXISTS_TAC ‘univ(:'a) DIFF t’ \\
     rw [] >> Q.EXISTS_TAC ‘t’ >> rw [])
 >> fs []
 >> Q.EXISTS_TAC ‘t’ >> rw []
QED

(* NOTE: HOL4's BIGINTER_SUBSET doesn't have ‘u <> {}’ *)
Theorem INTERS_SUBSET :
   !u s:'a->bool.
    ~(u = {}) /\ (!t. t IN u ==> t SUBSET s) ==> INTERS u SUBSET s
Proof
  SET_TAC[]
QED

(* essentially same as HOL4's BIGINTER_SUBSET but looks more reasonable *)
Theorem INTERS_SUBSET_STRONG :
   !u s:'a->bool. (?t. t IN u /\ t SUBSET s) ==> INTERS u SUBSET s
Proof
  SET_TAC[]
QED

Theorem DIFF_UNIONS :
   !u s. u DIFF UNIONS s = u INTER INTERS {u DIFF t | t IN s}
Proof
  SIMP_TAC std_ss [INTERS_GSPEC] THEN SET_TAC[]
QED

Theorem DIFF_UNIONS_NONEMPTY :
   !u s. ~(s = {}) ==> u DIFF UNIONS s = INTERS {u DIFF t | t IN s}
Proof
  SIMP_TAC std_ss [INTERS_GSPEC] THEN SET_TAC[]
QED

(* ------------------------------------------------------------------------- *)
(* Pairwise property over sets and lists (from real_topologyTheory)          *)
(* ------------------------------------------------------------------------- *)

val _ = hide "pairwise"; (* pred_setTheory *)

(* NOTE: this definition is HOL-Light compatible, originally from "sets.ml". *)
val pairwise = new_definition ("pairwise",
  ``pairwise r s <=> !x y. x IN s /\ y IN s /\ ~(x = y) ==> r x y``);

Overload pairwiseD        = “topology$pairwise”
Overload pairwiseN[local] = “pred_set$pairwise”

(* connection between pairwiseD and pairwiseN, originally by Michael Norrish *)
Theorem pairwiseD_alt_pairwiseN :
    !R. pairwiseD R = pairwiseN (RC R)
Proof
    RW_TAC std_ss [FUN_EQ_THM, pairwise, pairwise_def, RC_DEF]
 >> METIS_TAC []
QED

Theorem PAIRWISE_EMPTY :
   !r. pairwise r {} <=> T
Proof
   rw [pairwiseD_alt_pairwiseN, pairwise_EMPTY]
QED

Theorem PAIRWISE_SING :
   !r x. pairwise r {x} <=> T
Proof
  REWRITE_TAC[pairwise, IN_SING] THEN MESON_TAC[]
QED

Theorem PAIRWISE_IMP :
   !P Q s.
        pairwise P s /\
        (!x y. x IN s /\ y IN s /\ P x y /\ ~(x = y) ==> Q x y)
        ==> pairwise Q s
Proof
  REWRITE_TAC[pairwise] THEN SET_TAC[]
QED

Theorem PAIRWISE_MONO :
   !r s t. pairwise r s /\ t SUBSET s ==> pairwise r t
Proof
  REWRITE_TAC[pairwise] THEN SET_TAC[]
QED

Theorem PAIRWISE_AND :
   !R R' s. pairwise R s /\ pairwise R' s <=>
            pairwise (\x y. R x y /\ R' x y) s
Proof
  REWRITE_TAC[pairwise] THEN SET_TAC[]
QED

Theorem PAIRWISE_INSERT :
   !r x s.
        pairwise r (x INSERT s) <=>
        (!y. y IN s /\ ~(y = x) ==> r x y /\ r y x) /\
        pairwise r s
Proof
  REWRITE_TAC[pairwise, IN_INSERT] THEN MESON_TAC[]
QED

Theorem PAIRWISE_IMAGE :
   !r f. pairwise r (IMAGE f s) <=>
         pairwise (\x y. ~(f x = f y) ==> r (f x) (f y)) s
Proof
  REWRITE_TAC[pairwise, IN_IMAGE] THEN MESON_TAC[]
QED

Theorem PAIRWISE_UNION :
   !R s t. pairwise R (s UNION t) <=>
           pairwise R s /\ pairwise R t /\
           (!x y. x IN s DIFF t /\ y IN t DIFF s ==> R x y /\ R y x)
Proof
  REWRITE_TAC[pairwise] THEN SET_TAC[]
QED

(* ------------------------------------------------------------------------- *)
(* Useful idioms for being a suitable union/intersection of somethings.      *)
(* (ported from HOL Light)                                                   *)
(* ------------------------------------------------------------------------- *)

val _ = set_fixity "UNION_OF"        (Infixr 601);
val _ = set_fixity "INTERSECTION_OF" (Infixr 601);

Definition UNION_OF :
   P UNION_OF Q = \s. ?u. P u /\ (!c. c IN u ==> Q c) /\ UNIONS u = s
End

Definition INTERSECTION_OF :
   P INTERSECTION_OF Q = \s. ?u. P u /\ (!c. c IN u ==> Q c) /\ INTERS u = s
End

Theorem UNION_OF_INC :
   !P Q s:'a->bool. P {s} /\ Q s ==> (P UNION_OF Q) s
Proof
  REPEAT STRIP_TAC THEN SIMP_TAC std_ss [UNION_OF] THEN
  Q.EXISTS_TAC `{s:'a->bool}` THEN ASM_SIMP_TAC std_ss [UNIONS_1, IN_SING]
QED

Theorem INTERSECTION_OF_INC :
   !P Q s:'a->bool. P {s} /\ Q s ==> (P INTERSECTION_OF Q) s
Proof
  REPEAT STRIP_TAC THEN SIMP_TAC std_ss [INTERSECTION_OF] THEN
  Q.EXISTS_TAC `{s:'a->bool}` THEN ASM_SIMP_TAC std_ss [INTERS_1, IN_SING]
QED

Theorem UNION_OF_MONO :
   !P Q Q' s:'a->bool.
        (P UNION_OF Q) s /\ (!x. Q x ==> Q' x) ==> (P UNION_OF Q') s
Proof
  SIMP_TAC std_ss [UNION_OF] THEN MESON_TAC[]
QED

Theorem INTERSECTION_OF_MONO :
   !P Q Q' s:'a->bool.
        (P INTERSECTION_OF Q) s /\ (!x. Q x ==> Q' x)
        ==> (P INTERSECTION_OF Q') s
Proof
  SIMP_TAC std_ss [INTERSECTION_OF] THEN MESON_TAC[]
QED

Theorem FORALL_UNION_OF :
   (!s. (P UNION_OF Q) s ==> R s) <=>
   (!t. P t /\ (!c. c IN t ==> Q c) ==> R(UNIONS t))
Proof
  SIMP_TAC std_ss [UNION_OF] THEN MESON_TAC[]
QED

Theorem FORALL_INTERSECTION_OF :
   (!s. (P INTERSECTION_OF Q) s ==> R s) <=>
   (!t. P t /\ (!c. c IN t ==> Q c) ==> R(INTERS t))
Proof
  SIMP_TAC std_ss [INTERSECTION_OF] THEN MESON_TAC[]
QED

Theorem UNION_OF_EMPTY :
   !P Q:('a->bool)->bool. P {} ==> (P UNION_OF Q) {}
Proof
  REPEAT STRIP_TAC THEN SIMP_TAC std_ss [UNION_OF] THEN
  Q.EXISTS_TAC `{}:('a->bool)->bool` THEN
  ASM_SIMP_TAC std_ss [UNIONS_0, NOT_IN_EMPTY]
QED

Theorem INTERSECTION_OF_EMPTY :
   !P Q:('a->bool)->bool. P {} ==> (P INTERSECTION_OF Q) UNIV
Proof
  REPEAT STRIP_TAC THEN SIMP_TAC std_ss [INTERSECTION_OF] THEN
  Q.EXISTS_TAC `{}:('a->bool)->bool` THEN
  ASM_SIMP_TAC std_ss [INTERS_0, NOT_IN_EMPTY]
QED

(* ------------------------------------------------------------------------- *)
(* The ARBITRARY and FINITE cases of UNION_OF / INTERSECTION_OF              *)
(* ------------------------------------------------------------------------- *)

Definition ARBITRARY :
    ARBITRARY (s:('a->bool)->bool) <=> T
End

Theorem ARBITRARY_UNION_OF_ALT :
   !B s:'a->bool.
        (ARBITRARY UNION_OF B) s <=>
        !x. x IN s ==>  ?u. u IN B /\ x IN u /\ u SUBSET s
Proof
  GEN_TAC THEN SIMP_TAC std_ss [FORALL_AND_THM, TAUT
   `(p <=> q) <=> (p ==> q) /\ (q ==> p)`] THEN
  SIMP_TAC std_ss [FORALL_UNION_OF, ARBITRARY] THEN
  CONJ_TAC THENL [SET_TAC[], ALL_TAC] THEN
  Q.X_GEN_TAC `s:'a->bool` THEN DISCH_TAC THEN
  SIMP_TAC std_ss [ARBITRARY, UNION_OF] THEN
  Q.EXISTS_TAC `{u:'a->bool | u IN B /\ u SUBSET s}` THEN ASM_SET_TAC[]
QED

Theorem ARBITRARY_UNION_OF_EMPTY :
   !P:('a->bool)->bool. (ARBITRARY UNION_OF P) {}
Proof
  SIMP_TAC std_ss [UNION_OF_EMPTY, ARBITRARY]
QED

Theorem ARBITRARY_INTERSECTION_OF_EMPTY :
   !P:('a->bool)->bool. (ARBITRARY INTERSECTION_OF P) UNIV
Proof
  SIMP_TAC std_ss [INTERSECTION_OF_EMPTY, ARBITRARY]
QED

Theorem ARBITRARY_UNION_OF_INC :
   !P s:'a->bool. P s ==> (ARBITRARY UNION_OF P) s
Proof
  SIMP_TAC std_ss [UNION_OF_INC, ARBITRARY]
QED

Theorem ARBITRARY_INTERSECTION_OF_INC :
   !P s:'a->bool. P s ==> (ARBITRARY INTERSECTION_OF P) s
Proof
  SIMP_TAC std_ss [INTERSECTION_OF_INC, ARBITRARY]
QED

Theorem ARBITRARY_UNION_OF_COMPLEMENT :
   !P s. (ARBITRARY UNION_OF P) s <=>
         (ARBITRARY INTERSECTION_OF (\s. P(univ(:'a) DIFF s))) (univ(:'a) DIFF s)
Proof
  REPEAT GEN_TAC THEN SIMP_TAC std_ss [UNION_OF, INTERSECTION_OF] THEN
  EQ_TAC THEN
  DISCH_THEN(Q.X_CHOOSE_THEN `u:('a->bool)->bool` STRIP_ASSUME_TAC) THEN
  Q.EXISTS_TAC `IMAGE (\c. univ(:'a) DIFF c) u` THEN
  ASM_SIMP_TAC std_ss [ARBITRARY, FORALL_IN_IMAGE, COMPL_COMPL_applied] THEN
  ONCE_REWRITE_TAC [UNIONS_INTERS, INTERS_UNIONS] THEN
  SIMP_TAC std_ss [SET_RULE ``{f y | y IN IMAGE g s} = IMAGE (\x. f(g x)) s``] THEN
  ASM_SIMP_TAC std_ss [IMAGE_ID, COMPL_COMPL_applied]
QED

Theorem ARBITRARY_INTERSECTION_OF_COMPLEMENT :
   !P s. (ARBITRARY INTERSECTION_OF P) s <=>
         (ARBITRARY UNION_OF (\s. P(univ(:'a) DIFF s))) (univ(:'a) DIFF s)
Proof
  SIMP_TAC std_ss [ARBITRARY_UNION_OF_COMPLEMENT] THEN
  SIMP_TAC std_ss [ETA_AX, COMPL_COMPL_applied]
QED

Theorem ARBITRARY_UNION_OF_IDEMPOT :
   !P:('a->bool)->bool.
        ARBITRARY UNION_OF ARBITRARY UNION_OF P = ARBITRARY UNION_OF P
Proof
  GEN_TAC THEN SIMP_TAC std_ss [FUN_EQ_THM] THEN Q.X_GEN_TAC `s:'a->bool` THEN
  EQ_TAC THEN SIMP_TAC std_ss [ARBITRARY_UNION_OF_INC] THEN
  SIMP_TAC std_ss [UNION_OF, LEFT_IMP_EXISTS_THM] THEN
  Q.X_GEN_TAC `u:('a->bool)->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM)) THEN
  rw [EXT_SKOLEM_THM] \\
  Q.EXISTS_TAC
    `IMAGE SND {(s,t) | s IN u /\ t IN (f:('a->bool)->('a->bool)->bool) s}` THEN
  ASM_SIMP_TAC std_ss [ARBITRARY] THEN
  SIMP_TAC std_ss [FORALL_IN_IMAGE, FORALL_IN_GSPEC] THEN
  CONJ_TAC THENL [ASM_SET_TAC[], SIMP_TAC std_ss [UNIONS_IMAGE]] THEN
  SIMP_TAC std_ss [EXISTS_IN_GSPEC] THEN ASM_SET_TAC[]
QED

Theorem ARBITRARY_INTERSECTION_OF_IDEMPOT :
   !P:('a->bool)->bool.
        ARBITRARY INTERSECTION_OF ARBITRARY INTERSECTION_OF P =
        ARBITRARY INTERSECTION_OF P
Proof
    RW_TAC (std_ss ++ ETA_ss) [FUN_EQ_THM, COMPL_COMPL_applied,
                               ARBITRARY_INTERSECTION_OF_COMPLEMENT]
 >> SIMP_TAC std_ss [ARBITRARY_UNION_OF_IDEMPOT]
QED

Theorem ARBITRARY_UNION_OF_UNIONS :
   !P u:('a->bool)->bool.
        (!s. s IN u ==> (ARBITRARY UNION_OF P) s)
        ==> (ARBITRARY UNION_OF P) (UNIONS u)
Proof
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [GSYM ARBITRARY_UNION_OF_IDEMPOT] THEN
  ONCE_REWRITE_TAC [UNION_OF] THEN SIMP_TAC std_ss [] THEN
  Q.EXISTS_TAC `u:('a->bool)->bool` THEN ASM_SIMP_TAC std_ss [ARBITRARY]
QED

Theorem ARBITRARY_UNION_OF_UNION :
   !P s t. (ARBITRARY UNION_OF P) s /\ (ARBITRARY UNION_OF P) t
           ==> (ARBITRARY UNION_OF P) (s UNION t)
Proof
  REPEAT STRIP_TAC THEN SIMP_TAC std_ss [GSYM UNIONS_2] THEN
  MATCH_MP_TAC ARBITRARY_UNION_OF_UNIONS THEN
  ASM_SIMP_TAC std_ss [ARBITRARY, FORALL_IN_INSERT] THEN
  SIMP_TAC std_ss [ARBITRARY, NOT_IN_EMPTY]
QED

Theorem ARBITRARY_INTERSECTION_OF_INTERS :
   !P u:('a->bool)->bool.
        (!s. s IN u ==> (ARBITRARY INTERSECTION_OF P) s)
        ==> (ARBITRARY INTERSECTION_OF P) (INTERS u)
Proof
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM ARBITRARY_INTERSECTION_OF_IDEMPOT] THEN
  ONCE_REWRITE_TAC [INTERSECTION_OF] THEN SIMP_TAC std_ss [] THEN
  Q.EXISTS_TAC `u:('a->bool)->bool` THEN ASM_SIMP_TAC std_ss [ARBITRARY]
QED

Theorem ARBITRARY_INTERSECTION_OF_INTER :
   !P s t. (ARBITRARY INTERSECTION_OF P) s /\ (ARBITRARY INTERSECTION_OF P) t
           ==> (ARBITRARY INTERSECTION_OF P) (s INTER t)
Proof
  REPEAT STRIP_TAC THEN SIMP_TAC std_ss [GSYM INTERS_2] THEN
  MATCH_MP_TAC ARBITRARY_INTERSECTION_OF_INTERS THEN
  ASM_SIMP_TAC std_ss [ARBITRARY, FORALL_IN_INSERT] THEN
  SIMP_TAC std_ss [ARBITRARY, NOT_IN_EMPTY]
QED

Theorem ARBITRARY_UNION_OF_INTER_EQ :
   !P:('a->bool)->bool.
        (!s t. (ARBITRARY UNION_OF P) s /\ (ARBITRARY UNION_OF P) t
               ==> (ARBITRARY UNION_OF P) (s INTER t)) <=>
        (!s t. P s /\ P t ==> (ARBITRARY UNION_OF P) (s INTER t))
Proof
  GEN_TAC THEN
  EQ_TAC THENL [MESON_TAC[ARBITRARY_UNION_OF_INC], DISCH_TAC] THEN
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [UNION_OF] THEN
  SIMP_TAC std_ss [] THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  ASM_SIMP_TAC std_ss [INTER_UNIONS] THEN
  REPLICATE_TAC 2
   (MATCH_MP_TAC ARBITRARY_UNION_OF_UNIONS THEN
    ASM_SIMP_TAC std_ss [SIMPLE_IMAGE, ARBITRARY, FORALL_IN_IMAGE] THEN
    REPEAT STRIP_TAC)
QED

Theorem ARBITRARY_UNION_OF_INTER :
   !P:('a->bool)->bool.
        (!s t. P s /\ P t ==> P(s INTER t))
        ==> (!s t. (ARBITRARY UNION_OF P) s /\ (ARBITRARY UNION_OF P) t
                   ==> (ARBITRARY UNION_OF P) (s INTER t))
Proof
  RW_TAC std_ss [ARBITRARY_UNION_OF_INTER_EQ,
                 ARBITRARY_UNION_OF_INC]
QED

Theorem ARBITRARY_INTERSECTION_OF_UNION_EQ :
   !P:('a->bool)->bool.
        (!s t. (ARBITRARY INTERSECTION_OF P) s /\
               (ARBITRARY INTERSECTION_OF P) t
               ==> (ARBITRARY INTERSECTION_OF P) (s UNION t)) <=>
        (!s t. P s /\ P t ==> (ARBITRARY INTERSECTION_OF P) (s UNION t))
Proof
  ONCE_REWRITE_TAC [ARBITRARY_INTERSECTION_OF_COMPLEMENT] THEN
  SIMP_TAC std_ss [SET_RULE
    ``UNIV DIFF (s UNION t) = (UNIV DIFF s) INTER (UNIV DIFF t)``] THEN
  SIMP_TAC std_ss [MESON[COMPL_COMPL_applied] ``(!s. P(UNIV DIFF s)) <=> (!s. P s)``] THEN
  SIMP_TAC std_ss [ARBITRARY_UNION_OF_INTER_EQ] THEN
  SIMP_TAC std_ss [SET_RULE
   ``s INTER t = UNIV DIFF ((UNIV DIFF s) UNION (UNIV DIFF t))``] THEN
  SIMP_TAC std_ss [MESON[COMPL_COMPL_applied] ``(!s. P(UNIV DIFF s)) <=> (!s. P s)``] THEN
  SIMP_TAC std_ss [COMPL_COMPL_applied]
QED

Theorem ARBITRARY_INTERSECTION_OF_UNION :
   !P:('a->bool)->bool.
        (!s t. P s /\ P t ==> P(s UNION t))
        ==> (!s t. (ARBITRARY INTERSECTION_OF P) s /\
                   (ARBITRARY INTERSECTION_OF P) t
                   ==> (ARBITRARY INTERSECTION_OF P) (s UNION t))
Proof
  SIMP_TAC std_ss [ARBITRARY_INTERSECTION_OF_UNION_EQ] THEN
  MESON_TAC[ARBITRARY_INTERSECTION_OF_INC]
QED

Theorem FINITE_UNION_OF_EMPTY :
   !P:('a->bool)->bool. (FINITE UNION_OF P) {}
Proof
  SIMP_TAC std_ss [UNION_OF_EMPTY, FINITE_EMPTY]
QED

Theorem FINITE_INTERSECTION_OF_EMPTY :
   !P:('a->bool)->bool. (FINITE INTERSECTION_OF P) UNIV
Proof
  SIMP_TAC std_ss [INTERSECTION_OF_EMPTY, FINITE_EMPTY]
QED

Theorem FINITE_UNION_OF_INC :
   !P s:'a->bool. P s ==> (FINITE UNION_OF P) s
Proof
  SIMP_TAC std_ss [UNION_OF_INC, FINITE_SING]
QED

Theorem FINITE_INTERSECTION_OF_INC :
   !P s:'a->bool. P s ==> (FINITE INTERSECTION_OF P) s
Proof
  SIMP_TAC std_ss [INTERSECTION_OF_INC, FINITE_SING]
QED

Theorem FINITE_UNION_OF_COMPLEMENT :
   !P s. (FINITE UNION_OF P) s <=>
         (FINITE INTERSECTION_OF (\s. P(univ(:'a) DIFF s))) (univ(:'a) DIFF s)
Proof
  REPEAT GEN_TAC THEN SIMP_TAC std_ss [UNION_OF, INTERSECTION_OF] THEN
  EQ_TAC THEN
  DISCH_THEN(Q.X_CHOOSE_THEN `u:('a->bool)->bool` STRIP_ASSUME_TAC) THEN
  Q.EXISTS_TAC `IMAGE (\c. univ(:'a) DIFF c) u` THEN
  ASM_SIMP_TAC std_ss [FINITE_IMAGE, FORALL_IN_IMAGE, COMPL_COMPL_applied] THEN
  ONCE_REWRITE_TAC [UNIONS_INTERS, INTERS_UNIONS] THEN
  SIMP_TAC std_ss [SET_RULE ``{f y | y IN IMAGE g s} = IMAGE (\x. f(g x)) s``] THEN
  ASM_SIMP_TAC std_ss [IMAGE_ID, COMPL_COMPL_applied]
QED

Theorem FINITE_INTERSECTION_OF_COMPLEMENT :
   !P s. (FINITE INTERSECTION_OF P) s <=>
         (FINITE UNION_OF (\s. P(univ(:'a) DIFF s))) (univ(:'a) DIFF s)
Proof
  SIMP_TAC std_ss [FINITE_UNION_OF_COMPLEMENT] THEN
  SIMP_TAC (std_ss ++ ETA_ss) [COMPL_COMPL_applied]
QED

Theorem FINITE_UNION_OF_IDEMPOT :
   !P:('a->bool)->bool.
        FINITE UNION_OF FINITE UNION_OF P = FINITE UNION_OF P
Proof
  GEN_TAC THEN SIMP_TAC std_ss [FUN_EQ_THM] THEN Q.X_GEN_TAC `s:'a->bool` THEN
  EQ_TAC THEN SIMP_TAC std_ss [FINITE_UNION_OF_INC] THEN
  SIMP_TAC std_ss [UNION_OF, LEFT_IMP_EXISTS_THM] THEN
  Q.X_GEN_TAC `u:('a->bool)->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM)) THEN
  rw [EXT_SKOLEM_THM] \\
  Q.EXISTS_TAC
    `IMAGE SND {(s,t) | s IN u /\ t IN (f:('a->bool)->('a->bool)->bool) s}` THEN

  ASM_SIMP_TAC std_ss [FINITE_IMAGE, FINITE_PRODUCT_DEPENDENT] THEN
  SIMP_TAC std_ss [FORALL_IN_IMAGE, FORALL_IN_GSPEC] THEN
  CONJ_TAC THENL [ASM_SET_TAC[], SIMP_TAC std_ss [UNIONS_IMAGE]] THEN
  SIMP_TAC std_ss [EXISTS_IN_GSPEC] THEN ASM_SET_TAC[]
QED

Theorem FINITE_INTERSECTION_OF_IDEMPOT :
   !P:('a->bool)->bool.
        FINITE INTERSECTION_OF FINITE INTERSECTION_OF P =
        FINITE INTERSECTION_OF P
Proof
  RW_TAC (std_ss ++ ETA_ss) [FUN_EQ_THM, COMPL_COMPL_applied,
                             FINITE_INTERSECTION_OF_COMPLEMENT] THEN
  SIMP_TAC std_ss [FINITE_UNION_OF_IDEMPOT]
QED

Theorem FINITE_UNION_OF_UNIONS :
   !P u:('a->bool)->bool.
        FINITE u /\ (!s. s IN u ==> (FINITE UNION_OF P) s)
        ==> (FINITE UNION_OF P) (UNIONS u)
Proof
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [GSYM FINITE_UNION_OF_IDEMPOT] THEN
  ONCE_REWRITE_TAC [UNION_OF] THEN SIMP_TAC std_ss [] THEN
  Q.EXISTS_TAC `u:('a->bool)->bool` THEN ASM_SIMP_TAC std_ss []
QED

Theorem FINITE_UNION_OF_UNION :
    !P s t. (FINITE UNION_OF P) s /\ (FINITE UNION_OF P) t
           ==> (FINITE UNION_OF P) (s UNION t)
Proof
  REPEAT STRIP_TAC THEN SIMP_TAC std_ss [GSYM UNIONS_2] THEN
  MATCH_MP_TAC FINITE_UNION_OF_UNIONS THEN
  ASM_SIMP_TAC std_ss [FINITE_INSERT, FORALL_IN_INSERT] THEN
  SIMP_TAC std_ss [FINITE_EMPTY, NOT_IN_EMPTY]
QED

Theorem FINITE_INTERSECTION_OF_INTERS :
   !P u:('a->bool)->bool.
        FINITE u /\ (!s. s IN u ==> (FINITE INTERSECTION_OF P) s)
        ==> (FINITE INTERSECTION_OF P) (INTERS u)
Proof
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM FINITE_INTERSECTION_OF_IDEMPOT] THEN
  ONCE_REWRITE_TAC [INTERSECTION_OF] THEN SIMP_TAC std_ss [] THEN
  Q.EXISTS_TAC `u:('a->bool)->bool` THEN ASM_SIMP_TAC std_ss []
QED

Theorem FINITE_INTERSECTION_OF_INTER :
   !P s t. (FINITE INTERSECTION_OF P) s /\ (FINITE INTERSECTION_OF P) t
           ==> (FINITE INTERSECTION_OF P) (s INTER t)
Proof
  REPEAT STRIP_TAC THEN SIMP_TAC std_ss [GSYM INTERS_2] THEN
  MATCH_MP_TAC FINITE_INTERSECTION_OF_INTERS THEN
  ASM_SIMP_TAC std_ss [FINITE_INSERT, FORALL_IN_INSERT] THEN
  SIMP_TAC std_ss [FINITE_EMPTY, NOT_IN_EMPTY]
QED

Theorem FINITE_UNION_OF_INTER_EQ :
   !P:('a->bool)->bool.
        (!s t. (FINITE UNION_OF P) s /\ (FINITE UNION_OF P) t
                   ==> (FINITE UNION_OF P) (s INTER t)) <=>
        (!s t. P s /\ P t ==> (FINITE UNION_OF P) (s INTER t))
Proof
  GEN_TAC THEN
  EQ_TAC THENL [MESON_TAC[FINITE_UNION_OF_INC], DISCH_TAC] THEN
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [UNION_OF] THEN
  SIMP_TAC std_ss [] THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  ASM_SIMP_TAC std_ss [INTER_UNIONS] THEN
  REPLICATE_TAC 2
   (MATCH_MP_TAC FINITE_UNION_OF_UNIONS THEN
    ASM_SIMP_TAC std_ss [SIMPLE_IMAGE, FINITE_IMAGE, FORALL_IN_IMAGE] THEN
    REPEAT STRIP_TAC)
QED

Theorem FINITE_UNION_OF_INTER :
    !P:('a->bool)->bool.
        (!s t. P s /\ P t ==> P(s INTER t))
        ==> (!s t. (FINITE UNION_OF P) s /\ (FINITE UNION_OF P) t
                   ==> (FINITE UNION_OF P) (s INTER t))
Proof
  SIMP_TAC std_ss [FINITE_UNION_OF_INTER_EQ] THEN
  MESON_TAC[FINITE_UNION_OF_INC]
QED

Theorem FINITE_INTERSECTION_OF_UNION_EQ :
    !P:('a->bool)->bool.
        (!s t. (FINITE INTERSECTION_OF P) s /\
               (FINITE INTERSECTION_OF P) t
               ==> (FINITE INTERSECTION_OF P) (s UNION t)) <=>
        (!s t. P s /\ P t ==> (FINITE INTERSECTION_OF P) (s UNION t))
Proof
  ONCE_REWRITE_TAC [FINITE_INTERSECTION_OF_COMPLEMENT] THEN
  SIMP_TAC std_ss [SET_RULE
    ``UNIV DIFF (s UNION t) = (UNIV DIFF s) INTER (UNIV DIFF t)``] THEN
  SIMP_TAC std_ss [MESON[COMPL_COMPL_applied] ``(!s. P(UNIV DIFF s)) <=> (!s. P s)``] THEN
  SIMP_TAC std_ss [FINITE_UNION_OF_INTER_EQ] THEN
  SIMP_TAC std_ss [SET_RULE
   ``s INTER t = UNIV DIFF ((UNIV DIFF s) UNION (UNIV DIFF t))``] THEN
  SIMP_TAC std_ss [MESON[COMPL_COMPL_applied] ``(!s. P(UNIV DIFF s)) <=> (!s. P s)``] THEN
  SIMP_TAC std_ss [COMPL_COMPL_applied]
QED

Theorem FINITE_INTERSECTION_OF_UNION :
   !P:('a->bool)->bool.
        (!s t. P s /\ P t ==> P(s UNION t))
        ==> (!s t. (FINITE INTERSECTION_OF P) s /\
                   (FINITE INTERSECTION_OF P) t
                   ==> (FINITE INTERSECTION_OF P) (s UNION t))
Proof
  SIMP_TAC std_ss [FINITE_INTERSECTION_OF_UNION_EQ] THEN
  MESON_TAC[FINITE_INTERSECTION_OF_INC]
QED

Theorem COUNTABLE_UNION_OF_EMPTY :
   !P:('a->bool)->bool. (COUNTABLE UNION_OF P) {}
Proof
  SIMP_TAC std_ss [UNION_OF_EMPTY, COUNTABLE_EMPTY]
QED

Theorem COUNTABLE_INTERSECTION_OF_EMPTY :
   !P:('a->bool)->bool. (COUNTABLE INTERSECTION_OF P) UNIV
Proof
  SIMP_TAC std_ss [INTERSECTION_OF_EMPTY, COUNTABLE_EMPTY]
QED

Theorem COUNTABLE_UNION_OF_INC :
   !P s:'a->bool. P s ==> (COUNTABLE UNION_OF P) s
Proof
  SIMP_TAC std_ss [UNION_OF_INC, COUNTABLE_SING]
QED

Theorem COUNTABLE_INTERSECTION_OF_INC :
   !P s:'a->bool. P s ==> (COUNTABLE INTERSECTION_OF P) s
Proof
  SIMP_TAC std_ss [INTERSECTION_OF_INC, COUNTABLE_SING]
QED

Theorem COUNTABLE_UNION_OF_COMPLEMENT :
   !P s. (COUNTABLE UNION_OF P) s <=>
         (COUNTABLE INTERSECTION_OF (\s. P(univ(:'a) DIFF s))) (univ(:'a) DIFF s)
Proof
  REPEAT GEN_TAC THEN SIMP_TAC std_ss [UNION_OF, INTERSECTION_OF] THEN
  EQ_TAC THEN
  DISCH_THEN(Q.X_CHOOSE_THEN `u:('a->bool)->bool` STRIP_ASSUME_TAC) THEN
  Q.EXISTS_TAC `IMAGE (\c. univ(:'a) DIFF c) u` THEN
  ASM_SIMP_TAC std_ss [COUNTABLE_IMAGE, FORALL_IN_IMAGE, COMPL_COMPL_applied] THEN
  ONCE_REWRITE_TAC[UNIONS_INTERS, INTERS_UNIONS] THEN
  Q.ABBREV_TAC ‘g = \c. univ(:'a) DIFF c’ \\
  ASM_SIMP_TAC std_ss [] \\
 ‘{g t | t | t IN IMAGE g u} = IMAGE (\x. g (g x)) u’
     by (rw [Once EXTENSION] >> METIS_TAC []) \\
  rw [Abbr ‘g’, IMAGE_ID, COMPL_COMPL_applied]
QED

Theorem COUNTABLE_INTERSECTION_OF_COMPLEMENT :
   !P s. (COUNTABLE INTERSECTION_OF P) s <=>
         (COUNTABLE UNION_OF (\s. P(univ(:'a) DIFF s))) (univ(:'a) DIFF s)
Proof
  REWRITE_TAC[COUNTABLE_UNION_OF_COMPLEMENT] THEN
  SIMP_TAC (std_ss ++ ETA_ss) [COMPL_COMPL_applied]
QED

Theorem COUNTABLE_UNION_OF_EXPLICIT :
   !P s:'a->bool.
        P {}
        ==> ((COUNTABLE UNION_OF P) s <=>
             ?t. (!n. P(t n)) /\ UNIONS {t n | n IN univ(:num)} = s)
Proof
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  SIMP_TAC std_ss [UNION_OF, LEFT_IMP_EXISTS_THM] THENL
  [ (* goal 1 (of 2) *)
    Q.X_GEN_TAC `u:('a->bool)->bool` THEN
    ASM_CASES_TAC ``u:('a->bool)->bool = {}`` THENL
    [ (* goal 1.1 (of 2) *)
      ASM_REWRITE_TAC[UNIONS_0] THEN
      DISCH_THEN(SUBST1_TAC o SYM o last o CONJUNCTS) THEN
      Q.EXISTS_TAC `(\n. {}):num->'a->bool` THEN
      ASM_SIMP_TAC std_ss [UNIONS_GSPEC, NOT_IN_EMPTY, EMPTY_GSPEC],
      (* goal 1.2 (of 2) *)
      STRIP_TAC THEN
      MP_TAC(Q.ISPEC `u:('a->bool)->bool` COUNTABLE_AS_IMAGE) THEN
      RW_TAC std_ss [] >> fs [IN_IMAGE] \\
      Q.EXISTS_TAC ‘f’ >> ASM_SET_TAC[] ],
    (* goal 2 (of 2) *)
    Q.X_GEN_TAC `t:num->'a->bool` THEN STRIP_TAC THEN
    Q.EXISTS_TAC `{t n:'a->bool | n IN univ(:num)}` THEN
    ASM_REWRITE_TAC[FORALL_IN_GSPEC] THEN
    rw [SIMPLE_IMAGE, COUNTABLE_IMAGE, COUNTABLE_SUBSET_NUM] THEN
    ASM_REWRITE_TAC [] ]
QED

Theorem COUNTABLE_UNION_OF_ASCENDING :
   !P s:'a->bool.
        P {} /\ (!t u. P t /\ P u ==> P(t UNION u))
        ==> ((COUNTABLE UNION_OF P) s <=>
             ?t. (!n. P(t n)) /\
                 (!n. t n SUBSET t(SUC n)) /\
                 UNIONS {t n | n IN univ(:num)} = s)
Proof
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC std_ss [COUNTABLE_UNION_OF_EXPLICIT, IN_UNIV] THEN
  reverse EQ_TAC >- METIS_TAC [] \\
  DISCH_THEN(Q.X_CHOOSE_THEN `t:num->'a->bool` STRIP_ASSUME_TAC) THEN
  Q.EXISTS_TAC `(\n. UNIONS {t m | m <= n}):num->'a->bool` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FORALL_IN_IMAGE, IN_UNIV]) THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [ (* goal 1 (of 3) *)
    Induct_on ‘n’ >> rw [LE]
    >- (‘BIGUNION {t m | m = 0} = t 0’ by rw [Once EXTENSION] \\
        POP_ASSUM (ASM_REWRITE_TAC o wrap)) \\
    SIMP_TAC std_ss [SET_RULE ``{f x | P x \/ Q x} = {f x | P x} UNION {f x | Q x}``,
                     SET_RULE ``{f x | x = a} = {f a}``, UNIONS_UNION] THEN
    ASM_SIMP_TAC std_ss [UNIONS_1] \\
    FIRST_X_ASSUM MATCH_MP_TAC >> fs [],
    (* goal 2 (of 3) *)
    RW_TAC std_ss [UNIONS_GSPEC, LE] THEN SET_TAC[],
    (* goal 3 (of 3) *)
    FIRST_X_ASSUM(SUBST1_TAC o SYM o last o CONJUNCTS) THEN
    SIMP_TAC std_ss [UNIONS_GSPEC, IN_UNIV] \\
    rw [Once EXTENSION] \\
    EQ_TAC >> rw [] >- (Q.EXISTS_TAC ‘m’ >> rw []) \\
    qexistsl_tac [‘n’, ‘n’] >> rw [] ]
QED

Theorem COUNTABLE_UNION_OF_IDEMPOT :
   !P:('a->bool)->bool.
        COUNTABLE UNION_OF COUNTABLE UNION_OF P = COUNTABLE UNION_OF P
Proof
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN Q.X_GEN_TAC `s:'a->bool` THEN
  EQ_TAC THEN REWRITE_TAC[COUNTABLE_UNION_OF_INC] THEN
  SIMP_TAC std_ss [UNION_OF, LEFT_IMP_EXISTS_THM] THEN
  Q.X_GEN_TAC `u:('a->bool)->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM)) THEN
  rw [EXT_SKOLEM_THM] \\
  Q.EXISTS_TAC
    `IMAGE SND {s,t | s IN u /\ t IN (f:('a->bool)->('a->bool)->bool) s}` THEN
  ASM_SIMP_TAC std_ss [COUNTABLE_IMAGE, COUNTABLE_PRODUCT_DEPENDENT] THEN
  REWRITE_TAC[FORALL_IN_IMAGE, FORALL_IN_GSPEC] THEN
  rw [] >- METIS_TAC [SND] \\
  REWRITE_TAC[UNIONS_IMAGE] THEN
  REWRITE_TAC[EXISTS_IN_GSPEC] THEN ASM_SET_TAC[]
QED

Theorem COUNTABLE_INTERSECTION_OF_IDEMPOT :
   !P:('a->bool)->bool.
        COUNTABLE INTERSECTION_OF COUNTABLE INTERSECTION_OF P =
        COUNTABLE INTERSECTION_OF P
Proof
  RW_TAC (std_ss ++ ETA_ss)
         [COMPL_COMPL_applied, FUN_EQ_THM, COUNTABLE_INTERSECTION_OF_COMPLEMENT] THEN
  REWRITE_TAC[COUNTABLE_UNION_OF_IDEMPOT]
QED

Theorem COUNTABLE_UNION_OF_UNIONS :
   !P u:('a->bool)->bool.
        COUNTABLE u /\ (!s. s IN u ==> (COUNTABLE UNION_OF P) s)
        ==> (COUNTABLE UNION_OF P) (UNIONS u)
Proof
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM COUNTABLE_UNION_OF_IDEMPOT] THEN
  ONCE_REWRITE_TAC[UNION_OF] THEN SIMP_TAC std_ss [] THEN
  Q.EXISTS_TAC `u:('a->bool)->bool` THEN ASM_REWRITE_TAC[]
QED

Theorem COUNTABLE_UNION_OF_UNION :
   !P s t. (COUNTABLE UNION_OF P) s /\ (COUNTABLE UNION_OF P) t
           ==> (COUNTABLE UNION_OF P) (s UNION t)
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM UNIONS_2] THEN
  MATCH_MP_TAC COUNTABLE_UNION_OF_UNIONS THEN
  ASM_REWRITE_TAC[COUNTABLE_INSERT, FORALL_IN_INSERT] THEN
  REWRITE_TAC[COUNTABLE_EMPTY, NOT_IN_EMPTY]
QED

Theorem COUNTABLE_INTERSECTION_OF_INTERS :
   !P u:('a->bool)->bool.
        COUNTABLE u /\ (!s. s IN u ==> (COUNTABLE INTERSECTION_OF P) s)
        ==> (COUNTABLE INTERSECTION_OF P) (INTERS u)
Proof
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM COUNTABLE_INTERSECTION_OF_IDEMPOT] THEN
  ONCE_REWRITE_TAC[INTERSECTION_OF] THEN SIMP_TAC std_ss [] THEN
  Q.EXISTS_TAC `u:('a->bool)->bool` THEN ASM_REWRITE_TAC[]
QED

Theorem COUNTABLE_INTERSECTION_OF_INTER :
   !P s t. (COUNTABLE INTERSECTION_OF P) s /\ (COUNTABLE INTERSECTION_OF P) t
           ==> (COUNTABLE INTERSECTION_OF P) (s INTER t)
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INTERS_2] THEN
  MATCH_MP_TAC COUNTABLE_INTERSECTION_OF_INTERS THEN
  ASM_REWRITE_TAC[COUNTABLE_INSERT, FORALL_IN_INSERT] THEN
  REWRITE_TAC[COUNTABLE_EMPTY, NOT_IN_EMPTY]
QED

Theorem COUNTABLE_UNION_OF_INTER_EQ :
   !P:('a->bool)->bool.
        (!s t. (COUNTABLE UNION_OF P) s /\ (COUNTABLE UNION_OF P) t
                   ==> (COUNTABLE UNION_OF P) (s INTER t)) <=>
        (!s t. P s /\ P t ==> (COUNTABLE UNION_OF P) (s INTER t))
Proof
  GEN_TAC THEN
  EQ_TAC THENL [MESON_TAC[COUNTABLE_UNION_OF_INC], DISCH_TAC] THEN
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [UNION_OF] THEN
  SIMP_TAC std_ss [] THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  ASM_REWRITE_TAC[INTER_UNIONS] THEN
  REPLICATE_TAC 2
   (MATCH_MP_TAC COUNTABLE_UNION_OF_UNIONS THEN
    ASM_SIMP_TAC std_ss [SIMPLE_IMAGE, COUNTABLE_IMAGE, FORALL_IN_IMAGE] THEN
    REPEAT STRIP_TAC)
QED

Theorem COUNTABLE_UNION_OF_INTER :
   !P:('a->bool)->bool.
        (!s t. P s /\ P t ==> P(s INTER t))
        ==> (!s t. (COUNTABLE UNION_OF P) s /\ (COUNTABLE UNION_OF P) t
                   ==> (COUNTABLE UNION_OF P) (s INTER t))
Proof
  REWRITE_TAC[COUNTABLE_UNION_OF_INTER_EQ] THEN
  MESON_TAC[COUNTABLE_UNION_OF_INC]
QED

Theorem COUNTABLE_INTERSECTION_OF_UNION_EQ :
   !P:('a->bool)->bool.
        (!s t. (COUNTABLE INTERSECTION_OF P) s /\
               (COUNTABLE INTERSECTION_OF P) t
               ==> (COUNTABLE INTERSECTION_OF P) (s UNION t)) <=>
        (!s t. P s /\ P t ==> (COUNTABLE INTERSECTION_OF P) (s UNION t))
Proof
  ONCE_REWRITE_TAC[COUNTABLE_INTERSECTION_OF_COMPLEMENT] THEN
  REWRITE_TAC[SET_RULE
    ``UNIV DIFF (s UNION t) = (UNIV DIFF s) INTER (UNIV DIFF t)``] THEN
  SIMP_TAC std_ss [MESON[COMPL_COMPL_applied] ``(!s. P(UNIV DIFF s)) <=> (!s. P s)``] THEN
  SIMP_TAC std_ss [COUNTABLE_UNION_OF_INTER_EQ] THEN
  REWRITE_TAC[SET_RULE
   ``s INTER t = UNIV DIFF ((UNIV DIFF s) UNION (UNIV DIFF t))``] THEN
  SIMP_TAC std_ss [MESON[COMPL_COMPL_applied] ``(!s. P(UNIV DIFF s)) <=> (!s. P s)``] THEN
  REWRITE_TAC[COMPL_COMPL_applied]
QED

Theorem COUNTABLE_INTERSECTION_OF_UNION :
   !P:('a->bool)->bool.
        (!s t. P s /\ P t ==> P(s UNION t))
        ==> (!s t. (COUNTABLE INTERSECTION_OF P) s /\
                   (COUNTABLE INTERSECTION_OF P) t
                   ==> (COUNTABLE INTERSECTION_OF P) (s UNION t))
Proof
  REWRITE_TAC[COUNTABLE_INTERSECTION_OF_UNION_EQ] THEN
  MESON_TAC[COUNTABLE_INTERSECTION_OF_INC]
QED

Theorem COUNTABLE_INTERSECTION_OF_UNIONS_NONEMPTY :
   !P u:('a->bool)->bool.
        (!s t. P s /\ P t ==> P (s UNION t)) /\
        FINITE u /\ ~(u = {}) /\
        (!s. s IN u ==> (COUNTABLE INTERSECTION_OF P) s)
        ==> (COUNTABLE INTERSECTION_OF P) (UNIONS u)
Proof
  REWRITE_TAC[IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
  rpt GEN_TAC THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IMP_IMP, RIGHT_IMP_FORALL_THM]) THEN
  Q.SPEC_TAC (‘u’, ‘u’) \\
  HO_MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC std_ss [FORALL_IN_INSERT, NOT_INSERT_EMPTY] THEN
  qx_genl_tac [`s:'a->bool`, `u:('a->bool)->bool`] THEN
  ASM_CASES_TAC ``u:('a->bool)->bool = {}`` THEN
  ASM_SIMP_TAC std_ss [UNIONS_1] THEN REWRITE_TAC[UNIONS_INSERT] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP COUNTABLE_INTERSECTION_OF_UNION) THEN
  ASM_SIMP_TAC std_ss []
QED

Theorem COUNTABLE_INTERSECTION_OF_UNIONS :
   !P u:('a->bool)->bool.
        (COUNTABLE INTERSECTION_OF P) {} /\
        (!s t. P s /\ P t ==> P (s UNION t)) /\
        FINITE u /\
        (!s. s IN u ==> (COUNTABLE INTERSECTION_OF P) s)
        ==> (COUNTABLE INTERSECTION_OF P) (UNIONS u)
Proof
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_CASES_TAC ``u:('a->bool)->bool = {}`` THEN
  ASM_REWRITE_TAC[UNIONS_0] THEN STRIP_TAC THEN
  MATCH_MP_TAC COUNTABLE_INTERSECTION_OF_UNIONS_NONEMPTY THEN
  ASM_REWRITE_TAC[]
QED

Theorem COUNTABLE_UNION_OF_INTERS_NONEMPTY :
   !P u:('a->bool)->bool.
        (!s t. P s /\ P t ==> P (s INTER t)) /\
        FINITE u /\ ~(u = {}) /\
        (!s. s IN u ==> (COUNTABLE UNION_OF P) s)
        ==> (COUNTABLE UNION_OF P) (INTERS u)
Proof
  REWRITE_TAC[IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
  rpt GEN_TAC THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IMP_IMP, RIGHT_IMP_FORALL_THM]) THEN
  Q.SPEC_TAC (‘u’, ‘u’) \\
  HO_MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[FORALL_IN_INSERT, NOT_INSERT_EMPTY] THEN
  qx_genl_tac [`s:'a->bool`, `u:('a->bool)->bool`] THEN
  ASM_CASES_TAC ``u:('a->bool)->bool = {}`` THEN
  ASM_SIMP_TAC std_ss [INTERS_1] THEN REWRITE_TAC[INTERS_INSERT] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP COUNTABLE_UNION_OF_INTER) THEN
  ASM_SIMP_TAC std_ss []
QED

Theorem COUNTABLE_UNION_OF_INTERS :
   !P u:('a->bool)->bool.
        (COUNTABLE UNION_OF P) univ(:'a) /\
        (!s t. P s /\ P t ==> P (s INTER t)) /\
        FINITE u /\
        (!s. s IN u ==> (COUNTABLE UNION_OF P) s)
        ==> (COUNTABLE UNION_OF P) (INTERS u)
Proof
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_CASES_TAC ``u:('a->bool)->bool = {}`` THEN
  ASM_REWRITE_TAC[INTERS_0] THEN STRIP_TAC THEN
  MATCH_MP_TAC COUNTABLE_UNION_OF_INTERS_NONEMPTY THEN
  ASM_REWRITE_TAC[]
QED

Theorem COUNTABLE_DISJOINT_UNION_OF_IDEMPOT :
   !P:('a->bool)->bool.
        ((COUNTABLE INTER pairwise DISJOINT) UNION_OF
         (COUNTABLE INTER pairwise DISJOINT) UNION_OF P) =
        (COUNTABLE INTER pairwise DISJOINT) UNION_OF P
Proof
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN Q.X_GEN_TAC `s:'a->bool` THEN
  reverse EQ_TAC
  >- (MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] UNION_OF_INC) THEN
      rw [INTER_DEF, IN_APP, COUNTABLE_SING, PAIRWISE_SING]) \\
  SIMP_TAC std_ss [SET_RULE ``s INTER t = \x. s x /\ t x``] \\
  SIMP_TAC std_ss [UNION_OF, LEFT_IMP_EXISTS_THM] THEN
  Q.X_GEN_TAC `u:('a->bool)->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM)) THEN
  rw [EXT_SKOLEM_THM] \\
  Q.EXISTS_TAC
    `IMAGE SND {s,t | s IN u /\ t IN (f:('a->bool)->('a->bool)->bool) s}` THEN
  ASM_SIMP_TAC std_ss [COUNTABLE_IMAGE, COUNTABLE_PRODUCT_DEPENDENT] THEN
  SIMP_TAC std_ss [FORALL_IN_IMAGE, FORALL_IN_GSPEC] THEN
  REWRITE_TAC[UNIONS_IMAGE, EXISTS_IN_GSPEC, PAIRWISE_IMAGE] THEN
  CONJ_TAC THENL [REWRITE_TAC[pairwise], ASM_SET_TAC[]] THEN
  SIMP_TAC std_ss [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_GSPEC] THEN
  MAP_EVERY (fn x => Q.X_GEN_TAC x THEN DISCH_TAC)
   [`s1:'a->bool`, `t1:'a->bool`, `s2:'a->bool`, `t2:'a->bool`] THEN
  DISCH_THEN(K ALL_TAC) THEN ASM_CASES_TAC ``s2:'a->bool = s1`` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THENL
  [ ASM_MESON_TAC[], ASM_SET_TAC[] ]
QED

(* ------------------------------------------------------------------------- *)
(* A somewhat cheap but handy way of getting localized forms of various      *)
(* topological concepts (open, closed, borel, fsigma, gdelta etc.)           *)
(* ------------------------------------------------------------------------- *)

val _ = set_fixity "relative_to" (Infixl 500);

Definition relative_to :
   (P relative_to s) t = ?u. P u /\ s INTER u = t
End

Theorem RELATIVE_TO_UNIV :
    !P s. (P relative_to univ(:'a)) s <=> P s
Proof
  REWRITE_TAC[relative_to, INTER_UNIV] THEN MESON_TAC[]
QED

Theorem RELATIVE_TO_IMP_SUBSET :
   !P s t. (P relative_to s) t ==> t SUBSET s
Proof
  REWRITE_TAC[relative_to] THEN SET_TAC[]
QED

Theorem FORALL_RELATIVE_TO :
   (!s. (P relative_to u) s ==> Q s) <=>
   (!s. P s ==> Q(u INTER s))
Proof
  REWRITE_TAC[relative_to] THEN MESON_TAC[]
QED

Theorem RELATIVE_TO_INC :
   !P u s. P s ==> (P relative_to u) (u INTER s)
Proof
  REWRITE_TAC[relative_to] THEN MESON_TAC[]
QED

Theorem RELATIVE_TO :
   (P relative_to u) = {u INTER s | P s}
Proof
    rw [Once EXTENSION, relative_to, IN_APP]
 >> SET_TAC []
QED

Theorem RELATIVE_TO_RELATIVE_TO :
   !P:('a->bool)->bool s t.
        P relative_to s relative_to t = P relative_to (s INTER t)
Proof
    rw [Once EXTENSION, RELATIVE_TO]
 >> EQ_TAC >> rw [] >> rename1 ‘P u’
 >- (Q.EXISTS_TAC ‘u’ >> METIS_TAC [INTER_ASSOC, INTER_COMM])
 >> Q.EXISTS_TAC ‘s INTER u’
 >> CONJ_TAC >- METIS_TAC [INTER_ASSOC, INTER_COMM]
 >> Q.EXISTS_TAC ‘u’ >> rw []
QED

Theorem RELATIVE_TO_COMPL :
   !P u s:'a->bool.
        s SUBSET u
        ==> ((P relative_to u) (u DIFF s) <=>
             ((\c. P(UNIV DIFF c)) relative_to u) s)
Proof
    rpt STRIP_TAC >> REWRITE_TAC [relative_to]
 >> EQ_TAC >> rw []
 >- (rename1 ‘P w’ \\
     Q.EXISTS_TAC ‘univ(:'a) DIFF w’ >> rw [COMPL_COMPL_applied] \\
     ASM_SET_TAC [])
 >> rename1 ‘u INTER w SUBSET u’
 >> Q.EXISTS_TAC ‘univ(:'a) DIFF w’ >> rw []
 >> ASM_SET_TAC []
QED

Theorem RELATIVE_TO_SUBSET :
   !P s t:'a->bool. s SUBSET t /\ P s ==> (P relative_to t) s
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[relative_to] THEN
  Q.EXISTS_TAC `s:'a->bool` THEN ASM_SET_TAC[]
QED

Theorem RELATIVE_TO_SUBSET_TRANS :
   !P u s t:'a->bool.
      (P relative_to u) s /\ s SUBSET t /\ t SUBSET u ==> (P relative_to t) s
Proof
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[relative_to] THEN
  HO_MATCH_MP_TAC MONO_EXISTS THEN ASM_SET_TAC[]
QED

Theorem RELATIVE_TO_MONO :
   !P Q.
     (!s. P s ==> Q s) ==> !u. (P relative_to u) s ==> (Q relative_to u) s
Proof
  REWRITE_TAC[relative_to] THEN MESON_TAC[]
QED

Theorem RELATIVE_TO_SUBSET_INC :
   !P u s:'a->bool.
        s SUBSET u /\ P s ==> (P relative_to u) s
Proof
  REWRITE_TAC[relative_to] THEN
  MESON_TAC[SET_RULE ``s SUBSET u ==> u INTER s = s``]
QED

Theorem RELATIVE_TO_INTER :
   !P s. (!c d:'a->bool. P c /\ P d ==> P(c INTER d))
         ==> !c d. (P relative_to s) c /\ (P relative_to s) d
                   ==> (P relative_to s) (c INTER d)
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[relative_to] THEN DISCH_THEN(CONJUNCTS_THEN2
   (Q.X_CHOOSE_THEN `c':'a->bool` (STRIP_ASSUME_TAC o GSYM))
   (Q.X_CHOOSE_THEN `d':'a->bool` (STRIP_ASSUME_TAC o GSYM))) THEN
  Q.EXISTS_TAC `c' INTER d':'a->bool` THEN
  ASM_SIMP_TAC std_ss [] THEN ASM_SET_TAC[]
QED

Theorem RELATIVE_TO_UNION :
   !P s. (!c d:'a->bool. P c /\ P d ==> P(c UNION d))
         ==> !c d. (P relative_to s) c /\ (P relative_to s) d
                   ==> (P relative_to s) (c UNION d)
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[relative_to] THEN DISCH_THEN(CONJUNCTS_THEN2
   (Q.X_CHOOSE_THEN `c':'a->bool` (STRIP_ASSUME_TAC o GSYM))
   (Q.X_CHOOSE_THEN `d':'a->bool` (STRIP_ASSUME_TAC o GSYM))) THEN
  Q.EXISTS_TAC `c' UNION d':'a->bool` THEN
  ASM_SIMP_TAC std_ss [] THEN ASM_SET_TAC[]
QED

Theorem ARBITRARY_UNION_OF_RELATIVE_TO :
   !P u:'a->bool.
        ((ARBITRARY UNION_OF P) relative_to u) =
        (ARBITRARY UNION_OF (P relative_to u))
Proof
  REWRITE_TAC[FUN_EQ_THM] THEN
  REPEAT STRIP_TAC THEN SIMP_TAC std_ss [UNION_OF, relative_to] THEN
  EQ_TAC THENL
  [ (* goal 1 (of 2) *)
    DISCH_THEN(Q.X_CHOOSE_THEN `t:'a->bool`
     (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM))) THEN
    DISCH_THEN(Q.X_CHOOSE_THEN `f:('a->bool)->bool`
     (STRIP_ASSUME_TAC o GSYM)) THEN
    Q.EXISTS_TAC `{u INTER c | (c:'a->bool) IN f}` THEN
    ASM_REWRITE_TAC[INTER_UNIONS] THEN
    ASM_SIMP_TAC std_ss [SIMPLE_IMAGE, ARBITRARY, FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[],
    (* goal 2 (of 2) *)
    DISCH_THEN(Q.X_CHOOSE_THEN `f:('a->bool)->bool` STRIP_ASSUME_TAC) THEN
    Q.PAT_X_ASSUM ‘!c. c IN f ==> _’ MP_TAC \\
    rw [EXT_SKOLEM_THM] \\
    rename1 ‘!c. c IN f ==> P (g c) /\ u INTER g c = c’ \\
    Q.EXISTS_TAC `UNIONS (IMAGE (g:('a->bool)->('a->bool)) f)` THEN
    CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC[]] THEN
    Q.EXISTS_TAC `IMAGE (g:('a->bool)->('a->bool)) f` THEN
    ASM_SIMP_TAC std_ss [ARBITRARY, FORALL_IN_IMAGE] ]
QED

Theorem FINITE_UNION_OF_RELATIVE_TO :
   !P u:'a->bool.
        ((FINITE UNION_OF P) relative_to u) =
        (FINITE UNION_OF (P relative_to u))
Proof
  REWRITE_TAC[FUN_EQ_THM] THEN
  REPEAT STRIP_TAC THEN SIMP_TAC std_ss [UNION_OF, relative_to]
  THEN EQ_TAC THENL
  [ (* goal 1 (of 2) *)
    DISCH_THEN(Q.X_CHOOSE_THEN `t:'a->bool`
     (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM))) THEN
    DISCH_THEN(Q.X_CHOOSE_THEN `f:('a->bool)->bool`
     (STRIP_ASSUME_TAC o GSYM)) THEN
    Q.EXISTS_TAC `{u INTER c | (c:'a->bool) IN f}` THEN
    ASM_REWRITE_TAC[INTER_UNIONS] THEN
    ASM_SIMP_TAC std_ss [SIMPLE_IMAGE, FINITE_IMAGE, FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[],
    (* goal 2 (of 2) *)
    DISCH_THEN(Q.X_CHOOSE_THEN `f:('a->bool)->bool` STRIP_ASSUME_TAC) THEN
    Q.PAT_X_ASSUM ‘!c. c IN f ==> _’ MP_TAC \\
    rw [EXT_SKOLEM_THM] \\
    rename1 ‘!c. c IN f ==> P (g c) /\ u INTER g c = c’ \\
    Q.EXISTS_TAC `UNIONS (IMAGE (g:('a->bool)->('a->bool)) f)` THEN
    CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC[]] THEN
    Q.EXISTS_TAC `IMAGE (g:('a->bool)->('a->bool)) f` THEN
    ASM_SIMP_TAC std_ss [FINITE_IMAGE, FORALL_IN_IMAGE] ]
QED

Theorem COUNTABLE_UNION_OF_RELATIVE_TO :
   !P u:'a->bool.
        ((COUNTABLE UNION_OF P) relative_to u) =
        (COUNTABLE UNION_OF (P relative_to u))
Proof
  REWRITE_TAC[FUN_EQ_THM] THEN
  REPEAT STRIP_TAC THEN SIMP_TAC std_ss [UNION_OF, relative_to]
  THEN EQ_TAC THENL
  [ (* goal 1 (of 2) *)
    DISCH_THEN(Q.X_CHOOSE_THEN `t:'a->bool`
     (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM))) THEN
    DISCH_THEN(Q.X_CHOOSE_THEN `f:('a->bool)->bool`
     (STRIP_ASSUME_TAC o GSYM)) THEN
    Q.EXISTS_TAC `{u INTER c | (c:'a->bool) IN f}` THEN
    ASM_REWRITE_TAC[INTER_UNIONS] THEN
    ASM_SIMP_TAC std_ss [SIMPLE_IMAGE, COUNTABLE_IMAGE, FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[],
    (* goal 2 (of 2) *)
    DISCH_THEN(Q.X_CHOOSE_THEN `f:('a->bool)->bool` STRIP_ASSUME_TAC) THEN
    Q.PAT_X_ASSUM ‘!c. c IN f ==> _’ MP_TAC \\
    rw [EXT_SKOLEM_THM] \\
    rename1 ‘!c. c IN f ==> P (g c) /\ u INTER g c = c’ \\
    Q.EXISTS_TAC `UNIONS (IMAGE (g:('a->bool)->('a->bool)) f)` THEN
    CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC[]] THEN
    Q.EXISTS_TAC `IMAGE (g:('a->bool)->('a->bool)) f` THEN
    ASM_SIMP_TAC std_ss [COUNTABLE_IMAGE, FORALL_IN_IMAGE] ]
QED

Theorem ARBITRARY_INTERSECTION_OF_RELATIVE_TO :
   !P u:'a->bool.
        ((ARBITRARY INTERSECTION_OF P) relative_to u) =
        ((ARBITRARY INTERSECTION_OF (P relative_to u)) relative_to u)
Proof
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I empty_rewrites [FUN_EQ_THM] THEN
  Q.X_GEN_TAC `s:'a->bool` THEN REWRITE_TAC[INTERSECTION_OF, relative_to] THEN
  BETA_TAC THEN EQ_TAC THENL
  [ (* goal 1 (of 2) *)
    DISCH_THEN(Q.X_CHOOSE_THEN `t:'a->bool`
     (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM))) THEN
    DISCH_THEN(Q.X_CHOOSE_THEN `f:('a->bool)->bool`
     (STRIP_ASSUME_TAC o GSYM)) THEN
    Q.EXISTS_TAC `INTERS {u INTER c | (c:'a->bool) IN f}` THEN CONJ_TAC THENL
    [ (* goal 1.1 (of 2) *)
      Q.EXISTS_TAC `{u INTER c | (c:'a->bool) IN f}` THEN
      ASM_SIMP_TAC std_ss [ARBITRARY, SIMPLE_IMAGE, FORALL_IN_IMAGE] THEN
      ASM_MESON_TAC[],
      (* goal 1.2 (of 2) *)
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[INTER_INTERS] THEN
      SIMP_TAC std_ss [SIMPLE_IMAGE, IMAGE_EQ_EMPTY, INTERS_IMAGE, FORALL_IN_IMAGE,
                  SET_RULE ``u INTER (u INTER s) = u INTER s``] ],
    (* goal 2 (of 2) *)
    DISCH_THEN(Q.X_CHOOSE_THEN `t:'a->bool`
     (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM))) THEN
    DISCH_THEN(Q.X_CHOOSE_THEN `f:('a->bool)->bool` STRIP_ASSUME_TAC) THEN
    Q.PAT_X_ASSUM ‘!c. c IN f ==> _’ MP_TAC \\
    rw [EXT_SKOLEM_THM] \\
    rename1 ‘!c. c IN f ==> P (g c) /\ u INTER g c = c’ \\
    Q.EXISTS_TAC `INTERS (IMAGE (g:('a->bool)->('a->bool)) f)` THEN
    CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC[]] THEN
    Q.EXISTS_TAC `IMAGE (g:('a->bool)->('a->bool)) f` THEN
    ASM_SIMP_TAC std_ss [ARBITRARY, FORALL_IN_IMAGE] ]
QED

Theorem FINITE_INTERSECTION_OF_RELATIVE_TO :
   !P u:'a->bool.
        ((FINITE INTERSECTION_OF P) relative_to u) =
        ((FINITE INTERSECTION_OF (P relative_to u)) relative_to u)
Proof
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I empty_rewrites [FUN_EQ_THM] THEN
  Q.X_GEN_TAC `s:'a->bool` THEN REWRITE_TAC[INTERSECTION_OF, relative_to] THEN
  BETA_TAC THEN EQ_TAC THENL
  [ (* goal 1 (of 2) *)
    DISCH_THEN(Q.X_CHOOSE_THEN `t:'a->bool`
     (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM))) THEN
    DISCH_THEN(Q.X_CHOOSE_THEN `f:('a->bool)->bool`
     (STRIP_ASSUME_TAC o GSYM)) THEN
    Q.EXISTS_TAC `INTERS {u INTER c | (c:'a->bool) IN f}` THEN CONJ_TAC THENL
    [ (* goal 1.1 (of 2) *)
      Q.EXISTS_TAC `{u INTER c | (c:'a->bool) IN f}` THEN
      ASM_SIMP_TAC std_ss [FINITE_IMAGE, SIMPLE_IMAGE, FORALL_IN_IMAGE] THEN
      ASM_MESON_TAC[],
      (* goal 1.2 (of 2) *)
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[INTER_INTERS] THEN
      SIMP_TAC std_ss [SIMPLE_IMAGE, IMAGE_EQ_EMPTY, INTERS_IMAGE, FORALL_IN_IMAGE,
                  SET_RULE ``u INTER (u INTER s) = u INTER s``] ],
    (* goal 2 (of 2) *)
    DISCH_THEN(Q.X_CHOOSE_THEN `t:'a->bool`
     (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM))) THEN
    DISCH_THEN(Q.X_CHOOSE_THEN `f:('a->bool)->bool` STRIP_ASSUME_TAC) THEN
    Q.PAT_X_ASSUM ‘!c. c IN f ==> _’ MP_TAC \\
    rw [EXT_SKOLEM_THM] \\
    rename1 ‘!c. c IN f ==> P (g c) /\ u INTER g c = c’ \\
    Q.EXISTS_TAC `INTERS (IMAGE (g:('a->bool)->('a->bool)) f)` THEN
    CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC[]] THEN
    Q.EXISTS_TAC `IMAGE (g:('a->bool)->('a->bool)) f` THEN
    ASM_SIMP_TAC std_ss [FINITE_IMAGE, FORALL_IN_IMAGE] ]
QED

Theorem COUNTABLE_INTERSECTION_OF_RELATIVE_TO :
   !P u:'a->bool.
        ((COUNTABLE INTERSECTION_OF P) relative_to u) =
        ((COUNTABLE INTERSECTION_OF (P relative_to u)) relative_to u)
Proof
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I empty_rewrites [FUN_EQ_THM] THEN
  Q.X_GEN_TAC `s:'a->bool` THEN REWRITE_TAC[INTERSECTION_OF, relative_to] THEN
  BETA_TAC THEN EQ_TAC THENL
  [ (* goal 1 (of 2) *)
    DISCH_THEN(Q.X_CHOOSE_THEN `t:'a->bool`
     (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM))) THEN
    DISCH_THEN(Q.X_CHOOSE_THEN `f:('a->bool)->bool`
     (STRIP_ASSUME_TAC o GSYM)) THEN
    Q.EXISTS_TAC `INTERS {u INTER c | (c:'a->bool) IN f}` THEN CONJ_TAC THENL
    [ Q.EXISTS_TAC `{u INTER c | (c:'a->bool) IN f}` THEN
      ASM_SIMP_TAC std_ss [COUNTABLE_IMAGE, SIMPLE_IMAGE, FORALL_IN_IMAGE] THEN
      ASM_MESON_TAC[],
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[INTER_INTERS] THEN
      ASM_SIMP_TAC std_ss [SIMPLE_IMAGE, IMAGE_EQ_EMPTY, INTERS_IMAGE, FORALL_IN_IMAGE,
                  SET_RULE ``u INTER (u INTER s) = u INTER s``] ],
    DISCH_THEN(Q.X_CHOOSE_THEN `t:'a->bool`
     (CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM))) THEN
    DISCH_THEN(Q.X_CHOOSE_THEN `f:('a->bool)->bool` STRIP_ASSUME_TAC) THEN
    Q.PAT_X_ASSUM ‘!c. c IN f ==> _’ MP_TAC \\
    rw [EXT_SKOLEM_THM] \\
    rename1 ‘!c. c IN f ==> P (g c) /\ u INTER g c = c’ \\
    Q.EXISTS_TAC `INTERS (IMAGE (g:('a->bool)->('a->bool)) f)` THEN
    CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC[]] THEN
    Q.EXISTS_TAC `IMAGE (g:('a->bool)->('a->bool)) f` THEN
    ASM_SIMP_TAC std_ss [COUNTABLE_IMAGE, FORALL_IN_IMAGE] ]
QED

Theorem FINITE_INTERSECTION_OF_RELATIVE_TO_ALT :
   !P u s:'a->bool.
        P u ==> ((FINITE INTERSECTION_OF P relative_to u) s <=>
                 (FINITE INTERSECTION_OF P) s /\ s SUBSET u)
Proof
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC std_ss [RELATIVE_TO_SUBSET_INC] THEN
  Q.SPEC_TAC(`s:'a->bool`,`s:'a->bool`) THEN
  SIMP_TAC std_ss [FORALL_RELATIVE_TO, FORALL_INTERSECTION_OF] THEN
  REWRITE_TAC[INTER_SUBSET, GSYM INTERS_INSERT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_INTERSECTION_OF_INTERS THEN
  ASM_REWRITE_TAC[FINITE_INSERT, FORALL_IN_INSERT] THEN
  ASM_SIMP_TAC std_ss [FINITE_INTERSECTION_OF_INC]
QED

Theorem COUNTABLE_INTERSECTION_OF_RELATIVE_TO_ALT :
   !P u s:'a->bool.
        P u ==> ((COUNTABLE INTERSECTION_OF P relative_to u) s <=>
                 (COUNTABLE INTERSECTION_OF P) s /\ s SUBSET u)
Proof
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC std_ss [RELATIVE_TO_SUBSET_INC] THEN
  Q.SPEC_TAC(`s:'a->bool`,`s:'a->bool`) THEN
  SIMP_TAC std_ss [FORALL_RELATIVE_TO, FORALL_INTERSECTION_OF] THEN
  REWRITE_TAC[INTER_SUBSET, GSYM INTERS_INSERT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COUNTABLE_INTERSECTION_OF_INTERS THEN
  ASM_REWRITE_TAC[COUNTABLE_INSERT, FORALL_IN_INSERT] THEN
  ASM_SIMP_TAC std_ss [COUNTABLE_INTERSECTION_OF_INC]
QED

Theorem ARBITRARY_UNION_OF_NONEMPTY_FINITE_INTERSECTION :
   !u:('a->bool)->bool.
        ARBITRARY UNION_OF ((\s. FINITE s /\ ~(s = {})) INTERSECTION_OF u) =
        ARBITRARY UNION_OF (FINITE INTERSECTION_OF u relative_to UNIONS u)
Proof
  GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[REWRITE_RULE[IN_APP] SUBSET_DEF] THEN
  CONJ_TAC THEN Q.X_GEN_TAC `s:'a->bool` THENL
  [ (* goal 1 (of 2) *)
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] UNION_OF_MONO) THEN
    REWRITE_TAC[FORALL_INTERSECTION_OF] THEN Q.X_GEN_TAC `t:('a->bool)->bool` THEN
    STRIP_TAC THEN REWRITE_TAC[INTERSECTION_OF, relative_to] THEN
    Q.EXISTS_TAC `INTERS t:'a->bool` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[], ASM_SET_TAC[]],
    (* goal 2 (of 2) *)
    GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV) empty_rewrites
      [GSYM ARBITRARY_UNION_OF_IDEMPOT] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] UNION_OF_MONO) THEN
    SIMP_TAC std_ss [FORALL_RELATIVE_TO, FORALL_INTERSECTION_OF] THEN
    Q.X_GEN_TAC `t:('a->bool)->bool` THEN STRIP_TAC THEN
    ASM_CASES_TAC ``t:('a->bool)->bool = {}`` THENL
    [ (* goal 2.1 (of 2) *)
      ASM_REWRITE_TAC[INTERS_0, INTER_UNIV] THEN
      MATCH_MP_TAC ARBITRARY_UNION_OF_UNIONS THEN
      Q.X_GEN_TAC `r:'a->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC UNION_OF_INC THEN
      REWRITE_TAC[ARBITRARY] THEN MATCH_MP_TAC INTERSECTION_OF_INC THEN
      REWRITE_TAC[NOT_INSERT_EMPTY, FINITE_SING] THEN
      fs [IN_APP],
      (* goal 2.2 (of 2) *)
      MATCH_MP_TAC UNION_OF_INC THEN
      SIMP_TAC std_ss [ARBITRARY, INTERSECTION_OF] THEN
      Q.EXISTS_TAC `t:('a->bool)->bool` THEN ASM_SET_TAC[] ] ]
QED

Theorem OPEN_IN_RELATIVE_TO :
   !top s:'a->bool.
        (open_in top relative_to s) = open_in (subtopology top s)
Proof
  REWRITE_TAC[relative_to, OPEN_IN_SUBTOPOLOGY, FUN_EQ_THM] THEN
  MESON_TAC[INTER_COMM]
QED

Theorem CLOSED_IN_RELATIVE_TO :
   !top s:'a->bool.
        (closed_in top relative_to s) = closed_in (subtopology top s)
Proof
  REWRITE_TAC[relative_to, CLOSED_IN_SUBTOPOLOGY, FUN_EQ_THM] THEN
  MESON_TAC[INTER_COMM]
QED

(* ------------------------------------------------------------------------- *)
(* Continuous maps (ported from HOL-Light's metric.ml)                       *)
(* ------------------------------------------------------------------------- *)

(* NOTE: This makes REWRITE_TAC below behave like in HOL-Light *)
open Ho_Rewrite;

Definition continuous_map :
    continuous_map (top,top') (f :'a -> 'b) <=>
     (!x. x IN topspace top ==> f x IN topspace top') /\
     (!u. open_in top' u
          ==> open_in top {x | x IN topspace top /\ f x IN u})
End

Theorem CONTINUOUS_MAP :
   !top top' f.
        continuous_map (top,top') f <=>
       (IMAGE f (topspace top) SUBSET topspace top' /\
        !u. open_in top' u
            ==> open_in top {x | x IN topspace top /\ f x IN u})
Proof
  REWRITE_TAC[continuous_map, SUBSET_DEF, FORALL_IN_IMAGE]
QED

Theorem CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE :
  !top top' (f :'a->'b). continuous_map (top,top')  f
                     ==> IMAGE f (topspace top) SUBSET topspace top'
Proof
  REWRITE_TAC[continuous_map] THEN SET_TAC[]
QED

Theorem CONTINUOUS_MAP_ON_EMPTY :
   !top top' (f :'a->'b). topspace top = {} ==> continuous_map(top,top') f
Proof
  SIMP_TAC std_ss[continuous_map, NOT_IN_EMPTY, EMPTY_GSPEC, OPEN_IN_EMPTY]
QED

Theorem CONTINUOUS_MAP_INTO_EMPTY :
   !top top' (f :'a->'b).
        topspace top' = {}
        ==> (continuous_map(top,top') f <=> topspace top = {})
Proof
  REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC[CONTINUOUS_MAP_ON_EMPTY] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
  ASM_SET_TAC[]
QED

val _ = export_theory();

(* References:

  [1] J. L. Kelley, General Topology. Springer Science & Business Media, 1975.

 *)
