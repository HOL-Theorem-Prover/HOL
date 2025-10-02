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
(*  General topological and metric spaces (from hol-light's metric.ml)       *)
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
Theory topology
Ancestors
  pair combin pred_set arithmetic relation cardinal
Libs
  boolSimps simpLib mesonLib metisLib pairLib tautLib hurdUtils


fun METIS ths tm = prove(tm,METIS_TAC ths);

val DISC_RW_KILL = DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
                   POP_ASSUM K_TAC;

(* Begin of minimal hol-light compatibility layer *)
Theorem IMP_CONJ      = cardinalTheory.CONJ_EQ_IMP
Theorem IMP_IMP       = boolTheory.AND_IMP_INTRO
Theorem EQ_IMP        = boolTheory.EQ_IMPLIES

Theorem FINITE_SUBSET = pred_setTheory.SUBSET_FINITE_I

Theorem FINITE_INDUCT_STRONG :
   !P:('a->bool)->bool.
        P {} /\ (!x s. P s /\ ~(x IN s) /\ FINITE s ==> P(x INSERT s))
        ==> !s. FINITE s ==> P s
Proof
   METIS_TAC [FINITE_INDUCT]
QED

val REPLICATE_TAC = NTAC;
val ANTS_TAC = impl_tac;

Theorem LEFT_AND_EXISTS_THM :
   !P Q. (?(x :'a). P x) /\ Q <=> (?(x :'a). P x /\ Q)
Proof
   METIS_TAC []
QED

Theorem RIGHT_AND_EXISTS_THM :
   !P Q. P /\ (?(x :'a). Q x) <=> (?(x :'a). P /\ Q x)
Proof
   METIS_TAC []
QED

Theorem FORALL_UNWIND_THM2 :
   !P (a :'a). (!x. x = a ==> P x) <=> P a
Proof
   METIS_TAC []
QED

Theorem FORALL_UNWIND_THM1 :
   !P (a :'a). (!x. a = x ==> P x) <=> P a
Proof
  REPEAT GEN_TAC THEN CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  MATCH_ACCEPT_TAC FORALL_UNWIND_THM2
QED

val SUBSET_DIFF = DIFF_SUBSET; (* |- !s t. s DIFF t SUBSET s *)
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

Theorem ISTOPOLOGY_OPEN_IN:   !top. istopology (open_in top)
Proof
    PROVE_TAC [topology_tybij]
QED

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
Theorem open_topspace:   !top. open top ==> (topspace top = UNIV)
Proof
    GEN_TAC >> REWRITE_TAC [open_DEF]
 >> DISCH_TAC >> REWRITE_TAC [EXTENSION]
 >> REWRITE_TAC [topspace, IN_UNIV, IN_BIGUNION]
 >> GEN_TAC >> Q.EXISTS_TAC `UNIV`
 >> REWRITE_TAC [IN_UNIV, GSPECIFICATION]
 >> Q.EXISTS_TAC `UNIV` >> BETA_TAC
 >> ASM_SIMP_TAC std_ss []
QED

(* ------------------------------------------------------------------------- *)
(* Main properties of open sets.                                             *)
(* ------------------------------------------------------------------------- *)

Theorem OPEN_IN_CLAUSES:
   !top.
        open_in top {} /\
        (!s t. open_in top s /\ open_in top t ==> open_in top (s INTER t)) /\
        (!k. (!s. s IN k ==> open_in top s) ==> open_in top (BIGUNION k))
Proof
  SIMP_TAC std_ss [IN_DEF, SUBSET_DEF,
  SIMP_RULE std_ss [istopology, IN_DEF, SUBSET_DEF] ISTOPOLOGY_OPEN_IN]
QED

Theorem OPEN_IN_SUBSET:
   !top s. open_in top s ==> s SUBSET (topspace top)
Proof
  REWRITE_TAC[topspace] THEN SET_TAC[]
QED

Theorem OPEN_IN_EMPTY:
   !top. open_in top {}
Proof
  REWRITE_TAC[OPEN_IN_CLAUSES]
QED

Theorem OPEN_IN_INTER:
   !top s t. open_in top s /\ open_in top t ==> open_in top (s INTER t)
Proof
  REWRITE_TAC[OPEN_IN_CLAUSES]
QED

Theorem OPEN_IN_BIGUNION:
   !top k. (!s. s IN k ==> open_in top s) ==> open_in top (BIGUNION k)
Proof
  REWRITE_TAC[OPEN_IN_CLAUSES]
QED

Theorem OPEN_IN_UNIONS[local] = OPEN_IN_BIGUNION

Theorem BIGUNION_2:
   !s t. BIGUNION {s;t} = s UNION t
Proof
  SET_TAC[]
QED

Theorem OPEN_IN_UNION:
   !top s t. open_in top s /\ open_in top t ==> open_in top (s UNION t)
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM BIGUNION_2] THEN
  MATCH_MP_TAC OPEN_IN_BIGUNION THEN REPEAT (POP_ASSUM MP_TAC) THEN SET_TAC[]
QED

Theorem OPEN_IN_TOPSPACE:
   !top. open_in top (topspace top)
Proof
  SIMP_TAC std_ss [topspace, OPEN_IN_BIGUNION, GSPECIFICATION]
QED

Theorem OPEN_IN_BIGINTER:
   !top s:('a->bool)->bool.
        FINITE s /\ ~(s = {}) /\ (!t. t IN s ==> open_in top t)
        ==> open_in top (BIGINTER s)
Proof
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
  MATCH_MP_TAC OPEN_IN_INTER THEN ASM_SIMP_TAC std_ss []
QED

Theorem OPEN_IN_INTERS[local] = OPEN_IN_BIGINTER

Theorem OPEN_IN_SUBOPEN:
   !top s:'a->bool.
        open_in top s <=>
        !x. x IN s ==> ?t. open_in top t /\ x IN t /\ t SUBSET s
Proof
  REPEAT GEN_TAC THEN EQ_TAC THENL [PROVE_TAC[SUBSET_REFL], ALL_TAC] THEN
  SIMP_TAC std_ss [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] THEN
  REWRITE_TAC[DECIDE ``a ==> b /\ c <=> (a ==> b) /\ (a ==> c)``] THEN
  SIMP_TAC std_ss [FORALL_AND_THM, GSYM LEFT_EXISTS_IMP_THM] THEN
  ONCE_REWRITE_TAC[GSYM FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_BIGUNION) THEN
  MATCH_MP_TAC EQ_IMPLIES THEN AP_TERM_TAC THEN REPEAT (POP_ASSUM MP_TAC) THEN
  SET_TAC[]
QED

(*---------------------------------------------------------------------------*)
(* Characterize a neighbourhood of a point relative to a topology            *)
(*---------------------------------------------------------------------------*)

Definition neigh:
  neigh(top)(N,(x:'a)) = ?P. (open_in top) P /\ P SUBSET N /\ P x /\
                             N SUBSET topspace top
End

Theorem neigh_def :
    !top N x. neigh top (N,x) <=>
              ?P. open_in top P /\ P SUBSET N /\ x IN P /\ N SUBSET topspace top
Proof
    REWRITE_TAC [neigh, IN_APP]
QED

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

Theorem OPEN_SUBOPEN:
    !S' top. open_in(top) S' <=>
             !x:'a. S' x ==> ?P. P x /\ open_in(top) P /\ P SUBSET S'
Proof
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
      SIMP_TAC (srw_ss()) []]]
QED

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

Theorem OPEN_NEIGH' :
    !A top. open_in(top) A <=> !x. x IN A ==> ?N. neigh(top)(N,x) /\ N SUBSET A
Proof
    REWRITE_TAC [OPEN_NEIGH, IN_APP]
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

Theorem closed_topspace:   !top. closed top ==> (topspace top = UNIV)
Proof
    GEN_TAC >> REWRITE_TAC [closed_DEF, closed_in]
 >> REWRITE_TAC [UNIV_SUBSET]
 >> STRIP_TAC >> ASM_REWRITE_TAC []
QED

(* original definition of "closed_in" in HOL4 *)
Theorem CLOSED_IN_OPEN_IN_COMPL:
    !top. closed top ==> (!s. closed_in top s = open_in top (COMPL s))
Proof
    rpt STRIP_TAC
 >> IMP_RES_TAC closed_topspace
 >> ASM_REWRITE_TAC [closed_in, GSYM COMPL_DEF, SUBSET_UNIV]
QED

Theorem CLOSED_IN_SUBSET:
   !top s. closed_in top s ==> s SUBSET (topspace top)
Proof
  PROVE_TAC[closed_in]
QED

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

Theorem OPEN_IN_CLOSED_IN:
   !top s. s SUBSET topspace top
       ==> (open_in top s <=> closed_in top (topspace top DIFF s))
Proof
  SIMP_TAC std_ss [OPEN_IN_CLOSED_IN_EQ]
QED

Theorem OPEN_IN_DIFF:
   !top s t:'a->bool.
      open_in top s /\ closed_in top t ==> open_in top (s DIFF t)
Proof
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN ``s DIFF t :'a->bool = s INTER (topspace top DIFF t)``
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[],
    MATCH_MP_TAC OPEN_IN_INTER THEN PROVE_TAC[closed_in]]
QED

Theorem CLOSED_IN_DIFF:
   !top s t:'a->bool.
        closed_in top s /\ open_in top t ==> closed_in top (s DIFF t)
Proof
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN ``s DIFF t :'a->bool = s INTER (topspace top DIFF t)``
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP CLOSED_IN_SUBSET) THEN SET_TAC[],
    MATCH_MP_TAC CLOSED_IN_INTER THEN PROVE_TAC[OPEN_IN_CLOSED_IN_EQ]]
QED

Theorem CLOSED_IN_BIGUNION:
   !top s. FINITE s /\ (!t. t IN s ==> closed_in top t)
           ==> closed_in top (BIGUNION s)
Proof
  GEN_TAC THEN REWRITE_TAC[GSYM AND_IMP_INTRO] THEN
  KNOW_TAC ``!s. ((!t. t IN s ==> closed_in top t) ==>
                   closed_in top (BIGUNION s)) =
             (\s. (!t. t IN s ==> closed_in top t) ==>
                   closed_in top (BIGUNION s)) s`` THENL
  [FULL_SIMP_TAC std_ss [], ALL_TAC] THEN DISC_RW_KILL THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  REWRITE_TAC[BIGUNION_INSERT, BIGUNION_EMPTY, CLOSED_IN_EMPTY, IN_INSERT] THEN
  PROVE_TAC[CLOSED_IN_UNION]
QED

(*---------------------------------------------------------------------------*)
(* Define limit point in topological space                                   *)
(*---------------------------------------------------------------------------*)

Definition limpt:
  limpt(top) x S' <=>
  x IN topspace top /\
  !N:'a->bool. neigh(top)(N,x) ==> ?y. ~(x = y) /\ S' y /\ N y
End

(* Alternative characterisation without needing neigh, but using IN, rather
   than application. x is a limit point in A if any neighbour set U containing
   x, also contains a different point y of A, i.e. x has neighbour points at
   any "close" distance.
 *)
Theorem limpt_thm:
    !top x A. limpt top (x :'a) A <=>
              x IN topspace top /\
              !U. open_in(top) U /\ x IN U ==> ?y. y IN U /\ y IN A /\ y <> x
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

(* HOL-Light: parse_as_infix("hull",(21,"left"));; *)
val _ = set_fixity "hull" (Infix(NONASSOC, 499));

val hull = new_definition ("hull",
  ``P hull s = BIGINTER {t | P t /\ s SUBSET t}``);

Theorem HULL_P:
   !P s. P s ==> (P hull s = s)
Proof
  SIMP_TAC std_ss [hull, EXTENSION, IN_BIGINTER, GSPECIFICATION] THEN
  MESON_TAC[SUBSET_DEF]
QED

Theorem P_HULL:
   !P s. (!f. (!s. s IN f ==> P s) ==> P(BIGINTER f)) ==> P(P hull s)
Proof
  REWRITE_TAC[hull] THEN SIMP_TAC std_ss [GSPECIFICATION]
QED

Theorem HULL_EQ:
   !P s. (!f. (!s. s IN f ==> P s) ==> P(BIGINTER f))
         ==> ((P hull s = s) <=> P s)
Proof
  MESON_TAC[P_HULL, HULL_P]
QED

Theorem HULL_HULL:
   !P s. P hull (P hull s) = P hull s
Proof
  SIMP_TAC std_ss [hull, EXTENSION, IN_BIGINTER, GSPECIFICATION, SUBSET_DEF] >>
  METIS_TAC[]
QED

Theorem HULL_SUBSET:
   !P s. s SUBSET (P hull s)
Proof
  SIMP_TAC std_ss [hull,SUBSET_DEF,IN_BIGINTER,GSPECIFICATION] >> MESON_TAC[]
QED

Theorem HULL_MONO:
   !P s t. s SUBSET t ==> (P hull s) SUBSET (P hull t)
Proof
   SIMP_TAC std_ss [hull, SUBSET_DEF, IN_BIGINTER, GSPECIFICATION] THEN
   METIS_TAC[]
QED

Theorem HULL_ANTIMONO:
   !P Q s. P SUBSET Q ==> (Q hull s) SUBSET (P hull s)
Proof
  SIMP_TAC std_ss [SUBSET_DEF, hull, IN_BIGINTER, GSPECIFICATION] THEN
  MESON_TAC[IN_DEF]
QED

Theorem HULL_MINIMAL:
   !P s t. s SUBSET t /\ P t ==> (P hull s) SUBSET t
Proof
  SIMP_TAC std_ss [hull,SUBSET_DEF,IN_BIGINTER,GSPECIFICATION] >> METIS_TAC[]
QED

Theorem SUBSET_HULL:
   !P s t. P t ==> ((P hull s) SUBSET t <=> s SUBSET t)
Proof
  SIMP_TAC std_ss [hull,SUBSET_DEF,IN_BIGINTER,GSPECIFICATION] >> METIS_TAC[]
QED

Theorem HULL_UNIQUE:
   !P s t. s SUBSET t /\ P t /\ (!t'. s SUBSET t' /\ P t' ==> t SUBSET t')
           ==> (P hull s = t)
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  SIMP_TAC std_ss [hull, SUBSET_DEF, IN_BIGINTER, GSPECIFICATION] THEN
  ASM_MESON_TAC[SUBSET_HULL, SUBSET_DEF]
QED

Theorem HULL_UNION_SUBSET:
   !P s t. (P hull s) UNION (P hull t) SUBSET (P hull (s UNION t))
Proof
  SIMP_TAC std_ss [UNION_SUBSET, HULL_MONO, SUBSET_UNION]
QED

Theorem HULL_UNION:
   !P s t. P hull (s UNION t) = P hull ((P hull s) UNION (P hull t))
Proof
  REPEAT STRIP_TAC >> ONCE_REWRITE_TAC[hull] >>
  AP_TERM_TAC >> SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, UNION_SUBSET] >>
  METIS_TAC[SUBSET_HULL]
QED

Theorem HULL_UNION_LEFT:
   !P s t:'a->bool.
        P hull (s UNION t) = P hull ((P hull s) UNION t)
Proof
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[hull] THEN
  AP_TERM_TAC THEN SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, UNION_SUBSET] >>
  METIS_TAC[SUBSET_HULL]
QED

Theorem HULL_UNION_RIGHT:
   !P s t:'a->bool.
        P hull (s UNION t) = P hull (s UNION (P hull t))
Proof
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[hull] THEN
  AP_TERM_TAC THEN SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, UNION_SUBSET] >>
  MESON_TAC[SUBSET_HULL]
QED

Theorem HULL_REDUNDANT_EQ:
   !P a s. a IN (P hull s) <=> (P hull (a INSERT s) = P hull s)
Proof
  REWRITE_TAC[hull] THEN SET_TAC[]
QED

Theorem HULL_REDUNDANT:
   !P a s. a IN (P hull s) ==> (P hull (a INSERT s) = P hull s)
Proof
  REWRITE_TAC[HULL_REDUNDANT_EQ]
QED

Theorem HULL_INDUCT:
   !P p s. (!x:'a. x IN s ==> p x) /\ P {x | p x}
           ==> !x. x IN P hull s ==> p x
Proof
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [``P:('a->bool)->bool``, ``s:'a->bool``, ``{x:'a | p x}``]
                HULL_MINIMAL) THEN
  SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION]
QED

Theorem HULL_INC:
   !P s x. x IN s ==> x IN P hull s
Proof
  MESON_TAC[REWRITE_RULE[SUBSET_DEF] HULL_SUBSET]
QED

Theorem HULL_IMAGE_SUBSET:
   !P f s. (P (P hull s)) /\ (!s. P s ==> P(IMAGE f s))
           ==> (P hull (IMAGE f s)) SUBSET ((IMAGE f (P hull s)))
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN
  ASM_SIMP_TAC std_ss [IMAGE_SUBSET, HULL_SUBSET]
QED

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

Theorem IS_HULL:
   !P s. (!f. (!s. s IN f ==> P s) ==> P(BIGINTER f))
         ==> (P s <=> ?t. s = P hull t)
Proof
  MESON_TAC[HULL_P, P_HULL]
QED

Theorem HULLS_EQ:
   !P s t.
        (!f. (!s. s IN f ==> P s) ==> P (BIGINTER f)) /\
        s SUBSET (P hull t) /\ t SUBSET (P hull s)
        ==> (P hull s = P hull t)
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  CONJ_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN
  ASM_SIMP_TAC std_ss [P_HULL]
QED

Theorem HULL_P_AND_Q:
   !P Q. (!f. (!s. s IN f ==> P s) ==> P(BIGINTER f)) /\
         (!f. (!s. s IN f ==> Q s) ==> Q(BIGINTER f)) /\
         (!s. Q s ==> Q(P hull s))
         ==> ((\x. P x /\ Q x) hull s = P hull (Q hull s))
Proof
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HULL_UNIQUE THEN ASM_SIMP_TAC std_ss [HULL_INC, SUBSET_HULL] THEN
  ASM_MESON_TAC[P_HULL, HULL_SUBSET, SUBSET_TRANS]
QED

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

Theorem EXISTS_SUBSET_IMAGE :
   !P (f :'a->'b) s.
      (?t. t SUBSET IMAGE f s /\ P t) <=> (?t. t SUBSET s /\ P (IMAGE f t))
Proof
  REWRITE_TAC[SUBSET_IMAGE] THEN MESON_TAC[]
QED

Theorem FORALL_SUBSET_IMAGE :
   !P (f :'a->'b) s.
        (!t. t SUBSET IMAGE f s ==> P t) <=>
        (!t. t SUBSET s ==> P(IMAGE f t))
Proof
  REWRITE_TAC[SUBSET_IMAGE] THEN MESON_TAC[]
QED

Theorem SUBSET_IMAGE_INJ :
   !(f :'a->'b) s t.
        s SUBSET (IMAGE f t) <=>
        ?u. u SUBSET t /\
            (!x y. x IN u /\ y IN u ==> (f x = f y <=> x = y)) /\
            s = IMAGE f u
Proof
  REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC, MESON_TAC[IMAGE_SUBSET]] THEN
  DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP (SET_RULE
   “s SUBSET IMAGE f t ==> !x. x IN s ==> ?y. y IN t /\ f y = x”)) THEN
  REWRITE_TAC[SURJECTIVE_ON_RIGHT_INVERSE] THEN
  DISCH_THEN(X_CHOOSE_TAC “g:'b->'a”) THEN
  EXISTS_TAC “IMAGE (g :'b->'a) s” THEN ASM_SET_TAC[]
QED

Theorem EXISTS_SUBSET_IMAGE_INJ :
   !P (f :'a->'b) s.
    (?t. t SUBSET IMAGE f s /\ P t) <=>
    (?t. t SUBSET s /\
         (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y)) /\
         P (IMAGE f t))
Proof
  REWRITE_TAC[SUBSET_IMAGE_INJ] THEN METIS_TAC []
QED

Theorem FORALL_SUBSET_IMAGE_INJ :
   !P (f :'a->'b) s.
        (!t. t SUBSET IMAGE f s ==> P t) <=>
        (!t. t SUBSET s /\
             (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y))
             ==> P(IMAGE f t))
Proof
  REPEAT GEN_TAC THEN
  qabbrev_tac ‘Q = \t. t SUBSET IMAGE f s ==> P t’ \\
  qabbrev_tac ‘R = \t. t SUBSET s /\
                      (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y)) ==>
                       P (IMAGE f t)’ \\
  ‘$! Q <=> ~(?t. ~Q t)’ by rw [Abbr ‘Q’] >> POP_ORW \\
  ‘$! R <=> ~(?t. ~R t)’ by rw [Abbr ‘R’] >> POP_ORW \\
  simp[Abbr ‘Q’, Abbr ‘R’, NOT_IMP, EXISTS_SUBSET_IMAGE_INJ, GSYM CONJ_ASSOC]
QED

Theorem EXISTS_FINITE_SUBSET_IMAGE_INJ :
   !P (f :'a->'b) s.
    (?t. FINITE t /\ t SUBSET IMAGE f s /\ P t) <=>
    (?t. FINITE t /\ t SUBSET s /\
         (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y)) /\
         P (IMAGE f t))
Proof
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
  REPEAT GEN_TAC THEN SIMP_TAC std_ss[EXISTS_SUBSET_IMAGE_INJ] THEN
  AP_TERM_TAC THEN ABS_TAC THEN MESON_TAC[FINITE_IMAGE_INJ_EQ]
QED

Theorem FORALL_FINITE_SUBSET_IMAGE_INJ :
   !P (f :'a->'b) s.
        (!t. FINITE t /\ t SUBSET IMAGE f s ==> P t) <=>
        (!t. FINITE t /\ t SUBSET s /\
             (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y))
             ==> P(IMAGE f t))
Proof
  REPEAT GEN_TAC THEN
  qabbrev_tac ‘Q = \t. FINITE t /\ t SUBSET IMAGE f s ==> P t’ \\
  qabbrev_tac ‘R = \t. FINITE t /\ t SUBSET s /\
                      (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y)) ==>
                       P (IMAGE f t)’ \\
  ‘$! Q <=> ~(?t. ~Q t)’ by rw [Abbr ‘Q’] >> POP_ORW \\
  ‘$! R <=> ~(?t. ~R t)’ by rw [Abbr ‘R’] >> POP_ORW \\
  simp[Abbr ‘Q’, Abbr ‘R’, NOT_IMP, EXISTS_FINITE_SUBSET_IMAGE_INJ, GSYM CONJ_ASSOC]
QED

Theorem EXISTS_FINITE_SUBSET_IMAGE :
   !P (f :'a->'b) s.
      (?t. FINITE t /\ t SUBSET IMAGE f s /\ P t) <=>
      (?t. FINITE t /\ t SUBSET s /\ P (IMAGE f t))
Proof
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE_INJ] THEN MESON_TAC[],
    MESON_TAC[FINITE_IMAGE, IMAGE_SUBSET]]
QED

Theorem FORALL_FINITE_SUBSET_IMAGE :
   !P (f :'a->'b) s.
      (!t. FINITE t /\ t SUBSET IMAGE f s ==> P t) <=>
      (!t. FINITE t /\ t SUBSET s ==> P(IMAGE f t))
Proof
  REPEAT GEN_TAC THEN
  qabbrev_tac ‘Q = \t. FINITE t /\ t SUBSET IMAGE f s ==> P t’ \\
  qabbrev_tac ‘R = \t. FINITE t /\ t SUBSET s ==> P (IMAGE f t)’ \\
  ‘$! Q <=> ~(?t. ~Q t)’ by rw [Abbr ‘Q’] >> POP_ORW \\
  ‘$! R <=> ~(?t. ~R t)’ by rw [Abbr ‘R’] >> POP_ORW \\
  simp[Abbr ‘Q’, Abbr ‘R’, NOT_IMP, GSYM CONJ_ASSOC, EXISTS_FINITE_SUBSET_IMAGE]
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
(* (ported from HOL Light's sets.ml)                                         *)
(* ------------------------------------------------------------------------- *)

(* original priority in HOL-Light:
   parse_as_infix("UNION_OF",(20,"right"));;
   parse_as_infix("INTERSECTION_OF",(20,"right"));;
 *)
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
(* Continuous maps (ported from HOL-Light's Multivariate/metric.ml)          *)
(* ------------------------------------------------------------------------- *)

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
  SIMP_TAC std_ss[continuous_map, SUBSET_DEF, FORALL_IN_IMAGE]
QED

Theorem CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE :
  !top top' (f :'a->'b). continuous_map (top,top')  f
                     ==> IMAGE f (topspace top) SUBSET topspace top'
Proof
  SIMP_TAC std_ss[continuous_map] THEN SET_TAC[]
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

Theorem CONTINUOUS_MAP_CLOSED_IN :
    !top top' f:'a->'b.
         continuous_map (top,top') f <=>
         (!x. x IN topspace top ==> f x IN topspace top') /\
         (!c. closed_in top' c
              ==> closed_in top {x | x IN topspace top /\ f x IN c})
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[continuous_map] THEN
  MATCH_MP_TAC(TAUT `(p ==> (q <=> r)) ==> (p /\ q <=> p /\ r)`) THEN
  DISCH_TAC THEN EQ_TAC THEN DISCH_TAC THEN
 (* 2 subgoals, same tactics *)
  X_GEN_TAC “t:'b->bool” THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC “topspace top' DIFF t:'b->bool”) THEN
  ASM_SIMP_TAC std_ss[OPEN_IN_DIFF, CLOSED_IN_DIFF, OPEN_IN_TOPSPACE,
                      CLOSED_IN_TOPSPACE] THEN
  GEN_REWRITE_TAC LAND_CONV empty_rewrites[closed_in, OPEN_IN_CLOSED_IN_EQ] THEN
  SIMP_TAC std_ss[SUBSET_RESTRICT] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  ASM_SET_TAC[]
QED

Theorem OPEN_IN_CONTINUOUS_MAP_PREIMAGE :
    !f:'a->'b top top' u.
        continuous_map (top,top') f /\ open_in top' u
        ==> open_in top {x | x IN topspace top /\ f x IN u}
Proof
  REWRITE_TAC[continuous_map] THEN SET_TAC[]
QED

Theorem CLOSED_IN_CONTINUOUS_MAP_PREIMAGE :
    !f:'a->'b top top' c.
        continuous_map (top,top') f /\ closed_in top' c
        ==> closed_in top {x | x IN topspace top /\ f x IN c}
Proof
  REWRITE_TAC[CONTINUOUS_MAP_CLOSED_IN] THEN SET_TAC[]
QED

Theorem OPEN_IN_CONTINUOUS_MAP_PREIMAGE_GEN :
    !f:'a->'b top top' u v.
        continuous_map (top,top') f /\ open_in top u /\ open_in top' v
        ==> open_in top {x | x IN u /\ f x IN v}
Proof
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN “{x | x IN u /\ (f:'a->'b) x IN v} =
                u INTER {x | x IN topspace top /\ f x IN v}”
  SUBST1_TAC THENL
  [ REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET)) THEN SET_TAC[],
    MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
    ASM_MESON_TAC[] ]
QED

Theorem CLOSED_IN_CONTINUOUS_MAP_PREIMAGE_GEN :
    !f:'a->'b top top' u v.
        continuous_map (top,top') f /\ closed_in top u /\ closed_in top' v
        ==> closed_in top {x | x IN u /\ f x IN v}
Proof
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN “{x | x IN u /\ (f:'a->'b) x IN v} =
                u INTER {x | x IN topspace top /\ f x IN v}”
  SUBST1_TAC THENL
  [ REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP CLOSED_IN_SUBSET)) THEN SET_TAC[],
    MATCH_MP_TAC CLOSED_IN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN
    ASM_MESON_TAC[] ]
QED

Theorem CONTINUOUS_MAP_ID :
    !top:'a topology. continuous_map (top,top) (\x. x)
Proof
  SIMP_TAC std_ss[continuous_map] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC(MESON[] “(P x ==> x = y) ==> P x ==> P y”) THEN
  REWRITE_TAC[SET_RULE “u = {x | x IN s /\ x IN u} <=> u SUBSET s”] THEN
  REWRITE_TAC[OPEN_IN_SUBSET]
QED

Theorem TOPOLOGY_FINER_CONTINUOUS_ID :
    !top top':'a topology.
        topspace top' = topspace top
        ==> ((!s. open_in top s ==> open_in top' s) <=>
             continuous_map (top',top) (\x. x))
Proof
  REWRITE_TAC[continuous_map] THEN
  SIMP_TAC std_ss[OPEN_IN_SUBSET, SET_RULE
   “u SUBSET s ==> {x | x IN s /\ x IN u} = u”]
QED

Theorem CONTINUOUS_MAP_CONST :
    !(top1:'a topology) (top2:'b topology) c.
       continuous_map (top1,top2) (\x. c) <=>
       topspace top1 = {} \/ c IN topspace top2
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[continuous_map] THEN
  ASM_CASES_TAC “topspace top1:'a->bool = {}” THEN
  ASM_SIMP_TAC std_ss[NOT_IN_EMPTY, EMPTY_GSPEC, OPEN_IN_EMPTY] THEN
 (* one subgoal left *)
  ASM_CASES_TAC “(c:'b) IN topspace top2” THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC, ASM_SET_TAC[]] THEN
  X_GEN_TAC “u:'b->bool” THEN
  ASM_CASES_TAC “(c:'b) IN u” THEN
  ASM_SIMP_TAC std_ss[EMPTY_GSPEC, OPEN_IN_EMPTY] THEN
 (* one subgoal left *)
  REWRITE_TAC[SET_RULE “{x | x IN s} = s”, OPEN_IN_TOPSPACE]
QED

Theorem CONTINUOUS_MAP_COMPOSE :
    !top top' top'' (f:'a->'b) (g:'b->'c).
        continuous_map (top,top') f /\ continuous_map (top',top'') g
        ==> continuous_map (top,top'') (g o f)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[continuous_map, o_THM] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM_SET_TAC[], X_GEN_TAC “u:'c->bool”] THEN
  SUBGOAL_THEN
   “{x:'a | x IN topspace top /\ (g:'b->'c) (f x) IN u} =
    {x:'a | x IN topspace top /\ f x IN {y | y IN topspace top' /\ g y IN u}}”
  SUBST1_TAC THENL [ASM_SET_TAC[], ASM_SIMP_TAC std_ss[] ]
QED

(* |- (!x. P x ==> Q x) ==> (!x. P x) ==> !x. Q x *)
val MONO_FORALL = MONO_ALL;

Theorem CONTINUOUS_MAP_EQ :
    !top top' f (g:'a->'b).
        (!x. x IN topspace top ==> f x = g x) /\ continuous_map (top,top') f
        ==> continuous_map (top,top') g
Proof
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[continuous_map] THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL [ASM_SET_TAC[], ALL_TAC] THEN
  HO_MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_SET_TAC[]
QED

Theorem RESTRICTION_CONTINUOUS_MAP :
    !top top' (f:'a->'b) s.
        topspace top SUBSET s
        ==> (continuous_map (top,top') (RESTRICTION s f) <=>
             continuous_map (top,top') f)
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CONTINUOUS_MAP_EQ) THEN
  REWRITE_TAC[RESTRICTION] THEN ASM_SET_TAC[]
QED

Theorem CONTINUOUS_MAP_IN_SUBTOPOLOGY :
    !top top' s f:'a->'b.
     continuous_map (top,subtopology top' s) f <=>
     continuous_map (top,top') f /\ IMAGE f (topspace top) SUBSET s
Proof
  REPEAT GEN_TAC THEN
  REWRITE_TAC[continuous_map, TOPSPACE_SUBTOPOLOGY, IN_INTER,
    OPEN_IN_SUBTOPOLOGY] THEN
  EQ_TAC THEN SIMP_TAC std_ss[] THENL
 [ (* goal 1 (of 2) *)
   STRIP_TAC THEN CONJ_TAC THENL [ALL_TAC, ASM_SET_TAC[]] THEN
   rpt STRIP_TAC THEN
   SUBGOAL_THEN
     “{x:'a | x IN topspace top /\ f x:'b IN u} =
      {x | x IN topspace top /\ f x IN u INTER s}”
     (fn th => REWRITE_TAC[th])
   >- (Q.PAT_X_ASSUM ‘!x. x IN topspace top ==> _’ MP_TAC \\
       SET_TAC []) \\
   FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC “u:'b->bool” THEN
   ASM_REWRITE_TAC[],
   (* goal 2 (of 2) *)
   STRIP_TAC THEN
   CONJ_TAC THENL [ASM_SET_TAC[], ALL_TAC] THEN
   rpt STRIP_TAC THEN
   POP_ORW THEN
   SUBGOAL_THEN
     “{x:'a | x IN topspace top /\ f x:'b IN t INTER s} =
      {x | x IN topspace top /\ f x IN t}”
     (fn th => ASM_SIMP_TAC std_ss[th]) THEN
   ASM_SET_TAC[] ]
QED

Theorem CONTINUOUS_MAP_FROM_SUBTOPOLOGY :
    !top top' (f:'a->'b) s.
        continuous_map (top,top') f
        ==> continuous_map (subtopology top s,top') f
Proof
  SIMP_TAC std_ss[continuous_map, TOPSPACE_SUBTOPOLOGY, IN_INTER] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC “u:'b->bool” THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
  EXISTS_TAC “{x | x IN topspace top /\ (f:'a->'b) x IN u}” THEN
  ASM_SIMP_TAC std_ss[] THEN SET_TAC[]
QED

Theorem CONTINUOUS_MAP_INTO_FULLTOPOLOGY :
    !top top' (f:'a->'b) t.
        continuous_map (top,subtopology top' t) f
        ==> continuous_map (top,top') f
Proof
  SIMP_TAC std_ss[CONTINUOUS_MAP_IN_SUBTOPOLOGY]
QED

Theorem CONTINUOUS_MAP_INTO_SUBTOPOLOGY :
    !top top' (f:'a->'b) t.
        continuous_map (top,top') f /\
        IMAGE f (topspace top) SUBSET t
        ==> continuous_map (top,subtopology top' t) f
Proof
  SIMP_TAC std_ss[CONTINUOUS_MAP_IN_SUBTOPOLOGY]
QED

Theorem CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO :
    !top top' f s t.
           continuous_map (subtopology top t,top') f /\ s SUBSET t
           ==> continuous_map (subtopology top s,top') f
Proof
  MESON_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY, SUBTOPOLOGY_SUBTOPOLOGY,
            SET_RULE “s SUBSET t ==> t INTER s = s”]
QED

(* ------------------------------------------------------------------------- *)
(* Pointwise continuity in topological spaces.                               *)
(*  (ported from HOL-Light's Multivariate/metric.ml)                         *)
(* ------------------------------------------------------------------------- *)

Definition topcontinuous_at :
    topcontinuous_at top top' (f :'a -> 'b) x <=>
     x IN topspace top /\
     (!x. x IN topspace top ==> f x IN topspace top') /\
     (!v. open_in top' v /\ f x IN v
          ==> (?u. open_in top u /\ x IN u /\ (!y. y IN u ==> f y IN v)))
End

Theorem OPEN_IN_SUBSET_TOPSPACE :
    !top s. open_in top s ==> s SUBSET topspace top
Proof
    rw [SUBSET_DEF, topspace]
 >> Q.EXISTS_TAC ‘s’ >> art []
QED

(*
Theorem TOPCONTINUOUS_AT_ATPOINTOF :
   !top top' (f:'a->'b) x.
        topcontinuous_at top top' f x <=>
        x IN topspace top /\
        (!x. x IN topspace top ==> f x IN topspace top') /\
        limit top' f (f x) (atpointof top x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[topcontinuous_at] THEN
  MATCH_MP_TAC(TAUT
   `(p /\ q ==> (r <=> s)) ==> (p /\ q /\ r <=> p /\ q /\ s)`) THEN
  STRIP_TAC THEN ASM_SIMP_TAC[LIMIT_ATPOINTOF] THEN
  AP_TERM_TAC THEN ABS_TAC THEN SET_TAC[]);;
 *)

Theorem CONTINUOUS_MAP_EQ_TOPCONTINUOUS_AT :
    !top top' f.
        continuous_map (top,top') f <=>
        !x. x IN topspace top ==> topcontinuous_at top top' f x
Proof
    rw [continuous_map, topcontinuous_at]
 >> reverse EQ_TAC >> rw [] (* 3 subgoals *)
 >- (Q.PAT_X_ASSUM ‘!x. x IN topspace top ==> _’ (MP_TAC o Q.SPEC ‘x’) >> rw [])
 >- (rw [OPEN_NEIGH] \\
     Q.PAT_X_ASSUM ‘!x. x IN topspace top ==> _’ (MP_TAC o Q.SPEC ‘x’) >> rw [] \\
     POP_ASSUM (MP_TAC o Q.SPEC ‘u’) >> rw [] \\
     rename1 ‘x IN N’ \\
     Q.EXISTS_TAC ‘N’ \\
    ‘N SUBSET topspace top’ by PROVE_TAC [OPEN_IN_SUBSET_TOPSPACE] \\
     reverse CONJ_TAC
     >- (POP_ASSUM MP_TAC >> rw [SUBSET_DEF]) \\
     rw [neigh] \\
     Q.EXISTS_TAC ‘N’ >> fs [IN_APP])
 >> Q.PAT_X_ASSUM ‘!u. open_in top' u ==> _’ (MP_TAC o Q.SPEC ‘v’) >> rw []
 >> Q.EXISTS_TAC ‘{x | x IN topspace top /\ f x IN v}’ >> rw []
QED

(* ------------------------------------------------------------------------- *)
(* Derived set (set of limit points).                                        *)
(*  (ported from HOL-Light's Multivariate/metric.ml)                         *)
(* ------------------------------------------------------------------------- *)

(* parse_as_infix("derived_set_of",(21,"right"));; *)
val _ = set_fixity "derived_set_of" (Infixr 602);

Definition derived_set_of :
   top derived_set_of s =
   {(x :'a) | x IN topspace top /\
              !t. x IN t /\ open_in top t ==>
                  ?y. ~(y = x) /\ y IN s /\ y IN t}
End

Theorem DERIVED_SET_OF_RESTRICT :
   !top (s :'a set).
     top derived_set_of s = top derived_set_of (topspace top INTER s)
Proof
  rw [derived_set_of, Once EXTENSION] THEN
  MESON_TAC[REWRITE_RULE[SUBSET_DEF] OPEN_IN_SUBSET]
QED

Theorem IN_DERIVED_SET_OF :
   !top s (x :'a).
     x IN top derived_set_of s <=>
     x IN topspace top /\
     (!t. x IN t /\ open_in top t ==> ?y. ~(y = x) /\ y IN s /\ y IN t)
Proof
  rw [derived_set_of]
QED

Theorem DERIVED_SET_OF_SUBSET_TOPSPACE :
   !top (s :'a set). top derived_set_of s SUBSET topspace top
Proof
  REWRITE_TAC[derived_set_of] THEN SET_TAC[]
QED

Theorem DERIVED_SET_OF_SUBTOPOLOGY :
   !top u (s :'a set).
        (subtopology top u) derived_set_of s =
        u INTER top derived_set_of (u INTER s)
Proof
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I empty_rewrites[EXTENSION] THEN
  REWRITE_TAC[derived_set_of, OPEN_IN_SUBTOPOLOGY, TOPSPACE_SUBTOPOLOGY] THEN
  simp[RIGHT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM] THEN
  ASM_SET_TAC[]
QED

Theorem DERIVED_SET_OF_SUBSET_SUBTOPOLOGY :
   !top s (t :'a set). (subtopology top s) derived_set_of t SUBSET s
Proof
  SIMP_TAC std_ss[DERIVED_SET_OF_SUBTOPOLOGY, INTER_SUBSET]
QED

Theorem DERIVED_SET_OF_EMPTY :
   !(top:'a topology). top derived_set_of {} = {}
Proof
  REWRITE_TAC[EXTENSION, IN_DERIVED_SET_OF, NOT_IN_EMPTY] THEN
  MESON_TAC[OPEN_IN_TOPSPACE]
QED

Theorem DERIVED_SET_OF_MONO :
   !top s (t :'a set).
        s SUBSET t ==> top derived_set_of s SUBSET top derived_set_of t
Proof
  REWRITE_TAC[derived_set_of] THEN SET_TAC[]
QED

Theorem DERIVED_SET_OF_UNION :
   !top s (t :'a set).
       top derived_set_of (s UNION t) =
       top derived_set_of s UNION top derived_set_of t
Proof
  REPEAT GEN_TAC THEN
  SIMP_TAC std_ss[GSYM SUBSET_ANTISYM_EQ, UNION_SUBSET, DERIVED_SET_OF_MONO,
                  SUBSET_UNION] THEN
  REWRITE_TAC[SUBSET_DEF, IN_DERIVED_SET_OF, IN_UNION] THEN
  X_GEN_TAC “x :'a” THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC I empty_rewrites[GSYM CONTRAPOS_THM] THEN
  SIMP_TAC std_ss[DE_MORGAN_THM, NOT_FORALL_THM, NOT_IMP] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_TAC “u :'a set”) (X_CHOOSE_TAC “v :'a set”)) THEN
  EXISTS_TAC “u INTER (v :'a set)” THEN
  ASM_SIMP_TAC std_ss[OPEN_IN_INTER, IN_INTER] THEN ASM_MESON_TAC[]
QED

Theorem DERIVED_SET_OF_UNIONS :
   !top (f :('a set) set).
        FINITE f
        ==> top derived_set_of (UNIONS f) =
            UNIONS {top derived_set_of s | s IN f}
Proof
  GEN_TAC THEN HO_MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC std_ss[UNIONS_0, NOT_IN_EMPTY, UNIONS_INSERT, DERIVED_SET_OF_EMPTY,
                  DERIVED_SET_OF_UNION, SIMPLE_IMAGE, IMAGE_CLAUSES]
QED

Theorem DERIVED_SET_OF_TOPSPACE :
   !(top :'a topology).
        top derived_set_of (topspace top) =
        {x | x IN topspace top /\ ~open_in top {x}}
Proof
  GEN_TAC THEN simp[EXTENSION, derived_set_of] THEN
  X_GEN_TAC “a :'a” THEN ASM_CASES_TAC “(a :'a) IN topspace top” THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THEN DISCH_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC “{a :'a}”) THEN ASM_SET_TAC[],
    X_GEN_TAC “u :'a set” THEN STRIP_TAC THEN
    ASM_CASES_TAC “u = {a :'a}” THENL [ASM_MESON_TAC[], ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM_SET_TAC[]]
QED

Theorem OPEN_IN_INTER_DERIVED_SET_OF_SUBSET :
   !top s (t :'a set).
       open_in top s
       ==> s INTER top derived_set_of t SUBSET top derived_set_of (s INTER t)
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[derived_set_of] THEN
  simp [SUBSET_DEF, IN_INTER] THEN
  X_GEN_TAC “x :'a” THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC “u :'a set” THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC “s INTER (u :'a set)”) THEN
  ASM_SIMP_TAC std_ss[OPEN_IN_INTER, IN_INTER] THEN MESON_TAC[]
QED

Theorem OPEN_IN_INTER_DERIVED_SET_OF_EQ :
   !top s (t :'a set).
        open_in top s
        ==> s INTER top derived_set_of t =
            s INTER top derived_set_of (s INTER t)
Proof
  SIMP_TAC std_ss[GSYM SUBSET_ANTISYM_EQ, INTER_SUBSET, SUBSET_INTER] THEN
  SIMP_TAC std_ss[OPEN_IN_INTER_DERIVED_SET_OF_SUBSET] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE “s SUBSET t ==> u INTER s SUBSET t”) THEN
  MATCH_MP_TAC DERIVED_SET_OF_MONO THEN SET_TAC[]
QED

(* ------------------------------------------------------------------------- *)
(* Closure with respect to a topological space.                              *)
(*  (ported from HOL-Light's Multivariate/metric.ml)                         *)
(* ------------------------------------------------------------------------- *)

(* parse_as_infix("closure_of",(21,"right"));; *)
val _ = set_fixity "closure_of" (Infixr 602);

Definition closure_of :
   top closure_of s =
   {(x :'a) | x IN topspace top /\
              !t. x IN t /\ open_in top t ==> ?y. y IN s /\ y IN t}
End

Theorem CLOSURE_OF_RESTRICT :
    !top (s:'a->bool). top closure_of s = top closure_of (topspace top INTER s)
Proof
    rw [closure_of, Once EXTENSION, IN_INTER]
 >> MESON_TAC[REWRITE_RULE[SUBSET_DEF] OPEN_IN_SUBSET]
QED

Theorem IN_CLOSURE_OF :
   !top s (x :'a).
     x IN top closure_of s <=>
     x IN topspace top /\
     (!t. x IN t /\ open_in top t ==> ?y. y IN s /\ y IN t)
Proof
    rw [closure_of]
QED

Theorem CLOSURE_OF :
   !top (s :'a set).
     top closure_of s =
     topspace top INTER (s UNION top derived_set_of s)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION] THEN
  Q.X_GEN_TAC ‘x’ THEN
  REWRITE_TAC[IN_CLOSURE_OF, IN_DERIVED_SET_OF, IN_UNION, IN_INTER] THEN
  Cases_on ‘x IN topspace top’ THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[]
QED

Theorem CLOSURE_OF_ALT :
   !top (s :'a set).
        top closure_of s = topspace top INTER s UNION top derived_set_of s
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSURE_OF] THEN
  MP_TAC(Q.SPECL [`top`, `s`] DERIVED_SET_OF_SUBSET_TOPSPACE) THEN
  SET_TAC[]
QED

Theorem DERIVED_SET_OF_SUBSET_CLOSURE_OF :
   !top (s :'a set). top derived_set_of s SUBSET top closure_of s
Proof
  REWRITE_TAC[CLOSURE_OF, SUBSET_INTER, DERIVED_SET_OF_SUBSET_TOPSPACE] THEN
  SIMP_TAC std_ss[SUBSET_UNION]
QED

Theorem CLOSURE_OF_SUBTOPOLOGY :
   !top u (s :'a set).
      (subtopology top u) closure_of s = u INTER (top closure_of (u INTER s))
Proof
  SIMP_TAC std_ss[CLOSURE_OF, TOPSPACE_SUBTOPOLOGY, DERIVED_SET_OF_SUBTOPOLOGY] THEN
  SET_TAC[]
QED

Theorem CLOSURE_OF_EMPTY :
   !top. top closure_of ({} :'a set) = {}
Proof
  REWRITE_TAC[EXTENSION, IN_CLOSURE_OF, NOT_IN_EMPTY] THEN
  MESON_TAC[OPEN_IN_TOPSPACE]
QED

Theorem CLOSURE_OF_TOPSPACE :
   !(top :'a topology). top closure_of topspace top = topspace top
Proof
  REWRITE_TAC[EXTENSION, IN_CLOSURE_OF] THEN MESON_TAC[]
QED

Theorem CLOSURE_OF_UNIV :
   !top. top closure_of UNIV = topspace top
Proof
  REWRITE_TAC[closure_of] THEN SET_TAC[]
QED

Theorem CLOSURE_OF_SUBSET_TOPSPACE :
   !top (s :'a set). top closure_of s SUBSET topspace top
Proof
  REWRITE_TAC[closure_of] THEN SET_TAC[]
QED

Theorem CLOSURE_OF_SUBSET_SUBTOPOLOGY :
   !top s (t :'a set). (subtopology top s) closure_of t SUBSET s
Proof
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY, closure_of] THEN SET_TAC[]
QED

Theorem CLOSURE_OF_MONO :
   !top s (t :'a set).
        s SUBSET t ==> top closure_of s SUBSET top closure_of t
Proof
  REWRITE_TAC[closure_of] THEN SET_TAC[]
QED

Theorem CLOSURE_OF_SUBTOPOLOGY_SUBSET :
   !top s (u :'a set).
        (subtopology top u) closure_of s SUBSET (top closure_of s)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY] THEN
  MATCH_MP_TAC(SET_RULE “t SUBSET u ==> s INTER t SUBSET u”) THEN
  MATCH_MP_TAC CLOSURE_OF_MONO THEN REWRITE_TAC[INTER_SUBSET]
QED

Theorem CLOSURE_OF_SUBTOPOLOGY_MONO :
   !top s t (u :'a set).
        t SUBSET u
        ==> (subtopology top t) closure_of s SUBSET
            (subtopology top u) closure_of s
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY] THEN
  MATCH_MP_TAC(SET_RULE
    “s SUBSET s' /\ t SUBSET t' ==> s INTER t SUBSET s' INTER t'”) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_OF_MONO THEN
  ASM_SET_TAC[]
QED

Theorem CLOSURE_OF_UNION :
   !top s (t :'a set).
       top closure_of (s UNION t) = top closure_of s UNION top closure_of t
Proof
  REWRITE_TAC[CLOSURE_OF, DERIVED_SET_OF_UNION] THEN SET_TAC[]
QED

Theorem CLOSURE_OF_UNIONS :
   !top (f :('a set) set).
        FINITE f
        ==> top closure_of (UNIONS f) =  UNIONS {top closure_of s | s IN f}
Proof
  GEN_TAC THEN HO_MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC std_ss[UNIONS_0, NOT_IN_EMPTY, UNIONS_INSERT, CLOSURE_OF_EMPTY,
                  CLOSURE_OF_UNION, SIMPLE_IMAGE, IMAGE_CLAUSES]
QED

Theorem CLOSURE_OF_SUBSET :
   !top (s :'a set). s SUBSET topspace top ==> s SUBSET top closure_of s
Proof
  REWRITE_TAC[CLOSURE_OF] THEN SET_TAC[]
QED

Theorem CLOSURE_OF_SUBSET_INTER :
   !top (s :'a set). topspace top INTER s SUBSET top closure_of s
Proof
  REWRITE_TAC[CLOSURE_OF] THEN SET_TAC[]
QED

Theorem CLOSURE_OF_SUBSET_EQ :
   !top (s :'a set).
     s SUBSET topspace top /\ top closure_of s SUBSET s <=> closed_in top s
Proof
  REPEAT GEN_TAC THEN ASM_CASES_TAC “s :'a set SUBSET topspace top” THEN
  simp[closed_in, SUBSET_DEF, closure_of] THEN
  GEN_REWRITE_TAC RAND_CONV empty_rewrites[OPEN_IN_SUBOPEN] THEN
  MP_TAC(ISPEC “top :'a topology” OPEN_IN_SUBSET) THEN ASM_SET_TAC[]
QED

Theorem CLOSURE_OF_EQ :
   !top (s :'a set). top closure_of s = s <=> closed_in top s
Proof
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC “(s :'a set) SUBSET topspace top” THENL
   [ASM_MESON_TAC[SUBSET_ANTISYM_EQ, CLOSURE_OF_SUBSET, CLOSURE_OF_SUBSET_EQ],
    ASM_MESON_TAC[CLOSED_IN_SUBSET, CLOSURE_OF_SUBSET_TOPSPACE]]
QED

Theorem CLOSED_IN_CONTAINS_DERIVED_SET :
   !top (s :'a set).
        closed_in top s <=>
        top derived_set_of s SUBSET s /\ s SUBSET topspace top
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM CLOSURE_OF_SUBSET_EQ, CLOSURE_OF] THEN
  MP_TAC(ISPECL [“top :'a topology”, “s :'a set”]
    DERIVED_SET_OF_SUBSET_TOPSPACE) THEN
  SET_TAC[]
QED

Theorem DERIVED_SET_SUBSET_GEN :
   !top (s :'a set).
        top derived_set_of s SUBSET s <=>
        closed_in top (topspace top INTER s)
Proof
  REWRITE_TAC[CLOSED_IN_CONTAINS_DERIVED_SET, INTER_SUBSET] THEN
  REWRITE_TAC[GSYM DERIVED_SET_OF_RESTRICT, SUBSET_INTER] THEN
  REWRITE_TAC[DERIVED_SET_OF_SUBSET_TOPSPACE]
QED

Theorem DERIVED_SET_SUBSET :
   !top (s :'a set).
        s SUBSET topspace top
        ==> (top derived_set_of s SUBSET s <=> closed_in top s)
Proof
  SIMP_TAC std_ss[CLOSED_IN_CONTAINS_DERIVED_SET]
QED

Theorem CLOSED_IN_DERIVED_SET :
   !top s (t :'a set).
        closed_in (subtopology top t) s <=>
        s SUBSET topspace top /\ s SUBSET t /\
        !x. x IN top derived_set_of s /\ x IN t ==> x IN s
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSED_IN_CONTAINS_DERIVED_SET] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY, SUBSET_INTER] THEN
  REWRITE_TAC[DERIVED_SET_OF_SUBTOPOLOGY] THEN
  ASM_CASES_TAC “t INTER (s :'a set) = s” THEN ASM_REWRITE_TAC[] THEN
  ASM_SET_TAC[]
QED

Theorem CLOSED_IN_INTER_CLOSURE_OF :
   !top s (t :'a set).
        closed_in (subtopology top s) t <=> s INTER top closure_of t = t
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSURE_OF, CLOSED_IN_DERIVED_SET] THEN
  MP_TAC(ISPECL [“top :'a topology”, “t :'a set”]
        DERIVED_SET_OF_SUBSET_TOPSPACE) THEN
  SET_TAC[]
QED

Theorem CLOSURE_OF_CLOSED_IN :
   !top (s :'a set). closed_in top s ==> top closure_of s = s
Proof
  REWRITE_TAC[CLOSURE_OF_EQ]
QED

Theorem CLOSED_IN_CLOSURE_OF :
   !top (s :'a set). closed_in top (top closure_of s)
Proof
   REPEAT GEN_TAC THEN
  Q.SUBGOAL_THEN
   `top closure_of s =
    topspace top DIFF
    UNIONS {t | open_in top t /\ DISJOINT s t}`
  SUBST1_TAC THENL
  [ REWRITE_TAC[closure_of, UNIONS_GSPEC] THEN SET_TAC[],
    MATCH_MP_TAC CLOSED_IN_DIFF THEN REWRITE_TAC[CLOSED_IN_TOPSPACE] THEN
    SIMP_TAC std_ss[OPEN_IN_UNIONS, FORALL_IN_GSPEC] ]
QED

Theorem CLOSURE_OF_CLOSURE_OF :
   !top (s :'a set). top closure_of (top closure_of s) = top closure_of s
Proof
  REWRITE_TAC[CLOSURE_OF_EQ, CLOSED_IN_CLOSURE_OF]
QED

Theorem CLOSURE_OF_HULL :
   !top (s :'a set).
        s SUBSET topspace top ==> top closure_of s = (closed_in top) hull s
Proof
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC HULL_UNIQUE THEN
  ASM_SIMP_TAC std_ss[CLOSURE_OF_SUBSET, CLOSED_IN_CLOSURE_OF] THEN
  ASM_MESON_TAC[CLOSURE_OF_EQ, CLOSURE_OF_MONO]
QED

Theorem CLOSURE_OF_MINIMAL :
   !top s (t :'a set).
        s SUBSET t /\ closed_in top t ==> (top closure_of s) SUBSET t
Proof
  ASM_MESON_TAC[CLOSURE_OF_EQ, CLOSURE_OF_MONO]
QED

Theorem CLOSURE_OF_MINIMAL_EQ :
   !top s (t :'a set).
        s SUBSET topspace top /\ closed_in top t
        ==> ((top closure_of s) SUBSET t <=> s SUBSET t)
Proof
  MESON_TAC[SUBSET_TRANS, CLOSURE_OF_SUBSET, CLOSURE_OF_MINIMAL]
QED

Theorem CLOSURE_OF_UNIQUE :
   !top s t. s SUBSET t /\ closed_in top t /\
             (!t'. s SUBSET t' /\ closed_in top t' ==> t SUBSET t')
             ==> top closure_of s = t
Proof
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CLOSURE_OF_HULL o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[CLOSED_IN_SUBSET, SUBSET_TRANS],
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC HULL_UNIQUE THEN ASM_REWRITE_TAC[]
QED

Theorem FORALL_IN_CLOSURE_OF_GEN :
   !top P (s :'a set).
         (!x. x IN s ==> P x) /\
         closed_in top {x | x IN top closure_of s /\ P x}
         ==> (!x. x IN top closure_of s ==> P x)
Proof
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CLOSURE_OF_RESTRICT] THEN
  STRIP_TAC THEN
  REWRITE_TAC[SET_RULE
   “(!x. x IN s ==> P x) <=> s SUBSET {x | x IN s /\ P x}”] THEN
  MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [“top :'a topology”, “topspace top INTER (s :'a set)”]
        CLOSURE_OF_SUBSET) THEN
  ASM_SET_TAC[]
QED

Theorem FORALL_IN_CLOSURE_OF :
   !top P (s :'a set).
         (!x. x IN s ==> P x) /\
         closed_in top {x | x IN topspace top /\ P x}
         ==> (!x. x IN top closure_of s ==> P x)
Proof
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC FORALL_IN_CLOSURE_OF_GEN THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN “{x:'a | x IN top closure_of s /\ P x} =
                top closure_of s INTER {x | x IN topspace top /\ P x}”
   (fn th => ASM_SIMP_TAC std_ss[th, CLOSED_IN_INTER, CLOSED_IN_CLOSURE_OF]) THEN
  MP_TAC(ISPECL [“top :'a topology”, “s :'a set”] CLOSURE_OF_SUBSET_TOPSPACE) THEN
  SET_TAC[]
QED

Theorem FORALL_IN_CLOSURE_OF_UNIV :
   !top P (s :'a set).
        (!x. x IN s ==> P x) /\ closed_in top {x | P x}
        ==> !x. x IN top closure_of s ==> P x
Proof
  REWRITE_TAC[SET_RULE “(!x. x IN s ==> P x) <=> s SUBSET {x | P x}”] THEN
  SIMP_TAC std_ss[CLOSURE_OF_MINIMAL]
QED

Theorem CLOSURE_OF_EQ_EMPTY_GEN :
   !top (s :'a set).
        top closure_of s = {} <=> DISJOINT (topspace top) s
Proof
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CLOSURE_OF_RESTRICT, DISJOINT_DEF] THEN
  EQ_TAC THEN SIMP_TAC std_ss[CLOSURE_OF_EMPTY] THEN
  MATCH_MP_TAC(SET_RULE “t SUBSET s ==> s = {} ==> t = {}”) THEN
  MATCH_MP_TAC CLOSURE_OF_SUBSET THEN REWRITE_TAC[INTER_SUBSET]
QED

Theorem CLOSURE_OF_EQ_EMPTY :
   !top (s :'a set).
        s SUBSET topspace top ==> (top closure_of s = {} <=> s = {})
Proof
  REWRITE_TAC[CLOSURE_OF_EQ_EMPTY_GEN] THEN SET_TAC[]
QED

Theorem OPEN_IN_INTER_CLOSURE_OF_SUBSET :
   !top s (t :'a set).
        open_in top s
        ==> s INTER top closure_of t SUBSET top closure_of (s INTER t)
Proof
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC “t :'a set” o MATCH_MP
    OPEN_IN_INTER_DERIVED_SET_OF_SUBSET) THEN
  REWRITE_TAC[CLOSURE_OF] THEN SET_TAC[]
QED

Theorem CLOSURE_OF_OPEN_IN_INTER_CLOSURE_OF :
   !top s (t :'a set).
        open_in top s
        ==> top closure_of (s INTER top closure_of t) =
            top closure_of (s INTER t)
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN
    REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN
    ASM_SIMP_TAC std_ss[OPEN_IN_INTER_CLOSURE_OF_SUBSET],
    MATCH_MP_TAC CLOSURE_OF_MONO THEN
    MP_TAC(ISPECL [“top :'a topology”, “topspace top INTER (t :'a set)”]
        CLOSURE_OF_SUBSET) THEN
    REWRITE_TAC[INTER_SUBSET, GSYM CLOSURE_OF_RESTRICT] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    SET_TAC[]]
QED

Theorem OPEN_IN_INTER_CLOSURE_OF_EQ :
   !top s (t :'a set).
        open_in top s
        ==> s INTER top closure_of t = s INTER top closure_of (s INTER t)
Proof
  SIMP_TAC std_ss[GSYM SUBSET_ANTISYM_EQ, INTER_SUBSET, SUBSET_INTER] THEN
  SIMP_TAC std_ss[OPEN_IN_INTER_CLOSURE_OF_SUBSET] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE “s SUBSET t ==> u INTER s SUBSET t”) THEN
  MATCH_MP_TAC CLOSURE_OF_MONO THEN SET_TAC[]
QED

Theorem OPEN_IN_INTER_CLOSURE_OF_EQ_EMPTY :
   !top s (t :'a set).
        open_in top s ==> (s INTER top closure_of t = {} <=> s INTER t = {})
Proof
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SPEC “t :'a set” o
      MATCH_MP OPEN_IN_INTER_CLOSURE_OF_EQ) THEN
  EQ_TAC THEN SIMP_TAC std_ss[CLOSURE_OF_EMPTY, INTER_EMPTY] THEN
  MATCH_MP_TAC(SET_RULE
   “s INTER t SUBSET c ==> s INTER c = {} ==> s INTER t = {}”) THEN
  MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[]
QED

Theorem CLOSURE_OF_OPEN_IN_INTER_SUPERSET :
   !top s (t :'a set).
        open_in top s /\ s SUBSET top closure_of t
        ==> top closure_of (s INTER t) = top closure_of s
Proof
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o SPEC “t :'a set” o
    MATCH_MP CLOSURE_OF_OPEN_IN_INTER_CLOSURE_OF) THEN
  AP_TERM_TAC THEN ASM_SET_TAC[]
QED

Theorem CLOSURE_OF_OPEN_IN_SUBTOPOLOGY_INTER_CLOSURE_OF :
   !top s t (u :'a set).
        open_in (subtopology top u) s /\ t SUBSET u
        ==> top closure_of (s INTER top closure_of t) =
            top closure_of (s INTER t)
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I empty_rewrites[OPEN_IN_SUBTOPOLOGY]) THEN
    DISCH_THEN(X_CHOOSE_THEN “v :'a set”
     (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    FIRST_ASSUM(MP_TAC o SPEC “t :'a set” o
      MATCH_MP CLOSURE_OF_OPEN_IN_INTER_CLOSURE_OF) THEN
    ASM_SIMP_TAC std_ss[SET_RULE
     “t SUBSET u ==> (v INTER u) INTER t = v INTER t”] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC CLOSURE_OF_MONO THEN SET_TAC[],
    MATCH_MP_TAC CLOSURE_OF_MONO THEN
    MP_TAC(ISPECL [“top :'a topology”, “topspace top INTER (t :'a set)”]
        CLOSURE_OF_SUBSET) THEN
    REWRITE_TAC[GSYM CLOSURE_OF_RESTRICT, INTER_SUBSET] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[]]
QED

Theorem CLOSURE_OF_SUBTOPOLOGY_OPEN :
   !top u (s :'a set).
        open_in top u \/ s SUBSET u
        ==> (subtopology top u) closure_of s = u INTER top closure_of s
Proof
  REWRITE_TAC[SET_RULE “s SUBSET u <=> u INTER s = s”] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY] THEN
  ASM_MESON_TAC[OPEN_IN_INTER_CLOSURE_OF_EQ]
QED

(* ------------------------------------------------------------------------- *)
(* Interior with respect to a topological space.                             *)
(*  (ported from HOL-Light's Multivariate/metric.ml)                         *)
(* ------------------------------------------------------------------------- *)

(* parse_as_infix("interior_of",(21,"right"));; *)
val _ = set_fixity "interior_of" (Infixr 602);

Definition interior_of :
   top interior_of s = {x | ?t. open_in top t /\ x IN t /\ t SUBSET s}
End

Theorem INTERIOR_OF_RESTRICT :
   !top (s :'a set).
        top interior_of s = top interior_of (topspace top INTER s)
Proof
    rw [interior_of, Once EXTENSION, SUBSET_INTER]
 >> MESON_TAC[OPEN_IN_SUBSET]
QED

Theorem INTERIOR_OF_EQ :
   !top (s :'a set). (top interior_of s = s) <=> open_in top s
Proof
    rw [Once EXTENSION, interior_of]
 >> GEN_REWRITE_TAC RAND_CONV empty_rewrites[OPEN_IN_SUBOPEN]
 >> MESON_TAC[SUBSET_DEF]
QED

Theorem INTERIOR_OF_OPEN_IN :
   !top (s :'a set). open_in top s ==> top interior_of s = s
Proof
  MESON_TAC[INTERIOR_OF_EQ]
QED

Theorem INTERIOR_OF_EMPTY :
   !(top :'a topology). top interior_of {} = {}
Proof
  REWRITE_TAC[INTERIOR_OF_EQ, OPEN_IN_EMPTY]
QED

Theorem INTERIOR_OF_TOPSPACE :
   !(top :'a topology). top interior_of (topspace top) = topspace top
Proof
  REWRITE_TAC[INTERIOR_OF_EQ, OPEN_IN_TOPSPACE]
QED

Theorem OPEN_IN_INTERIOR_OF :
   !top (s :'a set). open_in top (top interior_of s)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[interior_of] THEN
  GEN_REWRITE_TAC I empty_rewrites[OPEN_IN_SUBOPEN]
 >> rw [SUBSET_DEF]
 >> Q.EXISTS_TAC ‘t’ >> art []
 >> Q.X_GEN_TAC ‘y’
 >> STRIP_TAC
 >> Q.EXISTS_TAC ‘t’ >> rw []
QED

Theorem INTERIOR_OF_INTERIOR_OF :
   !top (s :'a set). top interior_of top interior_of s = top interior_of s
Proof
  REWRITE_TAC[INTERIOR_OF_EQ, OPEN_IN_INTERIOR_OF]
QED

Theorem INTERIOR_OF_SUBSET :
   !top (s :'a set). top interior_of s SUBSET s
Proof
  REWRITE_TAC[interior_of] THEN SET_TAC[]
QED

Theorem INTERIOR_OF_SUBSET_CLOSURE_OF :
   !top (s :'a set). top interior_of s SUBSET top closure_of s
Proof
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[INTERIOR_OF_RESTRICT, CLOSURE_OF_RESTRICT] THEN
  Q_TAC (TRANS_TAC SUBSET_TRANS) `topspace top INTER s` THEN
  SIMP_TAC std_ss[INTERIOR_OF_SUBSET, CLOSURE_OF_SUBSET, INTER_SUBSET]
QED

Theorem SUBSET_INTERIOR_OF_EQ :
   !top (s :'a set). s SUBSET top interior_of s <=> open_in top s
Proof
  SIMP_TAC std_ss[GSYM INTERIOR_OF_EQ, GSYM SUBSET_ANTISYM_EQ, INTERIOR_OF_SUBSET]
QED

Theorem INTERIOR_OF_MONO :
   !top s (t :'a set).
        s SUBSET t ==> top interior_of s SUBSET top interior_of t
Proof
   REWRITE_TAC[interior_of] THEN SET_TAC[]
QED

Theorem INTERIOR_OF_MAXIMAL :
   !top s (t :'a set).
        t SUBSET s /\ open_in top t ==> t SUBSET top interior_of s
Proof
  REWRITE_TAC[interior_of] THEN SET_TAC[]
QED

Theorem INTERIOR_OF_MAXIMAL_EQ :
   !top s (t :'a set).
        open_in top t ==> (t SUBSET top interior_of s <=> t SUBSET s)
Proof
  MESON_TAC[INTERIOR_OF_MAXIMAL, SUBSET_TRANS, INTERIOR_OF_SUBSET]
QED

Theorem INTERIOR_OF_UNIQUE :
   !top s (t :'a set).
        t SUBSET s /\ open_in top t /\
        (!t'. t' SUBSET s /\ open_in top t' ==> t' SUBSET t)
        ==> top interior_of s = t
Proof
  MESON_TAC[SUBSET_ANTISYM, INTERIOR_OF_MAXIMAL, INTERIOR_OF_SUBSET,
            OPEN_IN_INTERIOR_OF]
QED

Theorem INTERIOR_OF_SUBSET_TOPSPACE :
   !top (s :'a set). top interior_of s SUBSET topspace top
Proof
    rw [SUBSET_DEF, interior_of]
 >> METIS_TAC[REWRITE_RULE[SUBSET_DEF] OPEN_IN_SUBSET]
QED

Theorem INTERIOR_OF_SUBSET_SUBTOPOLOGY :
   !top s (t :'a set). (subtopology top s) interior_of t SUBSET s
Proof
  REPEAT STRIP_TAC THEN MP_TAC
   (Q.ISPEC `subtopology top s` INTERIOR_OF_SUBSET_TOPSPACE) THEN
  SIMP_TAC std_ss[TOPSPACE_SUBTOPOLOGY, SUBSET_INTER]
QED

Theorem INTERIOR_OF_INTER :
   !top s (t :'a set).
      top interior_of (s INTER t) = top interior_of s INTER top interior_of t
Proof
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ, SUBSET_INTER] THEN
  SIMP_TAC std_ss[INTERIOR_OF_MONO, INTER_SUBSET] THEN
  SIMP_TAC std_ss[INTERIOR_OF_MAXIMAL_EQ, OPEN_IN_INTERIOR_OF, OPEN_IN_INTER] THEN
  MATCH_MP_TAC(SET_RULE
      “s SUBSET s' /\ t SUBSET t' ==> s INTER t SUBSET s' INTER t'”) THEN
  REWRITE_TAC[INTERIOR_OF_SUBSET]
QED

Theorem INTERIOR_OF_INTERS_SUBSET :
   !top f:('a->bool)->bool.
        top interior_of (INTERS f) SUBSET
        INTERS {top interior_of s | s IN f}
Proof
    REWRITE_TAC[SUBSET_DEF, interior_of, INTERS_GSPEC]
 >> rw [IN_INTERS]
 >> simp []
 >> Q.EXISTS_TAC ‘t’ >> rw []
QED

Theorem UNION_INTERIOR_OF_SUBSET :
   !top s (t :'a set).
        top interior_of s UNION top interior_of t
        SUBSET top interior_of (s UNION t)
Proof
  SIMP_TAC std_ss[UNION_SUBSET, INTERIOR_OF_MONO, SUBSET_UNION]
QED

Theorem INTERIOR_OF_EQ_EMPTY :
   !top (s :'a set).
                top interior_of s = {} <=>
                !t. open_in top t /\ t SUBSET s ==> t = {}
Proof
  MESON_TAC[INTERIOR_OF_MAXIMAL_EQ, SUBSET_EMPTY,
            OPEN_IN_INTERIOR_OF, INTERIOR_OF_SUBSET]
QED

Theorem INTERIOR_OF_EQ_EMPTY_ALT :
   !top (s :'a set).
        top interior_of s = {} <=>
        !t. open_in top t /\ ~(t = {}) ==> ~(t DIFF s = {})
Proof
  GEN_TAC THEN REWRITE_TAC[INTERIOR_OF_EQ_EMPTY] THEN SET_TAC[]
QED

Theorem INTERIOR_OF_UNIONS_OPEN_IN_SUBSETS :
   !top (s :'a set).
        UNIONS {t | open_in top t /\ t SUBSET s} = top interior_of s
Proof
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC INTERIOR_OF_UNIQUE THEN
  simp [OPEN_IN_UNIONS] >> SET_TAC []
QED

Theorem INTERIOR_OF_COMPLEMENT :
   !top (s :'a set).
        top interior_of (topspace top DIFF s) =
        topspace top DIFF top closure_of s
Proof
  REWRITE_TAC[interior_of, closure_of] THEN
  rw [Once EXTENSION, SUBSET_DEF] THEN
  MESON_TAC[REWRITE_RULE[SUBSET_DEF] OPEN_IN_SUBSET]
QED

Theorem INTERIOR_OF_CLOSURE_OF :
   !top (s :'a set).
        top interior_of s =
        topspace top DIFF top closure_of (topspace top DIFF s)
Proof
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM INTERIOR_OF_COMPLEMENT] THEN
  GEN_REWRITE_TAC LAND_CONV empty_rewrites[INTERIOR_OF_RESTRICT] THEN
  AP_TERM_TAC THEN SET_TAC[]
QED

Theorem CLOSURE_OF_INTERIOR_OF :
   !top (s :'a set).
        top closure_of s =
        topspace top DIFF top interior_of (topspace top DIFF s)
Proof
  REWRITE_TAC[INTERIOR_OF_COMPLEMENT] THEN
  REWRITE_TAC[SET_RULE “s = t DIFF (t DIFF s) <=> s SUBSET t”] THEN
  REWRITE_TAC[CLOSURE_OF_SUBSET_TOPSPACE]
QED

Theorem CLOSURE_OF_COMPLEMENT :
   !top (s :'a set).
        top closure_of (topspace top DIFF s) =
        topspace top DIFF top interior_of s
Proof
  REWRITE_TAC[interior_of, closure_of] THEN
  rw [Once EXTENSION, SUBSET_DEF] THEN
  MESON_TAC[REWRITE_RULE[SUBSET_DEF] OPEN_IN_SUBSET]
QED

Theorem INTERIOR_OF_EQ_EMPTY_COMPLEMENT :
   !top (s :'a set).
        top interior_of s = {} <=>
        top closure_of (topspace top DIFF s) = topspace top
Proof
  REPEAT GEN_TAC THEN MP_TAC(ISPECL
   [“top :'a topology”, “s :'a set”] INTERIOR_OF_SUBSET_TOPSPACE) THEN
  REWRITE_TAC[CLOSURE_OF_COMPLEMENT] THEN SET_TAC[]
QED

Theorem CLOSURE_OF_EQ_UNIV :
   !top (s :'a set).
     top closure_of s = topspace top <=>
     top interior_of (topspace top DIFF s) = {}
Proof
  REPEAT GEN_TAC THEN MP_TAC(ISPECL
   [“top :'a topology”, “s :'a set”] CLOSURE_OF_SUBSET_TOPSPACE) THEN
  REWRITE_TAC[INTERIOR_OF_COMPLEMENT] THEN SET_TAC[]
QED

Theorem INTERIOR_OF_SUBTOPOLOGY_SUBSET :
   !top s (u :'a set).
        u INTER top interior_of s SUBSET (subtopology top u) interior_of s
Proof
  simp[SUBSET_DEF, IN_INTER, interior_of, OPEN_IN_SUBTOPOLOGY] THEN
  REPEAT GEN_TAC THEN SIMP_TAC bool_ss[LEFT_AND_EXISTS_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  HO_MATCH_MP_TAC MONO_EXISTS THEN
  SIMP_TAC std_ss[TAUT `(p /\ q) /\ r <=> q /\ p /\ r`] THEN
  ASM_SET_TAC[]
QED

Theorem INTERIOR_OF_SUBTOPOLOGY_SUBSETS :
   !top s t (u :'a set).
        t SUBSET u
        ==> t INTER (subtopology top u) interior_of s SUBSET
            (subtopology top t) interior_of s
Proof
  REPEAT STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o MATCH_MP (SET_RULE
   “t SUBSET u ==> t = u INTER t”)) THEN
  REWRITE_TAC[GSYM SUBTOPOLOGY_SUBTOPOLOGY] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (SET_RULE “t SUBSET u ==> u INTER t = t”)) THEN
  REWRITE_TAC[INTERIOR_OF_SUBTOPOLOGY_SUBSET]
QED

Theorem INTERIOR_OF_SUBTOPOLOGY_MONO :
   !top s t (u :'a set).
        s SUBSET t /\ t SUBSET u
        ==> (subtopology top u) interior_of s SUBSET
            (subtopology top t) interior_of s
Proof
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC(SET_RULE
    “i SUBSET s /\ t INTER i SUBSET i'
     ==> s SUBSET t ==> i SUBSET i'”) THEN
  ASM_SIMP_TAC std_ss[INTERIOR_OF_SUBSET, INTERIOR_OF_SUBTOPOLOGY_SUBSETS]
QED

Theorem INTERIOR_OF_SUBTOPOLOGY_OPEN :
   !top u (s :'a set).
        open_in top u
        ==> (subtopology top u) interior_of s = u INTER top interior_of s
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[INTERIOR_OF_CLOSURE_OF] THEN
  ASM_SIMP_TAC std_ss[CLOSURE_OF_SUBTOPOLOGY_OPEN] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
  REWRITE_TAC[SET_RULE “s INTER t DIFF u = t INTER (s DIFF u)”] THEN
  ASM_SIMP_TAC std_ss[GSYM OPEN_IN_INTER_CLOSURE_OF_EQ] THEN SET_TAC[]
QED

Theorem DENSE_INTERSECTS_OPEN :
   !top (s :'a set).
        top closure_of s = topspace top <=>
        !t. open_in top t /\ ~(t = {}) ==> ~(s INTER t = {})
Proof
  REWRITE_TAC[CLOSURE_OF_INTERIOR_OF] THEN
  SIMP_TAC std_ss[INTERIOR_OF_SUBSET_TOPSPACE,
   SET_RULE “s SUBSET u ==> (u DIFF s = u <=> s = {})”] THEN
  REWRITE_TAC[INTERIOR_OF_EQ_EMPTY_ALT] THEN
  SIMP_TAC std_ss[OPEN_IN_SUBSET, SET_RULE
   “t SUBSET u ==> (~(t DIFF (u DIFF s) = {}) <=> ~(s INTER t = {}))”]
QED

Theorem INTERIOR_OF_CLOSED_IN_UNION_EMPTY_INTERIOR_OF :
   !top s (t :'a set).
        closed_in top s /\ top interior_of t = {}
        ==> top interior_of (s UNION t) = top interior_of s
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[INTERIOR_OF_CLOSURE_OF] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[SET_RULE “u DIFF (s UNION t) = (u DIFF s) INTER (u DIFF t)”] THEN
  W(MP_TAC o PART_MATCH (rand o rand) CLOSURE_OF_OPEN_IN_INTER_CLOSURE_OF o
    lhand o snd) THEN
  ASM_SIMP_TAC std_ss[CLOSURE_OF_COMPLEMENT, OPEN_IN_DIFF, OPEN_IN_TOPSPACE] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM CLOSURE_OF_COMPLEMENT] THEN
  AP_TERM_TAC THEN SET_TAC[]
QED

Theorem INTERIOR_OF_UNION_EQ_EMPTY :
   !top s (t :'a set).
        closed_in top s \/ closed_in top t
        ==> (top interior_of (s UNION t) = {} <=>
             top interior_of s = {} /\ top interior_of t = {})
Proof
  GEN_TAC THEN HO_MATCH_MP_TAC(MESON[]
   “(!x y. R x y ==> R y x) /\ (!x y. P x ==> R x y)
    ==> (!x y. P x \/ P y ==> R x y)”) THEN
  CONJ_TAC THENL [REWRITE_TAC[Once UNION_COMM] THEN SET_TAC[], ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT
   `(p ==> r) /\ (r ==> (p <=> q)) ==> (p <=> q /\ r)`) THEN
  ASM_SIMP_TAC std_ss[INTERIOR_OF_CLOSED_IN_UNION_EMPTY_INTERIOR_OF] THEN
  MATCH_MP_TAC(SET_RULE “s SUBSET t ==> t = {} ==> s = {}”) THEN
  SIMP_TAC std_ss[INTERIOR_OF_MONO, SUBSET_UNION]
QED

(* ------------------------------------------------------------------------- *)
(* Frontier (aka boundary) with respect to topological space.                *)
(*  (ported from HOL-Light's Multivariate/metric.ml)                         *)
(* ------------------------------------------------------------------------- *)

(* parse_as_infix("frontier_of",(21,"right"));; *)
val _ = set_fixity "frontier_of" (Infixr 602);

Definition frontier_of :
   top frontier_of s = top closure_of s DIFF top interior_of s
End

Theorem FRONTIER_OF_CLOSURES :
   !top s. top frontier_of s =
           top closure_of s INTER top closure_of (topspace top DIFF s)
Proof
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[frontier_of, CLOSURE_OF_COMPLEMENT] THEN
  MATCH_MP_TAC(SET_RULE “s SUBSET u ==> s INTER (u DIFF t) = s DIFF t”) THEN
  REWRITE_TAC[CLOSURE_OF_SUBSET_TOPSPACE]
QED

Theorem INTERIOR_OF_UNION_FRONTIER_OF :
   !top (s :'a set).
        top interior_of s UNION top frontier_of s = top closure_of s
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[frontier_of] THEN
  MP_TAC(Q.SPECL [`top`, `s`] INTERIOR_OF_SUBSET_CLOSURE_OF) THEN
  SET_TAC[]
QED

Theorem FRONTIER_OF_RESTRICT :
   !top (s :'a set). top frontier_of s = top frontier_of (topspace top INTER s)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[FRONTIER_OF_CLOSURES] THEN
  BINOP_TAC THEN GEN_REWRITE_TAC LAND_CONV empty_rewrites[CLOSURE_OF_RESTRICT] THEN
  AP_TERM_TAC THEN SET_TAC[]
QED

Theorem CLOSED_IN_FRONTIER_OF :
   !top (s :'a set). closed_in top (top frontier_of s)
Proof
  SIMP_TAC std_ss[FRONTIER_OF_CLOSURES, CLOSED_IN_INTER, CLOSED_IN_CLOSURE_OF]
QED

Theorem FRONTIER_OF_SUBSET_TOPSPACE :
   !top (s :'a set). top frontier_of s SUBSET topspace top
Proof
  SIMP_TAC std_ss[CLOSED_IN_SUBSET, CLOSED_IN_FRONTIER_OF]
QED

Theorem FRONTIER_OF_SUBSET_SUBTOPOLOGY :
   !top s (t :'a set). (subtopology top s) frontier_of t SUBSET s
Proof
  MESON_TAC[TOPSPACE_SUBTOPOLOGY, FRONTIER_OF_SUBSET_TOPSPACE, SUBSET_INTER]
QED

Theorem FRONTIER_OF_SUBTOPOLOGY_SUBSET :
   !top s (u :'a set).
        u INTER (subtopology top u) frontier_of s SUBSET (top frontier_of s)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[frontier_of] THEN MATCH_MP_TAC(SET_RULE
   “s SUBSET s' /\ u INTER t' SUBSET t
    ==> u INTER (s DIFF t) SUBSET s' DIFF t'”) THEN
  REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY_SUBSET, INTERIOR_OF_SUBTOPOLOGY_SUBSET]
QED

Theorem FRONTIER_OF_SUBTOPOLOGY_MONO :
   !top s t (u :'a set).
        s SUBSET t /\ t SUBSET u
        ==> (subtopology top t) frontier_of s SUBSET
            (subtopology top u) frontier_of s
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[frontier_of] THEN MATCH_MP_TAC(SET_RULE
   “s SUBSET s' /\ t' SUBSET t ==> s DIFF t SUBSET s' DIFF t'”) THEN
  ASM_SIMP_TAC std_ss[CLOSURE_OF_SUBTOPOLOGY_MONO, INTERIOR_OF_SUBTOPOLOGY_MONO]
QED

Theorem CLOPEN_IN_EQ_FRONTIER_OF :
   !top (s :'a set).
        closed_in top s /\ open_in top s <=>
        s SUBSET topspace top /\ top frontier_of s = {}
Proof
  REPEAT GEN_TAC THEN
  REWRITE_TAC[FRONTIER_OF_CLOSURES, OPEN_IN_CLOSED_IN_EQ] THEN
  ASM_CASES_TAC “(s :'a set) SUBSET topspace top” THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THENL [SIMP_TAC std_ss[CLOSURE_OF_CLOSED_IN] THEN SET_TAC[], DISCH_TAC] THEN
  ASM_SIMP_TAC std_ss[GSYM CLOSURE_OF_SUBSET_EQ, SUBSET_DIFF] THEN
  MATCH_MP_TAC(SET_RULE
   “c INTER c' = {} /\
    s SUBSET c /\ (u DIFF s) SUBSET c' /\ c SUBSET u /\ c' SUBSET u
        ==> c SUBSET s /\ c' SUBSET (u DIFF s)”) THEN
  ASM_SIMP_TAC std_ss[CLOSURE_OF_SUBSET, SUBSET_DIFF, CLOSURE_OF_SUBSET_TOPSPACE]
QED

Theorem FRONTIER_OF_EQ_EMPTY :
   !top (s :'a set).
        s SUBSET topspace top
        ==> (top frontier_of s = {} <=> closed_in top s /\ open_in top s)
Proof
  SIMP_TAC std_ss[CLOPEN_IN_EQ_FRONTIER_OF]
QED

Theorem FRONTIER_OF_OPEN_IN :
   !top (s :'a set).
        open_in top s ==> top frontier_of s = top closure_of s DIFF s
Proof
  SIMP_TAC std_ss[frontier_of, INTERIOR_OF_OPEN_IN]
QED

Theorem FRONTIER_OF_OPEN_IN_STRADDLE_INTER :
   !top s (u :'a set).
        open_in top u /\ ~(u INTER top frontier_of s = {})
        ==> ~(u INTER s = {}) /\ ~(u DIFF s = {})
Proof
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SIMP_TAC std_ss[FRONTIER_OF_CLOSURES, INTER_ASSOC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
   “~(s INTER t INTER u = {})
    ==> ~(s INTER t = {}) /\ ~(s INTER u = {})”)) THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) OPEN_IN_INTER_CLOSURE_OF_EQ_EMPTY o
     rand o lhand o snd) THEN
  ASM_SET_TAC[]
QED

Theorem FRONTIER_OF_SUBSET_CLOSED_IN :
   !top (s :'a set). closed_in top s ==> (top frontier_of s) SUBSET s
Proof
  REWRITE_TAC[GSYM CLOSURE_OF_SUBSET_EQ, frontier_of] THEN SET_TAC[]
QED

Theorem FRONTIER_OF_EMPTY :
   !top. top frontier_of {} = {}
Proof
  REWRITE_TAC[FRONTIER_OF_CLOSURES, CLOSURE_OF_EMPTY, INTER_EMPTY]
QED

Theorem FRONTIER_OF_TOPSPACE :
   !(top :'a topology). top frontier_of topspace top = {}
Proof
  SIMP_TAC std_ss[FRONTIER_OF_EQ_EMPTY, SUBSET_REFL] THEN
  REWRITE_TAC[OPEN_IN_TOPSPACE, CLOSED_IN_TOPSPACE]
QED

Theorem FRONTIER_OF_SUBSET_EQ :
   !top (s :'a set).
        s SUBSET topspace top
        ==> ((top frontier_of s) SUBSET s <=> closed_in top s)
Proof
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC std_ss[FRONTIER_OF_SUBSET_CLOSED_IN] THEN
  REWRITE_TAC[FRONTIER_OF_CLOSURES] THEN
  ASM_REWRITE_TAC[GSYM CLOSURE_OF_SUBSET_EQ] THEN
  ONCE_REWRITE_TAC[SET_RULE “s INTER t = s DIFF (s DIFF t)”] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP (SET_RULE
   “s DIFF t SUBSET u ==> t SUBSET u ==> s SUBSET u”)) THEN
  MATCH_MP_TAC(SET_RULE
   “!u. u DIFF s SUBSET d /\ c SUBSET u ==> c DIFF d SUBSET s”) THEN
  EXISTS_TAC “(topspace top) :'a set” THEN
  REWRITE_TAC[CLOSURE_OF_SUBSET_TOPSPACE] THEN
  MATCH_MP_TAC CLOSURE_OF_SUBSET THEN SET_TAC[]
QED

(* ------------------------------------------------------------------------- *)
(*  HOL-Light's “derived_set_of” and HOL4's “limpt”                          *)
(* ------------------------------------------------------------------------- *)

Theorem derived_set_of_alt_limpt :
    !top s. top derived_set_of s = {x | limpt top x s}
Proof
    rw [derived_set_of, limpt, Once EXTENSION]
 >> reverse EQ_TAC >> rw []
 >- (‘neigh top (t,x)’ by METIS_TAC [OPEN_OWN_NEIGH, IN_APP] \\
     Q.PAT_X_ASSUM ‘!N. neigh top (N,x) ==> _’ (MP_TAC o Q.SPEC ‘t’) >> rw [] \\
     Q.EXISTS_TAC ‘y’ >> rw [IN_APP])
 >> qabbrev_tac ‘u = top interior_of N’
 >> ‘open_in top u’ by PROVE_TAC [OPEN_IN_INTERIOR_OF]
 >> ‘u SUBSET N’ by PROVE_TAC [INTERIOR_OF_SUBSET]
 >> fs [neigh]
 >> ‘P SUBSET u’ by PROVE_TAC [INTERIOR_OF_MAXIMAL]
 >> ‘x IN u’ by METIS_TAC [SUBSET_DEF, IN_APP]
 >> Q.PAT_X_ASSUM ‘!t. x IN t /\ open_in top t ==> _’ (MP_TAC o Q.SPEC ‘u’)
 >> rw []
 >> ‘y IN N’ by METIS_TAC [SUBSET_DEF]
 >> Q.EXISTS_TAC ‘y’ >> fs [IN_APP]
QED

(* ------------------------------------------------------------------------- *)
(* Compact sets and compact topological spaces (from HOL-Light's metric.ml)  *)
(* ------------------------------------------------------------------------- *)

Definition compact_in :
   compact_in top s <=>
     s SUBSET topspace top /\
     (!U. (!u. u IN U ==> open_in top u) /\ s SUBSET UNIONS U
          ==> (?V. FINITE V /\ V SUBSET U /\ s SUBSET UNIONS V))
End

Definition compact_space :
   compact_space (top :'a topology) <=> compact_in top (topspace top)
End

Theorem COMPACT_SPACE_ALT :
   !(top :'a topology).
        compact_space top <=>
        !U. (!u. u IN U ==> open_in top u) /\
            topspace top SUBSET UNIONS U
            ==> ?V. FINITE V /\ V SUBSET U /\ topspace top SUBSET UNIONS V
Proof
  REWRITE_TAC[compact_space, compact_in, SUBSET_REFL]
QED

Theorem COMPACT_SPACE :
   !(top :'a topology).
        compact_space top <=>
        !U. (!u. u IN U ==> open_in top u) /\
            UNIONS U = topspace top
            ==> ?V. FINITE V /\ V SUBSET U /\ UNIONS V = topspace top
Proof
  GEN_TAC THEN REWRITE_TAC[COMPACT_SPACE_ALT] THEN
  SIMP_TAC std_ss[GSYM SUBSET_ANTISYM_EQ, UNIONS_SUBSET] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  MESON_TAC[SUBSET_DEF, OPEN_IN_SUBSET]
QED

Theorem COMPACT_IN_ABSOLUTE :
   !top (s :'a set).
        compact_in (subtopology top s) s <=> compact_in top s
Proof
  rw[compact_in] THEN
  simp[TOPSPACE_SUBTOPOLOGY, SUBSET_INTER, SUBSET_REFL] THEN
  simp[OPEN_IN_SUBTOPOLOGY, SET_RULE
   “(!x. x IN s ==> ?y. P y /\ x = f y) <=> s SUBSET IMAGE f {y | P y}”] THEN
  simp[IMP_CONJ, FORALL_SUBSET_IMAGE] THEN
  simp[EXISTS_FINITE_SUBSET_IMAGE] THEN
  simp[GSYM SIMPLE_IMAGE, GSYM INTER_UNIONS] THEN
  simp[SUBSET_INTER, SUBSET_REFL] THEN SET_TAC[]
QED

Theorem COMPACT_IN_SUBSPACE :
   !top (s :'a set).
        compact_in top s <=>
        s SUBSET topspace top /\ compact_space (subtopology top s)
Proof
  rw[compact_space, COMPACT_IN_ABSOLUTE, TOPSPACE_SUBTOPOLOGY] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q <=> ~(p ==> ~q)`] THEN
  qabbrev_tac ‘t = topspace top’ \\
  Know ‘(s SUBSET t ==> ~compact_in (subtopology top s) (t INTER s)) <=>
        (s SUBSET t ==> ~compact_in (subtopology top s) s)’
  >- METIS_TAC [SET_RULE “s SUBSET t ==> t INTER s = s”] >> Rewr' \\
  REWRITE_TAC[COMPACT_IN_ABSOLUTE] THEN
  REWRITE_TAC[TAUT `(p <=> ~(q ==> ~p)) <=> (p ==> q)`] THEN
  SIMP_TAC std_ss[Abbr ‘t’, compact_in]
QED

Theorem COMPACT_SPACE_SUBTOPOLOGY :
   !top (s :'a set). compact_in top s ==> compact_space (subtopology top s)
Proof
  SIMP_TAC std_ss[COMPACT_IN_SUBSPACE]
QED

Theorem COMPACT_IN_SUBTOPOLOGY :
   !top s (t :'a set).
        compact_in (subtopology top s) t <=> compact_in top t /\ t SUBSET s
Proof
  REPEAT GEN_TAC THEN
  REWRITE_TAC[COMPACT_IN_SUBSPACE, SUBTOPOLOGY_SUBTOPOLOGY] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY, SUBSET_INTER] THEN
  ASM_CASES_TAC “(t :'a set) SUBSET s” THEN ASM_REWRITE_TAC[] THEN
  METIS_TAC [SET_RULE “t SUBSET s ==> s INTER t = t”]
QED

Theorem COMPACT_IN_SUBSET_TOPSPACE :
   !top (s :'a set). compact_in top s ==> s SUBSET topspace top
Proof
  SIMP_TAC std_ss[compact_in]
QED

Theorem COMPACT_IN_CONTRACTIVE :
   !top (top' :'a topology).
        topspace top' = topspace top /\
        (!u. open_in top u ==> open_in top' u)
        ==> !s. compact_in top' s ==> compact_in top s
Proof
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  REWRITE_TAC[compact_in] THEN MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
   [ASM_SET_TAC[], HO_MATCH_MP_TAC MONO_FORALL THEN ASM_SET_TAC[]]
QED

Theorem COMPACT_SPACE_CONTRACTIVE :
   !top (top' :'a topology).
        topspace top' = topspace top /\
        (!u. open_in top u ==> open_in top' u)
        ==> compact_space top' ==> compact_space top
Proof
  SIMP_TAC std_ss[compact_space] THEN MESON_TAC[COMPACT_IN_CONTRACTIVE]
QED

Theorem FINITE_IMP_COMPACT_IN :
   !top (s :'a set). s SUBSET topspace top /\ FINITE s ==> compact_in top s
Proof
  SIMP_TAC std_ss[compact_in] \\
  rpt STRIP_TAC \\
  EXISTS_TAC “IMAGE (\(x :'a). @u. u IN U /\ x IN u) s” THEN
  CONJ_TAC >- (MATCH_MP_TAC FINITE_IMAGE >> art []) \\
  ASM_SET_TAC []
QED

Theorem COMPACT_IN_EMPTY :
   !(top :'a topology). compact_in top {}
Proof
  GEN_TAC THEN MATCH_MP_TAC FINITE_IMP_COMPACT_IN THEN
  REWRITE_TAC[FINITE_EMPTY, EMPTY_SUBSET]
QED

Theorem COMPACT_SPACE_TOPSPACE_EMPTY :
   !(top :'a topology). topspace top = {} ==> compact_space top
Proof
  MESON_TAC[SUBTOPOLOGY_TOPSPACE, COMPACT_IN_EMPTY, compact_space]
QED

Theorem FINITE_IMP_COMPACT_IN_EQ :
   !top (s :'a set).
        FINITE s ==> (compact_in top s <=> s SUBSET topspace top)
Proof
  MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE, FINITE_IMP_COMPACT_IN]
QED

Theorem COMPACT_IN_SING :
   !top (a :'a). compact_in top {a} <=> a IN topspace top
Proof
  SIMP_TAC std_ss[FINITE_IMP_COMPACT_IN_EQ, FINITE_SING, SING_SUBSET]
QED

Theorem CLOSED_COMPACT_IN :
   !top k (c :'a set). compact_in top k /\ c SUBSET k /\ closed_in top c
                   ==> compact_in top c
Proof
    rpt GEN_TAC
 >> REWRITE_TAC [compact_in] >> STRIP_TAC
 >> CONJ_TAC >- ASM_SET_TAC []
 >> rpt STRIP_TAC
 >> Q.PAT_X_ASSUM ‘!U. _ ==> ?V. FINITE V /\ _’
      (MP_TAC o Q.SPEC ‘(topspace top DIFF c) INSERT U’)
 >> ANTS_TAC
 >- (qabbrev_tac ‘t = topspace top’ \\
    ‘open_in top t’ by rw [OPEN_IN_TOPSPACE, Abbr ‘t’] \\
     reverse CONJ_TAC
     >- (rw [SUBSET_DEF] \\
         Cases_on ‘x IN c’
         >- (Q.PAT_X_ASSUM ‘c SUBSET BIGUNION U’ MP_TAC \\
             rw [SUBSET_DEF] \\
             POP_ASSUM (MP_TAC o Q.SPEC ‘x’) >> rw [] \\
             Q.EXISTS_TAC ‘s’ >> rw []) \\
         Q.EXISTS_TAC ‘t DIFF c’ >> simp [] \\
         ASM_SET_TAC []) \\
     rw [] >- (MATCH_MP_TAC OPEN_IN_DIFF >> art []) \\
     Q.PAT_X_ASSUM ‘c SUBSET BIGUNION U’ MP_TAC \\
     rw [SUBSET_DEF])
 >> STRIP_TAC
 >> Q.EXISTS_TAC ‘V DELETE (topspace top DIFF c)’
 >> ASM_REWRITE_TAC[FINITE_DELETE]
 >> CONJ_TAC >- ASM_SET_TAC []
 >> REWRITE_TAC[SUBSET_DEF, IN_UNIONS, IN_DELETE]
 >> ASM_SET_TAC []
QED

Theorem CLOSED_IN_COMPACT_SPACE :
   !top (s :'a set).
        compact_space top /\ closed_in top s ==> compact_in top s
Proof
  REWRITE_TAC[compact_space] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CLOSED_COMPACT_IN THEN EXISTS_TAC “topspace (top :'a topology)” THEN
  ASM_MESON_TAC[CLOSED_IN_SUBSET]
QED

(* References:

  [1] J. L. Kelley, General Topology. Springer Science & Business Media, 1975.

 *)
