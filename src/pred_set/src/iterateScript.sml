(* ========================================================================= *)
(*    Generic iterated operations and special cases of sums over N           *)
(*                                                                           *)
(*        (c) Copyright 2014-2015,                                           *)
(*                       Muhammad Qasim,                                     *)
(*                       Osman Hasan,                                        *)
(*                       Hardware Verification Group,                        *)
(*                       Concordia University                                *)
(*                                                                           *)
(*            Contact:  <m_qasi@ece.concordia.ca>                            *)
(*                                                                           *)
(*    Note: This theory was ported from HOL Light's iterate.ml               *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*              (c) Copyright, Lars Schewe 2007                              *)
(* ========================================================================= *)
Theory iterate[bare]
Ancestors
  prim_rec combin quotient arithmetic pair pred_set option
  relation permutes
Libs
  HolKernel Parse boolLib BasicProvers numLib tautLib Arith
  metisLib mesonLib pred_setLib simpLib pureSimps numSimps
  hurdUtils TotalDefn computeLib TypeBase boolSimps unwindLib


val qexists_tac = Q.EXISTS_TAC;
val qabbrev_tac = Q.ABBREV_TAC;
val qid_spec_tac = Q.ID_SPEC_TAC;
val rename = Q.RENAME_TAC;
val rename1 = Q.RENAME1_TAC;
val rw = SRW_TAC [];
fun simp ths = ASM_SIMP_TAC (srw_ss()) ths;
fun fs ths = FULL_SIMP_TAC (srw_ss()) ths;
fun rfs ths = REV_FULL_SIMP_TAC (srw_ss()) ths;

val metis_tac = METIS_TAC;

val _ = augment_srw_ss [ARITH_ss];

val GEN_REWR_TAC = Lib.C Rewrite.GEN_REWRITE_TAC Rewrite.empty_rewrites;

(* ------------------------------------------------------------------------- *)
(* MESON, METIS, SET_TAC, SET_RULE, ASSERT_TAC, ASM_ARITH_TAC                *)
(* ------------------------------------------------------------------------- *)

fun METIS ths tm = prove(tm,METIS_TAC ths);

val DISC_RW_KILL = DISCH_TAC >> ONCE_ASM_REWRITE_TAC [] \\
                   POP_ASSUM K_TAC;

fun ASSERT_TAC tm = SUBGOAL_THEN tm STRIP_ASSUME_TAC;

val ASM_ARITH_TAC = rpt (POP_ASSUM MP_TAC) >> ARITH_TAC;

Theorem CONJ_EQ_IMP[local] :
    !p q r. p /\ q ==> r <=> p ==> q ==> r
Proof
    REWRITE_TAC [AND_IMP_INTRO]
QED

(* Minimal hol-light compatibility layer *)
val FINITE_SUBSET = SUBSET_FINITE_I; (* pred_setTheory *)

Theorem LEFT_IMP_EXISTS_THM[local] :
    !P Q. (?x. P x) ==> Q <=> (!x. P x ==> Q)
Proof
    SIMP_TAC std_ss [PULL_EXISTS]
QED

Theorem FORALL_IN_GSPEC[local] :
   (!P f. (!z. z IN {f x | P x} ==> Q z) <=> (!x. P x ==> Q(f x))) /\
   (!P f. (!z. z IN {f x y | P x y} ==> Q z) <=>
          (!x y. P x y ==> Q(f x y))) /\
   (!P f. (!z. z IN {f w x y | P w x y} ==> Q z) <=>
          (!w x y. P w x y ==> Q(f w x y)))
Proof
   SRW_TAC [][] THEN SET_TAC []
QED

Theorem CONJ_ACI[local] :
   !p q. (p /\ q <=> q /\ p) /\
   ((p /\ q) /\ r <=> p /\ (q /\ r)) /\
   (p /\ (q /\ r) <=> q /\ (p /\ r)) /\
   (p /\ p <=> p) /\
   (p /\ (p /\ q) <=> p /\ q)
Proof
  METIS_TAC [CONJ_ASSOC, CONJ_SYM]
QED

(* ------------------------------------------------------------------------- *)
(* misc.                                                                     *)
(* ------------------------------------------------------------------------- *)

Theorem FINITE_SUBSET_IMAGE:
   !f:'a->'b s t.
        FINITE(t) /\ t SUBSET (IMAGE f s) <=>
        ?s'. FINITE s' /\ s' SUBSET s /\ (t = IMAGE f s')
Proof
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC, ASM_MESON_TAC[IMAGE_FINITE, IMAGE_SUBSET]] THEN
  STRIP_TAC THEN
  EXISTS_TAC ``IMAGE (\y. @x. x IN s /\ ((f:'a->'b)(x) = y)) t`` THEN
  ASM_SIMP_TAC std_ss [IMAGE_FINITE] THEN
  SIMP_TAC std_ss [EXTENSION, SUBSET_DEF, FORALL_IN_IMAGE] THEN CONJ_TAC THENL
   [METIS_TAC[SUBSET_DEF, IN_IMAGE], ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN X_GEN_TAC ``y:'b`` THEN
  SIMP_TAC std_ss [GSYM RIGHT_EXISTS_AND_THM] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[UNWIND_THM2, GSYM CONJ_ASSOC] THEN
  METIS_TAC [SUBSET_DEF, IN_IMAGE]
QED

Theorem EXISTS_FINITE_SUBSET_IMAGE:
   !P f s.
    (?t. FINITE t /\ t SUBSET IMAGE f s /\ P t) <=>
    (?t. FINITE t /\ t SUBSET s /\ P (IMAGE f t))
Proof
  REWRITE_TAC[FINITE_SUBSET_IMAGE, CONJ_ASSOC] THEN MESON_TAC[]
QED

Theorem FORALL_FINITE_SUBSET_IMAGE:
   !P f s. (!t. FINITE t /\ t SUBSET IMAGE f s ==> P t) <=>
           (!t. FINITE t /\ t SUBSET s ==> P(IMAGE f t))
Proof
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [METIS [] ``(FINITE t /\ t SUBSET IMAGE f s ==> P t) =
                            (\t. FINITE t /\ t SUBSET IMAGE f s ==> P t) t``] THEN
   ONCE_REWRITE_TAC [METIS [] ``(FINITE t /\ t SUBSET s ==> P (IMAGE f t)) =
                            (\t. FINITE t /\ t SUBSET s ==> P (IMAGE f t)) t``] THEN
   ONCE_REWRITE_TAC [MESON[] ``(!x. P x) <=> ~(?x. ~P x)``] THEN
   SIMP_TAC std_ss [NOT_IMP, GSYM CONJ_ASSOC, EXISTS_FINITE_SUBSET_IMAGE]
QED

Theorem EMPTY_BIGUNION:
   !s. (BIGUNION s = {}) <=> !t. t IN s ==> (t = {})
Proof
  SET_TAC[]
QED

Theorem UPPER_BOUND_FINITE_SET:
  !f:('a->num) s. FINITE(s) ==> ?a. !x. x IN s ==> f(x) <= a
Proof
  rpt strip_tac >> qexists_tac ‘MAX_SET (IMAGE f s)’ >>
  rpt strip_tac >> irule X_LE_MAX_SET >> simp[]
QED

Theorem BOUNDS_LINEAR:
   !A B C. (!n:num. A * n <= B * n + C) <=> A <= B
Proof
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[NOT_LESS_EQUAL] THEN
    DISCH_THEN(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LT_EXISTS]) THEN
    REWRITE_TAC[RIGHT_ADD_DISTRIB, LE_ADD_LCANCEL] THEN
    DISCH_THEN(MP_TAC o SPEC ``SUC C``) THEN
    REWRITE_TAC[NOT_LESS_EQUAL, MULT_CLAUSES, ADD_CLAUSES, LT_SUC_LE] THEN
    ARITH_TAC,
    DISCH_THEN(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
    ARITH_TAC]
QED

Theorem BOUNDS_LINEAR_0:
   !A B. (!n:num. A * n <= B) <=> (A = 0)
Proof
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [``A:num``, ``0:num``, ``B:num``] BOUNDS_LINEAR) THEN
  REWRITE_TAC[MULT_CLAUSES, ADD_CLAUSES, LE]
QED

Theorem FINITE_POWERSET:
    !s. FINITE s ==> FINITE {t | t SUBSET s}
Proof
    METIS_TAC [FINITE_POW, POW_DEF]
QED

Theorem LE_ADD:
   !m n:num. m <= m + n
Proof
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC arith_ss [LE, ADD_CLAUSES, LESS_EQ_REFL]
QED

Theorem LE_ADDR:
   !m n:num. n <= m + n
Proof
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_ACCEPT_TAC LE_ADD
QED

Theorem ADD_SUB2:
   !m n:num. (m + n) - m = n
Proof
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_ACCEPT_TAC ADD_SUB
QED

Theorem ADD_SUBR2:
   !m n:num. m - (m + n) = 0
Proof
  REWRITE_TAC[SUB_EQ_0, LESS_EQ_ADD]
QED

Theorem ADD_SUBR:
   !m n:num. n - (m + n) = 0
Proof
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_ACCEPT_TAC ADD_SUBR2
QED

Theorem TRANSITIVE_STEPWISE_LE_EQ:
   !R. (!x. R x x) /\ (!x y z. R x y /\ R y z ==> R x z)
       ==> ((!m n. m <= n ==> R m n) <=> (!n. R n (SUC n)))
Proof
  REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC std_ss [LE, LESS_EQ_REFL] THEN
  DISCH_TAC THEN SIMP_TAC std_ss [LE_EXISTS, LEFT_IMP_EXISTS_THM] THEN
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN ASM_MESON_TAC[]
QED

Theorem TRANSITIVE_STEPWISE_LE:
   !R. (!x. R x x) /\ (!x y z. R x y /\ R y z ==> R x z) /\
       (!n. R n (SUC n))
       ==> !m n. m <= n ==> R m n
Proof
  REPEAT GEN_TAC THEN MATCH_MP_TAC(TAUT
   `(a /\ a' ==> (c <=> b)) ==> a /\ a' /\ b ==> c`) THEN
  MATCH_ACCEPT_TAC TRANSITIVE_STEPWISE_LE_EQ
QED

Theorem TRANSITIVE_STEPWISE_LT_EQ :
   !R. (!x y z. R x y /\ R y z ==> R x z)
         ==> ((!m n. m < n ==> R m n) <=> (!n. R n (SUC n)))
Proof
  REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC std_ss [LESS_THM] THEN
  DISCH_TAC THEN SIMP_TAC std_ss [LT_EXISTS] THEN
  KNOW_TAC ``(!m n. (?d. n = m + SUC d) ==> R m n) =
              (!m d n. (n = m + SUC d) ==> R m (m + SUC d))`` THENL
  [METIS_TAC [LEFT_EXISTS_IMP_THM, SWAP_FORALL_THM], ALL_TAC] THEN
  DISC_RW_KILL THEN GEN_TAC THEN
  SIMP_TAC std_ss [LEFT_FORALL_IMP_THM, EXISTS_REFL, ADD_CLAUSES] THEN
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN ASM_MESON_TAC[]
QED

Theorem TRANSITIVE_STEPWISE_LT :
   !R. (!x y z. R x y /\ R y z ==> R x z) /\ (!n. R n (SUC n))
       ==> !m n. m < n ==> R m n
Proof
  REPEAT GEN_TAC THEN MATCH_MP_TAC(TAUT
   `(a ==> (c <=> b)) ==> a /\ b ==> c`) THEN
  MATCH_ACCEPT_TAC TRANSITIVE_STEPWISE_LT_EQ
QED

Theorem LAMBDA_PAIR:
   (\(x,y). P x y) = (\p. P (FST p) (SND p))
Proof
  SIMP_TAC std_ss [FUN_EQ_THM, FORALL_PROD] THEN
  SIMP_TAC std_ss []
QED

Theorem NOT_EQ:
   !a b. (a <> b) = ~(a = b)
Proof METIS_TAC []
QED

Theorem POWERSET_CLAUSES:
   ({s | s SUBSET {}} = {{}}) /\
   ((!a:'a t. {s | s SUBSET (a INSERT t)} =
            {s | s SUBSET t} UNION IMAGE (\s. a INSERT s) {s | s SUBSET t}))
Proof
  REWRITE_TAC[SUBSET_INSERT_DELETE, SUBSET_EMPTY, SET_RULE
   ``(!a. {x | x = a} = {a}) /\ (!a. {x | a = x} = {a})``] THEN
  MAP_EVERY X_GEN_TAC [``a:'a``, ``t:'a->bool``] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[UNION_SUBSET] THEN
  ONCE_REWRITE_TAC[SUBSET_DEF] THEN
  SIMP_TAC std_ss [FORALL_IN_IMAGE, FORALL_IN_GSPEC] THEN
  SIMP_TAC std_ss [GSPECIFICATION, IN_UNION, IN_IMAGE] THEN
  CONJ_TAC THENL [ALL_TAC, SET_TAC[]] THEN
  X_GEN_TAC ``s:'a->bool`` THEN
  ASM_CASES_TAC ``(a:'a) IN s`` THENL [ALL_TAC, ASM_SET_TAC[]] THEN
  STRIP_TAC THEN DISJ2_TAC THEN EXISTS_TAC ``s DELETE (a:'a)`` THEN
  ASM_SET_TAC[]
QED

Theorem SIMPLE_IMAGE_GEN:
   !f P. {f x | P x} = IMAGE f {x | P x}
Proof
  SET_TAC[]
QED

Theorem FUN_IN_IMAGE:
   !f s x. x IN s ==> f(x) IN IMAGE f s
Proof
  SET_TAC[]
QED

Theorem DIFF_BIGINTER2 : (* was: DIFF_BIGINTER *)
    !u s. u DIFF BIGINTER s = BIGUNION {u DIFF t | t IN s}
Proof
  SIMP_TAC std_ss [BIGUNION_GSPEC] THEN SET_TAC[]
QED

Theorem BIGINTER_BIGUNION:
   !s. BIGINTER s = UNIV DIFF (BIGUNION {UNIV DIFF t | t IN s})
Proof
  REWRITE_TAC[GSYM DIFF_BIGINTER2] THEN SET_TAC[]
QED

Theorem BIGUNION_BIGINTER:
   !s. BIGUNION s = UNIV DIFF (BIGINTER {UNIV DIFF t | t IN s})
Proof
  GEN_TAC THEN GEN_REWR_TAC I [EXTENSION] THEN
  SIMP_TAC std_ss [IN_BIGUNION, IN_UNIV, IN_DIFF, BIGINTER_GSPEC,
   GSPECIFICATION] THEN
  MESON_TAC[]
QED

(* ------------------------------------------------------------------------- *)
(* Recursion over finite sets; based on Ching-Tsun's code (archive 713).     *)
(* ------------------------------------------------------------------------- *)

Definition FINREC:
   (FINREC (f:'a->'b->'b) b s a 0 <=> (s = {}) /\ (a = b)) /\
   (FINREC (f:'a->'b->'b) b s a (SUC n) <=>
                ?x c. x IN s /\
                      FINREC f b (s DELETE x) c n /\
                      (a = f x c))
End

Theorem FINREC_1_LEMMA:
    !f b s a. FINREC f b s a (SUC 0) <=> ?x. (s = {x}) /\ (a = f x b)
Proof
  REWRITE_TAC[FINREC] THEN REPEAT GEN_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  SIMP_TAC std_ss [GSPECIFICATION] THEN EQ_TAC THENL [METIS_TAC [DELETE_EQ_SING],
  STRIP_TAC THEN ASM_REWRITE_TAC [IN_SING, SING_DELETE]]
QED

Theorem FINREC_SUC_LEMMA:
    !(f:'a->'b->'b) b.
           (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
           ==> !n s z.
                  FINREC f b s z (SUC n)
                  ==> !x. x IN s ==> ?w. FINREC f b (s DELETE x) w n /\
                                         (z = f x w)
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
  [REWRITE_TAC[FINREC_1_LEMMA] THEN REWRITE_TAC[FINREC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IN_INSERT, NOT_IN_EMPTY] THEN
  DISCH_THEN SUBST1_TAC THEN EXISTS_TAC ``b:'b`` THEN
  ASM_REWRITE_TAC[SING_DELETE], REPEAT GEN_TAC THEN
  GEN_REWR_TAC LAND_CONV [FINREC] THEN
  DISCH_THEN(X_CHOOSE_THEN ``y:'a`` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN ``c:'b`` STRIP_ASSUME_TAC) THEN
  X_GEN_TAC ``x:'a`` THEN DISCH_TAC THEN
  ASM_CASES_TAC ``x:'a = y`` THEN ASM_REWRITE_TAC[] THENL
  [EXISTS_TAC ``c:'b`` THEN ASM_REWRITE_TAC[],
  UNDISCH_TAC ``FINREC (f:'a->'b->'b) b (s DELETE y) c (SUC n)`` THEN
  DISCH_THEN(ANTE_RES_THEN (MP_TAC o SPEC ``x:'a``)) THEN
  ONCE_ASM_REWRITE_TAC[IN_DELETE] THEN ONCE_ASM_REWRITE_TAC[IN_DELETE] THEN
  ONCE_ASM_REWRITE_TAC[IN_DELETE] THEN ONCE_ASM_REWRITE_TAC[IN_DELETE] THEN
  ONCE_ASM_REWRITE_TAC[IN_DELETE] THEN
  DISCH_THEN(X_CHOOSE_THEN ``v:'b`` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC ``(f:'a->'b->'b) y v`` THEN ONCE_ASM_REWRITE_TAC[FINREC] THEN
  CONJ_TAC THENL [MAP_EVERY EXISTS_TAC [``y:'a``, ``v:'b``] THEN
  ONCE_REWRITE_TAC[DELETE_COMM] THEN ONCE_ASM_REWRITE_TAC[IN_DELETE] THEN
  ONCE_ASM_REWRITE_TAC[IN_DELETE] THEN ONCE_ASM_REWRITE_TAC[IN_DELETE] THEN
  METIS_TAC [], METIS_TAC []]]]
QED

Theorem FINREC_UNIQUE_LEMMA:
    !(f:'a->'b->'b) b.
          (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
          ==> !n1 n2 s a1 a2.
                 FINREC f b s a1 n1 /\ FINREC f b s a2 n2
                 ==> (a1 = a2) /\ (n1 = n2)
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN INDUCT_TAC THENL
  [REWRITE_TAC[FINREC] THEN MESON_TAC[NOT_IN_EMPTY],
  REWRITE_TAC[FINREC] THEN MESON_TAC[NOT_IN_EMPTY],
  REWRITE_TAC[FINREC] THEN MESON_TAC[NOT_IN_EMPTY],
  IMP_RES_THEN ASSUME_TAC FINREC_SUC_LEMMA THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fn th => MP_TAC(CONJUNCT1 th) THEN MP_TAC th) THEN
  DISCH_THEN(CONJUNCTS_THEN (ANTE_RES_THEN ASSUME_TAC)) THEN
  REWRITE_TAC[FINREC] THEN STRIP_TAC THEN ASM_MESON_TAC[]]
QED

Theorem FINREC_EXISTS_LEMMA:
    !(f:'a->'b->'b) b s. FINITE s ==> ?a n. FINREC f b s a n
Proof
  REPEAT GEN_TAC THEN
  KNOW_TAC ``(?a:'b n. FINREC f b s a n) = (\s. ?a:'b n. FINREC f b s a n) s`` THENL
  [FULL_SIMP_TAC std_ss [], DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN REPEAT STRIP_TAC THENL
  [MAP_EVERY EXISTS_TAC [``b:'b``, ``0:num``] THEN REWRITE_TAC[FINREC],
  MAP_EVERY EXISTS_TAC [``(f:'a->'b->'b) e a``, ``SUC n``] THEN
  REWRITE_TAC[FINREC] THEN MAP_EVERY EXISTS_TAC [``e:'a``, ``a:'b``] THEN
  FULL_SIMP_TAC std_ss [IN_INSERT] THEN
  EVAL_TAC THEN FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT]]]
QED

Theorem FINREC_FUN_LEMMA:
    !P (R:'a->'b->'c->bool).
      (!s. P s ==> ?a n. R s a n) /\
      (!n1 n2 s a1 a2.
         R s a1 n1 /\ R s a2 n2 ==> (a1 = a2) /\ (n1 = n2)) ==>
      ?f. !s a. P s ==> ((?n. R s a n) <=> (f s = a))
Proof
  REPEAT STRIP_TAC THEN EXISTS_TAC ``\s:'a. @a:'b. ?n:'c. R s a n`` THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN EQ_TAC THENL [STRIP_TAC THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC[],
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SELECT_CONV THEN ASM_MESON_TAC[]]
QED

Theorem FINREC_FUN :
    !(f:'a->'b->'b) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> ?g. (g {} = b) /\
                !s x. FINITE s /\ x IN s
                      ==> (g s = f x (g (s DELETE x)))
Proof
  REPEAT STRIP_TAC THEN IMP_RES_THEN MP_TAC FINREC_UNIQUE_LEMMA THEN
  REPEAT STRIP_TAC THEN
  KNOW_TAC ``!n1 n2 s a1 a2. FINREC f b s a1 n1 /\
                             FINREC f b s a2 n2 ==> (a1 = a2) /\ (n1 = n2)``
  THEN1 METIS_TAC [] THEN
  DISCH_THEN (MP_TAC o CONJ (SPECL [``f:'a->'b->'b``, ``b:'b``] FINREC_EXISTS_LEMMA)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP FINREC_FUN_LEMMA) THEN
  DISCH_THEN(X_CHOOSE_TAC ``g:('a->bool)->'b``) THEN
  EXISTS_TAC ``g:('a->bool)->'b`` THEN CONJ_TAC THENL
  [ SUBGOAL_THEN ``FINITE(EMPTY:'a->bool)``
    (ANTE_RES_THEN (fn th => GEN_REWR_TAC I [GSYM th])) THENL
     [REWRITE_TAC[FINITE_EMPTY],
      EXISTS_TAC ``0:num`` THEN REWRITE_TAC[FINREC]],
    REPEAT STRIP_TAC THEN
    ANTE_RES_THEN MP_TAC (ASSUME ``FINITE(s:'a->bool)``) THEN
    DISCH_THEN(ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC ``(g:('a->bool)->'b) s``) THEN
    REWRITE_TAC[] THEN REWRITE_TAC[GSYM LEFT_FORALL_IMP_THM] THEN
    INDUCT_TAC THENL
    [ ASM_REWRITE_TAC[FINREC] THEN DISCH_TAC THEN UNDISCH_TAC ``x:'a IN s`` THEN
      ASM_REWRITE_TAC[NOT_IN_EMPTY],
      IMP_RES_THEN ASSUME_TAC FINREC_SUC_LEMMA THEN
      DISCH_THEN(ANTE_RES_THEN (MP_TAC o SPEC ``x:'a``)) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN ``w:'b`` (CONJUNCTS_THEN ASSUME_TAC)) THEN
      SUBGOAL_THEN ``(g (s DELETE x:'a) = w:'b)`` SUBST1_TAC THENL
      [ SUBGOAL_THEN ``FINITE(s DELETE x:'a)`` MP_TAC THENL
        [ FULL_SIMP_TAC std_ss [FINITE_DELETE],
          DISCH_THEN(ANTE_RES_THEN (MP_TAC o GSYM)) THEN
          DISCH_THEN(fn th => REWRITE_TAC[th]) THEN
          METIS_TAC [] ],
        ASM_REWRITE_TAC [] ] ] ]
QED

Theorem SET_RECURSION_LEMMA:
   !(f:'a->'b->'b) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> ?g. (g {} = b) /\
                !x s. FINITE s
                      ==> (g (x INSERT s) =
                                if x IN s then g s else f x (g s))
Proof
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC ``b:'b`` o MATCH_MP FINREC_FUN) THEN
  DISCH_THEN(X_CHOOSE_THEN ``g:('a->bool)->'b`` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC ``g:('a->bool)->'b`` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[GSYM ABSORPTION] THEN ASM_REWRITE_TAC[],
    SUBGOAL_THEN ``FINITE(x:'a INSERT s) /\ x IN (x INSERT s)`` MP_TAC THENL
     [REWRITE_TAC[IN_INSERT] THEN ASM_MESON_TAC[FINITE_INSERT],
      DISCH_THEN(ANTE_RES_THEN SUBST1_TAC) THEN
      REPEAT AP_TERM_TAC THEN UNDISCH_TAC ``~(x:'a IN s)`` THEN DISCH_TAC THEN
      EVAL_TAC THEN FULL_SIMP_TAC std_ss [DELETE_NON_ELEMENT, SUBSET_REFL]]]
QED

(* This is HOL Light's definition of ‘ITSET’ *)
Theorem ITSET_alt :
    !(f:'a->'b->'b) s b.
        (!x y z. f x (f y z) = f y (f x z)) /\ FINITE s ==>
         ITSET f s b =
         (@g. (g {} = b) /\
              !x s. FINITE s ==>
                    (g (x INSERT s) = if x IN s then g s else f x (g s))) s
Proof
    RW_TAC std_ss []
 >> SELECT_ELIM_TAC
 >> CONJ_TAC
 >- (MATCH_MP_TAC SET_RECURSION_LEMMA >> rw [])
 >> rpt STRIP_TAC
 >> Q.PAT_X_ASSUM ‘FINITE s’ MP_TAC
 >> Q.SPEC_TAC (‘s’, ‘s’)
 >> HO_MATCH_MP_TAC FINITE_INDUCT
 >> CONJ_TAC >- rw [ITSET_THM, FINITE_EMPTY]
 >> rpt STRIP_TAC
 >> Q.PAT_X_ASSUM ‘!x s. FINITE s ==> P’
      (fn th => ONCE_REWRITE_TAC [MATCH_MP th (ASSUME “FINITE s”)])
 >> simp []
 >> Know ‘ITSET f (e INSERT s) b = f e (ITSET f (s DELETE e) b)’
 >- (MATCH_MP_TAC COMMUTING_ITSET_RECURSES >> rw [])
 >> Rewr'
 >> Suff ‘s DELETE e = s’ >- rw []
 >> rw [GSYM DELETE_NON_ELEMENT]
QED

Theorem FINITE_RECURSION :
    !(f:'a->'b->'b) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> (ITSET f {} b = b) /\
            !x s. FINITE s
                  ==> (ITSET f (x INSERT s) b =
                       if x IN s then ITSET f s b
                                 else f x (ITSET f s b))
Proof
    RW_TAC std_ss [ITSET_EMPTY]
 >> Cases_on `x IN s`
 >- (`x INSERT s = s` by PROVE_TAC [ABSORPTION] >> art [])
 >> ASM_SIMP_TAC std_ss []
 >> Know `ITSET f s b = ITSET f (s DELETE x) b`
 >- (`s DELETE x = s` by PROVE_TAC [DELETE_NON_ELEMENT] >> art [])
 >> Rewr'
 >> MATCH_MP_TAC COMMUTING_ITSET_RECURSES
 >> rename1 `i IN s` >> RW_TAC std_ss []
 >> Cases_on `x = y` >- art []
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

Theorem CARD_UNION_EQ:
    !s t u.
         FINITE u /\ (s INTER t = {}) /\ (s UNION t = u)
         ==> (CARD s + CARD t = CARD u)
Proof
  REPEAT STRIP_TAC THEN KNOW_TAC ``FINITE (s:'a->bool) /\ FINITE (t:'a->bool)``
  THENL [METIS_TAC [FINITE_UNION], ALL_TAC] THEN STRIP_TAC THEN
  ASSUME_TAC CARD_UNION THEN
  POP_ASSUM (MP_TAC o Q.SPEC `s`) THEN FULL_SIMP_TAC std_ss [] THEN
  DISCH_TAC THEN POP_ASSUM (MP_TAC o Q.SPEC `t`) THEN
  FULL_SIMP_TAC std_ss [CARD_EMPTY]
QED

Theorem SUBSET_RESTRICT:
   !s P. {x | x IN s /\ P x} SUBSET s
Proof
  SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION]
QED

Theorem FINITE_RESTRICT:
   !s:'a->bool P. FINITE s ==> FINITE {x | x IN s /\ P x}
Proof
METIS_TAC[SUBSET_RESTRICT, SUBSET_FINITE]
QED

(* ------------------------------------------------------------------------- *)
(* Choosing a smaller subset of a given size.                                *)
(* ------------------------------------------------------------------------- *)

Theorem SET_PROVE_CASES:
   !P:('a->bool)->bool.
       P {} /\ (!a s. ~(a IN s) ==> P(a INSERT s))
       ==> !s. P s
Proof
  MESON_TAC[SET_CASES]
QED

Theorem CHOOSE_SUBSET_STRONG:
   !n s:'a->bool.
        (FINITE s ==> n <= CARD s) ==> ?t. t SUBSET s /\ t HAS_SIZE n
Proof
  INDUCT_TAC THEN REWRITE_TAC[HAS_SIZE_0, HAS_SIZE_SUC] THENL
   [MESON_TAC[EMPTY_SUBSET], ALL_TAC] THEN
  ONCE_REWRITE_TAC [METIS [] ``((FINITE s ==> SUC n <= CARD s) ==>
   ?t. t SUBSET s /\ t <> {} /\ !a. a IN t ==> t DELETE a HAS_SIZE n) =
                           (\s. (FINITE s ==> SUC n <= CARD s) ==>
   ?t. t SUBSET s /\ t <> {} /\ !a. a IN t ==> t DELETE a HAS_SIZE n) s``] THEN
  MATCH_MP_TAC SET_PROVE_CASES THEN BETA_TAC THEN
  REWRITE_TAC[FINITE_EMPTY, CARD_EMPTY, CARD_INSERT, ARITH_PROVE ``~(SUC n <= 0)``] THEN
  MAP_EVERY X_GEN_TAC [``a:'a``, ``s:'a->bool``] THEN DISCH_TAC THEN
  ASM_SIMP_TAC std_ss [CARD_EMPTY, CARD_INSERT, FINITE_INSERT,
                       DECIDE “x <= SUC y <=> x <= y \/ x = SUC y”] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC ``s:'a->bool``) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN ``t:'a->bool`` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC ``(a:'a) INSERT t`` THEN
  REPEAT(CONJ_TAC THENL [ASM_SET_TAC[], ALL_TAC]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
  ASM_SIMP_TAC std_ss [HAS_SIZE, CARD_DELETE, FINITE_INSERT, FINITE_DELETE,
               CARD_EMPTY, CARD_INSERT] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[SUC_SUB1] THEN
  ASM_SET_TAC[]
QED

Theorem CHOOSE_SUBSET:
   !s:'a->bool. FINITE s ==> !n. n <= CARD s ==> ?t. t SUBSET s /\ t HAS_SIZE n
Proof
  MESON_TAC[CHOOSE_SUBSET_STRONG]
QED

Theorem HAS_SIZE_NUMSEG_LT:
   !n. {m | m < n} HAS_SIZE n
Proof
  INDUCT_TAC THENL
   [SUBGOAL_THEN ``{m:num | m < 0} = {}``
       (fn th => REWRITE_TAC[HAS_SIZE_0, th]) THEN
    SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY, GSPECIFICATION, LESS_THM, NOT_LESS_0],
    SUBGOAL_THEN ``{m | m < SUC n} = n INSERT {m | m < n}`` SUBST1_TAC THENL
     [SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INSERT] THEN ARITH_TAC,
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
    ASM_SIMP_TAC std_ss [HAS_SIZE, CARD_EMPTY, CARD_INSERT, FINITE_INSERT] THEN
    SIMP_TAC std_ss [GSPECIFICATION, LESS_REFL]]
QED

Theorem FINITE_NUMSEG_LT:
   !n:num. FINITE {m | m < n}
Proof
  REWRITE_TAC[REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_LT]
QED

Theorem HAS_SIZE_NUMSEG_LE:
   !n. {m | m <= n} HAS_SIZE (n + 1)
Proof
  REWRITE_TAC[GSYM LT_SUC_LE, HAS_SIZE_NUMSEG_LT, ADD1]
QED

Theorem FINITE_NUMSEG_LE:
   !n:num. FINITE {m | m <= n}
Proof
 SIMP_TAC std_ss [REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_LE]
QED

(* ------------------------------------------------------------------------- *)
(* A natural notation for segments of the naturals.                          *)
(* ------------------------------------------------------------------------- *)

Definition numseg:
  numseg m n = {x:num | m <= x /\ x <= n}
End

(* syntax is similar to the version also available for lists, where
   listRangeTheory has  [ m .. n ]
 *)
val _ = add_rule { block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                   fixity = Closefix,
                   paren_style = OnlyIfNecessary,
                   pp_elements = [TOK "{", TM, HardSpace 1, TOK "..",
                                  BreakSpace(1,1), TM, BreakSpace(0,0),
                                  TOK "}"],
                   term_name = "numseg" }

Theorem IN_NUMSEG[simp]:
  x IN {m .. n} <=> m <= x /\ x <= n
Proof
  simp[numseg]
QED

(* ‘count n’ re-expressed by numseg *)
Theorem COUNT_NUMSEG :
    !n. 0 < n ==> count n = {0..n-1}
Proof
    rw [Once EXTENSION]
QED

Theorem FINITE_NUMSEG:
  !m n. FINITE {m..n}
Proof
  rw[numseg] >> irule FINITE_SUBSET >> irule_at Any FINITE_COUNT >>
  qexists_tac ‘n + 1’ >> simp[SUBSET_DEF]
QED

Theorem NUMSEG_COMBINE_R:
   !m p n. m <= p + 1 /\ p <= n ==> {m..p} UNION {p+1..n} = {m..n}
Proof
  simp[EXTENSION]
QED

Theorem NUMSEG_COMBINE_L:
  !m p n. m <= p /\ p <= n + 1 ==> {m..p-1} UNION {p..n} = {m..n}
Proof
  simp[EXTENSION]
QED

Theorem NUMSEG_LREC:
  !m n. m <= n ==> m INSERT {m+1..n} = {m..n}
Proof
  simp[EXTENSION]
QED

Theorem NUMSEG_RREC:
  !m n. m <= n ==> n INSERT {m..n-1} = {m..n}
Proof
  simp[EXTENSION]
QED

Theorem NUMSEG_REC:
  !m n. m <= SUC n ==> {m..SUC n} = SUC n INSERT {m..n}
Proof SIMP_TAC std_ss [GSYM NUMSEG_RREC, SUC_SUB1]
QED

Theorem IN_NUMSEG_0:
   !m n. m IN {0..n} <=> m <= n
Proof simp[]
QED

Theorem NUMSEG_SING: !n. {n..n} = {n}
Proof simp[EXTENSION]
QED

Theorem NUMSEG_EMPTY:
  !m n. {m..n} = {} <=> n < m
Proof
  simp[EXTENSION] >> MESON_TAC[NOT_LESS_EQUAL, LESS_EQ_TRANS, LESS_EQ_REFL]
QED

Theorem CARD_NUMSEG_LEMMA:
  !m d. CARD{m..m+d} = d + 1
Proof
  GEN_TAC THEN INDUCT_TAC THEN
  fs[NUMSEG_SING, ADD_CLAUSES, NUMSEG_REC, FINITE_NUMSEG]
QED

Theorem CARD_NUMSEG:
  !m n. CARD {m..n} = n + 1 - m
Proof
  REPEAT GEN_TAC >> Cases_on ‘m <= n’
  >- (full_simp_tac bool_ss [LE_EXISTS, CARD_NUMSEG_LEMMA] >> simp[])
  >> fs[NOT_LESS_EQUAL]
  >> drule_then assume_tac (iffRL NUMSEG_EMPTY)
  >> simp[]
QED

Theorem HAS_SIZE_NUMSEG:
  !m n. {m..n} HAS_SIZE ((n + 1:num) - m)
Proof
  REWRITE_TAC[HAS_SIZE, FINITE_NUMSEG, CARD_NUMSEG]
QED

Theorem CARD_NUMSEG_1:
 !n. CARD{1..n} = n
Proof
  simp[CARD_NUMSEG]
QED

Theorem HAS_SIZE_NUMSEG_1:
  !n. {1..n} HAS_SIZE n
Proof
  REWRITE_TAC[CARD_NUMSEG, HAS_SIZE, FINITE_NUMSEG] THEN ARITH_TAC
QED

Theorem NUMSEG_CLAUSES:
  (!m. {m..0} = if m = 0 then {0} else {}) /\
  !m n. {m..SUC n} = if m <= SUC n then SUC n INSERT {m..n} else {m..n}
Proof
  rw[] >> simp[NUMSEG_EMPTY, NUMSEG_SING, NUMSEG_REC] >> simp[EXTENSION]
QED

Theorem FINITE_INDEX_NUMSEG:
  !s:'a->bool.
    FINITE s =
    ?f. (!i j. i IN {1..CARD s} /\ j IN {1..CARD s} /\ f i = f j ==> i = j) /\
        s = IMAGE f {1..CARD s}
Proof
  GEN_TAC >> reverse EQ_TAC >- MESON_TAC[FINITE_NUMSEG, IMAGE_FINITE] >>
  qid_spec_tac ‘s’ >> Induct_on ‘FINITE’ >> rw[NUMSEG_EMPTY] >>
  rename [‘e NOTIN s’, ‘s = IMAGE f _’] >> qabbrev_tac ‘C = CARD s’ >>
  qexists_tac ‘f (| SUC C |-> e |)’ >> simp[combinTheory.APPLY_UPDATE_THM] >>
  reverse conj_tac
  >- (simp[EXTENSION, combinTheory.APPLY_UPDATE_THM, AllCaseEqs(), SF DNF_ss] >>
      metis_tac[LE, DECIDE “x <= y ==> x <> SUC y”]) >>
  rpt gen_tac >> simp[AllCaseEqs()] >>
  ‘!i. 1 <= i /\ i <= C ==> f i <> e’ by (rfs[] >> rw[Abbr ‘C’] >> metis_tac[]) >>
  simp[LE] >> rpt strip_tac >> metis_tac[]
QED

Theorem FINITE_INDEX_NUMBERS:
  !s:'a->bool.
        FINITE s =
         ?k:num->bool f. (!i j. i IN k /\ j IN k /\ (f i = f j) ==> (i = j)) /\
                         FINITE k /\ (s = IMAGE f k)
Proof
  MESON_TAC[FINITE_INDEX_NUMSEG, FINITE_NUMSEG, IMAGE_FINITE]
QED

Theorem DISJOINT_NUMSEG:
  !m n p q. DISJOINT {m..n} {p..q} <=> n < p \/ q < m \/ n < m \/ q < p
Proof
 simp[DISJOINT_DEF, EXTENSION, NOT_LESS_EQUAL] >> rpt gen_tac >> eq_tac >>
 simp[] >> MESON_TAC[LESS_ANTISYM]
QED

Theorem NUMSEG_ADD_SPLIT:
  !m n p. m <= n + 1 ==> {m..n+p} = {m..n} UNION {n+1..n+p}
Proof
  REWRITE_TAC[EXTENSION, IN_UNION, IN_NUMSEG] THEN ARITH_TAC
QED

Theorem NUMSEG_OFFSET_IMAGE:
  !m n p. {m+p..n+p} = IMAGE (\i. i + p) {m..n}
Proof
  simp[EXTENSION, EQ_IMP_THM] >> rpt strip_tac >> rename [‘m + p <= x’] >>
  qexists_tac ‘x - p’ >> simp[]
QED

Theorem SUBSET_NUMSEG:
  !m n p q. {m..n} SUBSET {p..q} <=> n < m \/ p <= m /\ n <= q
Proof
  simp[SUBSET_DEF, EQ_IMP_THM] >>
  MESON_TAC[LESS_EQ_TRANS, NOT_LESS_EQUAL, LESS_EQ_REFL]
QED

(* ------------------------------------------------------------------------- *)
(* Equivalence with the more ad-hoc comprehension notation.                  *)
(* ------------------------------------------------------------------------- *)

Theorem NUMSEG_LE:
  !n. {x | x <= n} = {0..n}
Proof
  simp[EXTENSION]
QED

Theorem NUMSEG_LT:
  !n. {x | x < n} = if n = 0 then {} else {0..n-1}
Proof
  rw[EXTENSION]
QED

(* ------------------------------------------------------------------------- *)
(* Segment of natural numbers starting at a specific number.                 *)
(* ------------------------------------------------------------------------- *)

Definition from_def:
    from n = {m:num | n <= m}
End

Theorem FROM_0:
    from 0 = univ(:num)
Proof
    REWRITE_TAC [from_def, ZERO_LESS_EQ, GSPEC_T]
QED

Theorem IN_FROM:
    !m n. m IN from n <=> n <= m
Proof
    SIMP_TAC std_ss [from_def, GSPECIFICATION]
QED

Theorem DISJOINT_COUNT_FROM:   !n. DISJOINT (count n) (from n)
Proof
    RW_TAC arith_ss [from_def, count_def, DISJOINT_DEF, Once EXTENSION, NOT_IN_EMPTY,
                     GSPECIFICATION, IN_INTER]
QED

Theorem DISJOINT_FROM_COUNT:   !n. DISJOINT (from n) (count n)
Proof
    RW_TAC std_ss [Once DISJOINT_SYM, DISJOINT_COUNT_FROM]
QED

Theorem UNION_COUNT_FROM:   !n. (count n) UNION (from n) = UNIV
Proof
    RW_TAC arith_ss [from_def, count_def, Once EXTENSION, NOT_IN_EMPTY,
                     GSPECIFICATION, IN_UNION, IN_UNIV]
QED

Theorem UNION_FROM_COUNT:   !n. (from n) UNION (count n) = UNIV
Proof
    RW_TAC std_ss [Once UNION_COMM, UNION_COUNT_FROM]
QED

Theorem FROM_NOT_EMPTY :
    !n. from n <> {}
Proof
    RW_TAC std_ss [GSYM MEMBER_NOT_EMPTY, from_def, GSPECIFICATION]
 >> Q.EXISTS_TAC `n` >> REWRITE_TAC [LESS_EQ_REFL]
QED

Theorem COUNTABLE_FROM :
    !n. COUNTABLE (from n)
Proof
    PROVE_TAC [COUNTABLE_NUM]
QED

Theorem FROM_INTER_NUMSEG_GEN:
   !k m n. (from k) INTER {m..n} = if m < k then {k..n} else {m..n}
Proof
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  SIMP_TAC std_ss [from_def, GSPECIFICATION, IN_INTER, IN_NUMSEG, EXTENSION] THEN
  ARITH_TAC
QED

Theorem FROM_INTER_NUMSEG_MAX:
   !m n p. from p INTER {m..n} = {MAX p m..n}
Proof
  SIMP_TAC arith_ss [EXTENSION, IN_INTER, IN_NUMSEG, IN_FROM] THEN ARITH_TAC
QED

Theorem FROM_INTER_NUMSEG:
   !k n. (from k) INTER {0..n} = {k..n}
Proof
  SIMP_TAC std_ss [from_def, GSPECIFICATION, IN_INTER, IN_NUMSEG, EXTENSION] THEN
  ARITH_TAC
QED

Theorem INFINITE_FROM:
    !n. INFINITE(from n)
Proof
   GEN_TAC THEN KNOW_TAC ``from n = univ(:num) DIFF {i | i < n}`` THENL
  [SIMP_TAC std_ss [EXTENSION, from_def, IN_DIFF, IN_UNIV, GSPECIFICATION] THEN
   ARITH_TAC, DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC INFINITE_DIFF_FINITE' THEN
   REWRITE_TAC [FINITE_NUMSEG_LT, num_INFINITE]]
QED

(* ------------------------------------------------------------------------- *)
(* Topological sorting of a finite set.                                      *)
(* ------------------------------------------------------------------------- *)

val _ = temp_set_fixity "<<" (Infix(NONASSOC, 450))

Theorem TOPOLOGICAL_SORT:
   !(<<). (!x y:'a. x << y /\ y << x ==> (x = y)) /\
          (!x y z. x << y /\ y << z ==> x << z)
          ==> !n s. s HAS_SIZE n
                    ==> ?f. (s = IMAGE f {1..n}) /\
                            (!j k. j IN {1..n} /\ k IN {1..n} /\ j < k
                                   ==> ~(f k << f j))
Proof
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN ``!n s. s HAS_SIZE n /\ ~(s = {})
                      ==> ?a:'a. a IN s /\ !b. b IN (s DELETE a) ==> ~(b << a)``
  ASSUME_TAC THENL
   [INDUCT_TAC THEN
    REWRITE_TAC[HAS_SIZE_0, HAS_SIZE_SUC, TAUT `~(a /\ ~a)`] THEN
    X_GEN_TAC ``s:'a->bool`` THEN STRIP_TAC THEN
    UNDISCH_TAC ``(s:'a->bool) <> {}`` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC ``a:'a``) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC ``a:'a``) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC ``s DELETE (a:'a)``) THEN
    ASM_SIMP_TAC std_ss [SET_RULE ``a IN s ==> ((s DELETE a = {}) <=> (s = {a}))``] THEN
    ASM_CASES_TAC ``s = {a:'a}`` THEN ASM_SIMP_TAC std_ss [] THENL
     [EXISTS_TAC ``a:'a`` THEN SET_TAC[], ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN ``b:'a`` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC ``((a:'a) << (b:'a)) :bool`` THENL
     [EXISTS_TAC ``a:'a``, EXISTS_TAC ``b:'a``] THEN ASM_SET_TAC[],
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [SIMP_TAC arith_ss [HAS_SIZE_0, NUMSEG_CLAUSES, IMAGE_EMPTY, IMAGE_INSERT, NOT_IN_EMPTY],
    ALL_TAC] THEN
  REWRITE_TAC[HAS_SIZE_SUC] THEN X_GEN_TAC ``s:'a->bool`` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [``SUC n``, ``s:'a->bool``]) THEN
  ASM_REWRITE_TAC[HAS_SIZE_SUC] THEN
  DISCH_THEN(X_CHOOSE_THEN ``a:'a`` MP_TAC) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC ``s DELETE (a:'a)``) THEN ASM_SIMP_TAC std_ss [] THEN
  DISCH_THEN(X_CHOOSE_THEN ``f:num->'a`` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC ``\k. if k = 1n then a:'a else f(k - 1)`` THEN
  SIMP_TAC std_ss [ARITH_PROVE ``1 <= k ==> ~(SUC k = 1)``, SUC_SUB1] THEN
  SUBGOAL_THEN ``!i. i IN {1..SUC n} <=> i = 1 \/ 1 < i /\ i - 1 IN {1..n}``
   (fn th => REWRITE_TAC[EXTENSION, IN_IMAGE, th])
  THENL [REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC, ALL_TAC] THEN CONJ_TAC THENL
   [X_GEN_TAC ``b:'a`` THEN ASM_CASES_TAC ``b:'a = a`` THENL
     [METIS_TAC[], ALL_TAC] THEN
    FIRST_ASSUM(fn th => ONCE_REWRITE_TAC[MATCH_MP
     (SET_RULE ``~(b = a) ==> (b IN s <=> b IN (s DELETE a))``) th]) THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    ASM_REWRITE_TAC[IN_IMAGE, IN_NUMSEG] THEN
    EQ_TAC THENL [ALL_TAC, METIS_TAC[]] THEN
    DISCH_THEN(X_CHOOSE_TAC ``i:num``) THEN EXISTS_TAC ``i + 1:num`` THEN
    ASM_SIMP_TAC arith_ss [ARITH_PROVE ``1 <= x ==> 1 < x + 1 /\ ~(x + 1 = 1:num)``, ADD_SUB],
    MAP_EVERY X_GEN_TAC [``j:num``, ``k:num``] THEN
    MAP_EVERY ASM_CASES_TAC [``j = 1:num``, ``k = 1:num``] THEN
    ASM_REWRITE_TAC[LESS_REFL] THENL
     [STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SET_TAC[],
      ARITH_TAC,
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC arith_ss []]]
QED

(* Another form using relationTheory and (count n), added by Chun Tian

   NOTE: the set sorting is slightly different with list sorting, as there are
   no duplicated elements in sets, thus the sorting result (given by an index
   function) has strict orders for each pair of elements.

   Also, the sorting requirements is slightly different: list sorting requires
  ‘transitive’ and ‘total’ (cf. sortingTheory.QSORT_SORTED), while set sorting
   here requires ‘transitive’ and ‘antisymmetric’. (‘~R x y’ also means that
   x and y are incomparable, i.e. some part of ‘f’ is an "antichain".)
 *)
Theorem TOPOLOGICAL_SORT' :
    !R s n. transitive R /\ antisymmetric R /\ s HAS_SIZE n ==>
            ?f. s = IMAGE f (count n) /\
                !j k. j < n /\ k < n /\ j < k ==> ~(R (f k) (f j))
Proof
    RW_TAC std_ss []
 >> MP_TAC (REWRITE_RULE [GSYM transitive_def, GSYM antisymmetric_def]
                         (Q.SPEC ‘R’ TOPOLOGICAL_SORT))
 >> RW_TAC std_ss []
 >> POP_ASSUM (MP_TAC o (Q.SPECL [‘n’, ‘s’]))
 >> RW_TAC std_ss [IN_NUMSEG]
 >> Q.EXISTS_TAC ‘f o SUC’
 >> CONJ_TAC
 >- (rw [Once EXTENSION, IN_IMAGE, IN_COUNT, IN_NUMSEG] \\
     EQ_TAC >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       rename1 ‘i <= n’ >> Q.EXISTS_TAC ‘PRE i’ >> rw [] \\
       Suff ‘SUC (PRE i) = i’ >- Rewr \\
       rw [GSYM SUC_PRE],
       (* goal 2 (of 2) *)
       rename1 ‘i < n’ >> Q.EXISTS_TAC ‘SUC i’ >> rw [] ])
 >> RW_TAC arith_ss []
QED

(* ------------------------------------------------------------------------- *)
(* Generic iteration of operation over set with finite support.              *)
(* ------------------------------------------------------------------------- *)

Definition neutral[nocompute]:
  neutral op = @x. !y. (op x y = y) /\ (op y x = y)
End

(* NOTE: The set of all numbers of the involved type, ‘op’ and ‘neutral op’
   actually form an Abelian Monoid (also called Commutative Monoid), i.e.

   |- monoidal op <=>
      AbelianMonoid <| carrier = UNIV, op = op, id = (neutral op) |>

   (see also AbelianMonoid_def in examples/algebra/monoid/monoidScript.sml)
 *)
Definition monoidal[nocompute]:
  monoidal op <=> (!x y. op x y = op y x) /\
                    (!x y z. op x (op y z) = op (op x y) z) /\
                    (!x:'a. op (neutral op) x = x)
End

Theorem MONOIDAL_AC:
    !op. monoidal op
         ==> (!a. op (neutral op) a = a) /\
             (!a. op a (neutral op) = a) /\
             (!a b. op a b = op b a) /\
             (!a b c. op (op a b) c = op a (op b c)) /\
             (!a b c. op a (op b c) = op b (op a c))
Proof
  REWRITE_TAC[monoidal] THEN MESON_TAC[]
QED

Definition support[nocompute]:
  support op (f:'a->'b) s = {x | x IN s /\ ~(f x = neutral op)}
End

Definition iterate[nocompute]:
  iterate op (s:'a->bool) f =
         if FINITE(support op f s)
         then ITSET (\x a. op (f x) a) (support op f s) (neutral op)
         else neutral op
End

Theorem IN_SUPPORT:
    !op f x s. x IN (support op f s) <=> x IN s /\ ~(f x = neutral op)
Proof
   SIMP_TAC std_ss [support, GSPECIFICATION]
QED

Theorem SUPPORT_SUPPORT:
    !op f s. support op f (support op f s) = support op f s
Proof
  SIMP_TAC std_ss [support, GSPECIFICATION, EXTENSION]
QED

Theorem SUPPORT_EMPTY:
    !op f s. (!x. x IN s ==> (f(x) = neutral op)) <=> (support op f s = {})
Proof
   SIMP_TAC std_ss [IN_SUPPORT, EXTENSION, GSPECIFICATION, NOT_IN_EMPTY] THEN
   MESON_TAC[]
QED

Theorem SUPPORT_SUBSET:
    !op f s. (support op f s) SUBSET s
Proof
  SIMP_TAC std_ss [SUBSET_DEF, IN_SUPPORT]
QED

Theorem FINITE_SUPPORT:
    !op f s. FINITE s ==> FINITE(support op f s)
Proof
  MESON_TAC[SUPPORT_SUBSET, SUBSET_FINITE]
QED

Theorem SUPPORT_CLAUSES:
   (!f. support op f {} = {}) /\
   (!f x s. support op f (x INSERT s) =
       if f(x) = neutral op then support op f s
       else x INSERT (support op f s)) /\
   (!f x s. support op f (s DELETE x) = (support op f s) DELETE x) /\
   (!f s t. support op f (s UNION t) =
                    (support op f s) UNION (support op f t)) /\
   (!f s t. support op f (s INTER t) =
                    (support op f s) INTER (support op f t)) /\
   (!f s t. support op f (s DIFF t) =
                    (support op f s) DIFF (support op f t)) /\
   (!f g s.  support op g (IMAGE f s) = IMAGE f (support op (g o f) s))
Proof
  SIMP_TAC std_ss [support, EXTENSION, GSPECIFICATION, IN_INSERT, IN_DELETE, o_THM,
    IN_IMAGE, NOT_IN_EMPTY, IN_UNION, IN_INTER, IN_DIFF, COND_RAND] THEN
  REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN ASM_MESON_TAC[]
QED

Theorem SUPPORT_DELTA:
   !op s f a. support op (\x. if x = a then f(x) else neutral op) s =
              if a IN s then support op f {a} else {}
Proof
  SIMP_TAC std_ss [EXTENSION, support, GSPECIFICATION, IN_SING] THEN
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN
  FULL_SIMP_TAC std_ss [GSPECIFICATION, NOT_IN_EMPTY]
QED

Theorem FINITE_SUPPORT_DELTA:
   !op f a. FINITE(support op (\x. if x = a then f(x) else neutral op) s)
Proof
  REWRITE_TAC[SUPPORT_DELTA] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  SIMP_TAC std_ss [FINITE_EMPTY, FINITE_INSERT, FINITE_SUPPORT]
QED

(* ------------------------------------------------------------------------- *)
(* Key lemmas about the generic notion.                                      *)
(* ------------------------------------------------------------------------- *)

Theorem ITERATE_SUPPORT:
   !op f s. iterate op (support op f s) f = iterate op s f
Proof
  SIMP_TAC std_ss [iterate, SUPPORT_SUPPORT]
QED

Theorem ITERATE_EXPAND_CASES:
   !op f s. iterate op s f =
              if FINITE(support op f s) then iterate op (support op f s) f
              else neutral op
Proof
  SIMP_TAC std_ss [iterate, SUPPORT_SUPPORT]
QED

Theorem ITERATE_CLAUSES_GEN:
   !op. monoidal op
        ==> (!(f:'a->'b). iterate op {} f = neutral op) /\
            (!f x s. monoidal op /\ FINITE(support op (f:'a->'b) s)
                     ==> (iterate op (x INSERT s) f =
                                if x IN s then iterate op s f
                                else op (f x) (iterate op s f)))
Proof
  GEN_TAC THEN STRIP_TAC THEN CONV_TAC AND_FORALL_CONV THEN
  GEN_TAC THEN MP_TAC(ISPECL [``\x a. (op:'b->'b->'b) ((f:'a->'b)(x)) a``,
                              ``neutral op :'b``] FINITE_RECURSION) THEN
  KNOW_TAC ``(!(x :'a) (y :'a) (s :'b). x <> y ==>
        ((\(x :'a) (a :'b). (op :'b -> 'b -> 'b) ((f :'a -> 'b) x) a) x
        ((\(x :'a) (a :'b). op (f x) a) y s) = (\(x :'a) (a :'b). op (f x) a) y
        ((\(x :'a) (a :'b). op (f x) a) x s)))`` THENL
  [ASM_MESON_TAC [monoidal], FULL_SIMP_TAC std_ss [] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[iterate, SUPPORT_CLAUSES, FINITE_EMPTY, FINITE_INSERT] THEN
  GEN_REWR_TAC (LAND_CONV o RATOR_CONV o LAND_CONV) [COND_RAND] THEN
  ASM_REWRITE_TAC[SUPPORT_CLAUSES, FINITE_INSERT, COND_ID] THEN
  ASM_CASES_TAC ``(f:'a->'b) x = neutral op`` THEN ASM_SIMP_TAC std_ss [IN_SUPPORT] THEN
 COND_CASES_TAC THEN ASM_MESON_TAC[monoidal]]
QED

Theorem ITERATE_CLAUSES:
   !op. monoidal op
        ==> (!f:('b->'a). iterate op {} f = neutral op) /\
            (!f:('b->'a) x s. FINITE(s)
                     ==> (iterate op (x INSERT s) f =
                          if x IN s then iterate op s f
                          else op (f x) (iterate op s f)))
Proof
  SIMP_TAC std_ss [ITERATE_CLAUSES_GEN, FINITE_SUPPORT]
QED

Theorem ITERATE_UNION:
   !op. monoidal op
        ==> !f s t. FINITE s /\ FINITE t /\ DISJOINT s t
                    ==> (iterate op (s UNION t) f =
                         op (iterate op s f) (iterate op t f))
Proof
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC [GSYM AND_IMP_INTRO] THEN SIMP_TAC std_ss [RIGHT_FORALL_IMP_THM] THEN
  REPEAT DISCH_TAC THEN
  KNOW_TAC ``!t. (DISJOINT (s :'b -> bool) (t :'b -> bool) ==>
   (iterate (op :'a -> 'a -> 'a) (s UNION t) (f :'b -> 'a) =
   op (iterate op s f) (iterate op t f))) = (\t. DISJOINT s t ==>
   (iterate op (s UNION t) f = op (iterate op s f) (iterate op t f))) t``
  THENL [FULL_SIMP_TAC std_ss [], DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  ASM_SIMP_TAC std_ss [ITERATE_CLAUSES, UNION_EMPTY] THEN
  SIMP_TAC std_ss [GSYM RIGHT_FORALL_IMP_THM] THEN
  ONCE_REWRITE_TAC [DISJOINT_SYM] THEN FULL_SIMP_TAC std_ss [DISJOINT_INSERT]
  THEN ONCE_REWRITE_TAC [UNION_COMM] THEN SIMP_TAC std_ss [INSERT_UNION] THEN
  ASM_SIMP_TAC std_ss [ITERATE_CLAUSES, IN_UNION, UNION_EMPTY,
  FINITE_UNION] THEN ASM_MESON_TAC[monoidal]]
QED

Theorem ITERATE_UNION_GEN:
   !op. monoidal op
        ==> !(f:'a->'b) s t. FINITE(support op f s) /\ FINITE(support op f t) /\
                           DISJOINT (support op f s) (support op f t)
                           ==> (iterate op (s UNION t) f =
                                op (iterate op s f) (iterate op t f))
Proof
  ONCE_REWRITE_TAC[GSYM ITERATE_SUPPORT] THEN
  SIMP_TAC std_ss [SUPPORT_CLAUSES, ITERATE_UNION]
QED

val lemma = prove (
 ``!t s. t SUBSET s ==> (s = (s DIFF t) UNION t) /\ DISJOINT (s DIFF t) t``,
    rpt STRIP_TAC
 >| [ (* goal 1 (of 2) *)
      SIMP_TAC std_ss [UNION_DEF, DIFF_DEF, EXTENSION, GSPECIFICATION] \\
      GEN_TAC \\
      EQ_TAC >- FULL_SIMP_TAC std_ss [] \\
      STRIP_TAC \\
      FULL_SIMP_TAC std_ss [SUBSET_DEF],
      (* goal 2 (of 2) *)
      SIMP_TAC std_ss [DISJOINT_DEF, INTER_DEF, DIFF_DEF,
                       EXTENSION, GSPECIFICATION, NOT_IN_EMPTY] ]);

Theorem ITERATE_DIFF:
   !op. monoidal op
        ==> !f s t. FINITE s /\ t SUBSET s
                    ==> (op (iterate op (s DIFF t) f) (iterate op t f) =
                         iterate op s f)
Proof
  MESON_TAC[lemma, ITERATE_UNION, FINITE_UNION, SUBSET_FINITE, SUBSET_DIFF]
QED

Theorem ITERATE_DIFF_GEN:
   !op. monoidal op
        ==> !f:'a->'b s t. FINITE (support op f s) /\
                         (support op f t) SUBSET (support op f s)
                         ==> (op (iterate op (s DIFF t) f) (iterate op t f) =
                              iterate op s f)
Proof
  ONCE_REWRITE_TAC[GSYM ITERATE_SUPPORT] THEN
  SIMP_TAC std_ss [SUPPORT_CLAUSES, ITERATE_DIFF]
QED


val lemma1 = prove (
 ``!a b. a UNION b = ((a DIFF b) UNION (b DIFF a)) UNION (a INTER b)``,
  REPEAT GEN_TAC THEN REWRITE_TAC [UNION_DEF, DIFF_DEF, INTER_DEF]
  THEN SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN GEN_TAC THEN
  EQ_TAC THEN STRIP_TAC THEN RW_TAC std_ss []);

val lemma2 = prove (
 ``!s t f. op (iterate op s f) (iterate op t f) =
           op (iterate op (s DIFF t UNION s INTER t) f)
              (iterate op (t DIFF s UNION s INTER t) f)``,
  REPEAT GEN_TAC THEN
  KNOW_TAC ``((s:'a->bool) = s DIFF t UNION s INTER t) /\
             ((t:'a->bool)= t DIFF s UNION s INTER t)`` THENL
  [REWRITE_TAC [DIFF_DEF, UNION_DEF, DIFF_DEF, INTER_DEF] THEN
  SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN CONJ_TAC THENL
  [GEN_TAC THEN EQ_TAC THENL [RW_TAC std_ss [], RW_TAC std_ss []],
  GEN_TAC THEN EQ_TAC THENL [RW_TAC std_ss [], RW_TAC std_ss []]],
  DISCH_TAC THEN METIS_TAC []]);

val lemma3 = prove (
  ``!s t. DISJOINT (s DIFF t UNION t DIFF s) (s INTER s') /\
            DISJOINT (s DIFF t) (t DIFF s) /\
            DISJOINT (s DIFF t) (t INTER s) /\
            DISJOINT (s DIFF t) (s INTER t)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [DISJOINT_DEF, DIFF_DEF, UNION_DEF, INTER_DEF] THEN
  SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN
  CONV_TAC CONJ_FORALL_CONV THEN GEN_TAC THEN CONJ_TAC THENL
  [EQ_TAC THENL [RW_TAC std_ss [], RW_TAC std_ss [NOT_IN_EMPTY]], CONJ_TAC THENL
  [EQ_TAC THENL [RW_TAC std_ss [], RW_TAC std_ss [NOT_IN_EMPTY]], CONJ_TAC THENL
  [EQ_TAC THENL [RW_TAC std_ss [], RW_TAC std_ss [NOT_IN_EMPTY]],
  EQ_TAC THENL [RW_TAC std_ss [], RW_TAC std_ss [NOT_IN_EMPTY]]]]]);

Theorem ITERATE_INCL_EXCL:
   !op. monoidal op
        ==> !s t f. FINITE s /\ FINITE t
                    ==> (op (iterate op s f) (iterate op t f) =
                         op (iterate op (s UNION t) f)
                            (iterate op (s INTER t) f))
Proof
 REPEAT STRIP_TAC THEN
 ONCE_REWRITE_TAC [lemma1] THEN GEN_REWR_TAC (LAND_CONV) [lemma2] THEN
 KNOW_TAC ``(FINITE ((s:'b->bool) DIFF (t:'b->bool) UNION (t DIFF s))) /\
  (FINITE (s INTER t)) /\ (DISJOINT (s DIFF t UNION (t DIFF s)) (s INTER t))`` THENL
 [FULL_SIMP_TAC std_ss [FINITE_DIFF, FINITE_UNION, FINITE_INTER] THEN
 SIMP_TAC std_ss [DISJOINT_DEF, DIFF_DEF, UNION_DEF, INTER_DEF, EXTENSION, GSPECIFICATION]
 THEN GEN_TAC THEN EQ_TAC THENL [RW_TAC std_ss [], RW_TAC std_ss [NOT_IN_EMPTY]],
 STRIP_TAC THEN ASM_SIMP_TAC std_ss [ITERATE_UNION, FINITE_UNION, FINITE_DIFF,
 FINITE_INTER, lemma3] THEN METIS_TAC [MONOIDAL_AC]]
QED

Theorem ITERATE_CLOSED:
   !op. monoidal op
        ==> !P. P(neutral op) /\ (!x y. P x /\ P y ==> P (op x y))
                ==> !f:'a->'b s. (!x. x IN s /\ ~(f x = neutral op) ==> P(f x))
                               ==> P(iterate op s f)
Proof
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[GSYM IN_SUPPORT] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [] THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC(``support op (f:'a->'b) s``,``s:'a->bool``) THEN
  GEN_TAC THEN KNOW_TAC ``(monoidal (op :'b -> 'b -> 'b) ==>
  (P :'b -> bool) (neutral op) ==> (!(x :'b) (y :'b). P x /\
  P y ==> P (op x y)) ==> (!(x :'a). x IN s ==>
  P ((f :'a -> 'b) x)) ==> P (iterate op s f)) =
  ((\s. monoidal op ==> P (neutral op) ==>
  (!x y. P x /\ P y ==> P (op x y)) ==> (!x. x IN s ==> P (f x)) ==>
  P (iterate op s f))s)`` THENL [FULL_SIMP_TAC std_ss [],
  DISCH_TAC THEN ONCE_ASM_REWRITE_TAC []
  THEN MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  ASM_SIMP_TAC std_ss [ITERATE_CLAUSES, FINITE_INSERT, IN_INSERT]]
QED

Theorem ITERATE_RELATED:
   !op. monoidal op
        ==> !R. R (neutral op) (neutral op) /\
                (!x1 y1 x2 y2. R x1 x2 /\ R y1 y2 ==> R (op x1 y1) (op x2 y2))
                ==> !f:'a->'b g s.
                      FINITE s /\
                      (!x. x IN s ==> R (f x) (g x))
                      ==> R (iterate op s f) (iterate op s g)
Proof
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  GEN_TAC THEN REWRITE_TAC[GSYM AND_IMP_INTRO] THEN GEN_TAC THEN
  KNOW_TAC ``(!x. x IN s ==> R (f x) (g x)) ==>
    R (iterate op s f) (iterate op s g) <=> (\s. (!x. x IN s ==> R (f x) (g x)) ==>
    R (iterate op s f) (iterate op s g)) s`` THENL [FULL_SIMP_TAC std_ss [],
   DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  ASM_SIMP_TAC std_ss [ITERATE_CLAUSES, FINITE_INSERT, IN_INSERT]]
QED

Theorem ITERATE_EQ_NEUTRAL:
   !op. monoidal op
        ==> !f:'a->'b s. (!x. x IN s ==> (f(x) = neutral op))
                       ==> (iterate op s f = neutral op)
Proof
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN ``support op (f:'a->'b) s = {}`` ASSUME_TAC THENL
   [ASM_MESON_TAC[EXTENSION, NOT_IN_EMPTY, IN_SUPPORT],
    ASM_MESON_TAC[ITERATE_CLAUSES, FINITE_EMPTY, ITERATE_SUPPORT]]
QED

Theorem ITERATE_SING:
   !op. monoidal op ==> !f:'a->'b x. (iterate op {x} f = f x)
Proof
  SIMP_TAC std_ss [ITERATE_CLAUSES, FINITE_EMPTY, NOT_IN_EMPTY] THEN
  MESON_TAC[monoidal]
QED

Theorem ITERATE_DELETE:
   !op. monoidal op
        ==> !(f:'a->'b) s a. FINITE s /\ a IN s
        ==> (op (f a) (iterate op (s DELETE a) f) = iterate op s f)
Proof
  METIS_TAC[ITERATE_CLAUSES, FINITE_DELETE, IN_DELETE, INSERT_DELETE]
QED

Theorem ITERATE_DELTA:
   !op. monoidal op
        ==> !f a s. iterate op s (\x. if x = a then f(x) else neutral op) =
                    if a IN s then f(a) else neutral op
Proof
  GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM ITERATE_SUPPORT] THEN
  REWRITE_TAC[SUPPORT_DELTA] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC std_ss [ITERATE_CLAUSES] THEN REWRITE_TAC[SUPPORT_CLAUSES] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC std_ss [ITERATE_CLAUSES, ITERATE_SING]
QED

val lemma = prove (
 ``(a <=> a') /\ (a' ==> (b = b'))
      ==> ((if a then b else c) = (if a' then b' else c))``,
  METIS_TAC []);

Theorem ITERATE_IMAGE:
   !op. monoidal op
       ==> !f:'a->'b g:'b->'c s.
                (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
                ==> (iterate op (IMAGE f s) g = iterate op s (g o f))
Proof
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN GEN_TAC THEN
  SUBGOAL_THEN ``!s. FINITE s /\
        (!x y:'a. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
        ==> (iterate op (IMAGE f s) (g:'b->'c) = iterate op s (g o f))``
  ASSUME_TAC THENL [REWRITE_TAC[GSYM AND_IMP_INTRO] THEN GEN_TAC THEN
  KNOW_TAC ``((!x y. x IN s ==> y IN s ==> (f x = f y) ==> (x = y)) ==>
              (iterate op (IMAGE f s) g = iterate op s (g o f))) =
         (\s. (!x y. x IN s ==> y IN s ==> (f x = f y) ==> (x = y)) ==>
              (iterate op (IMAGE f s) g = iterate op s (g o f))) s``
  THENL [FULL_SIMP_TAC std_ss [], DISCH_TAC THEN ONCE_ASM_REWRITE_TAC []
  THEN MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  ASM_SIMP_TAC std_ss [ITERATE_CLAUSES, IMAGE_EMPTY, IMAGE_INSERT, IMAGE_FINITE] THEN
  REWRITE_TAC[o_THM, IN_INSERT] THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
  [METIS_TAC[IN_IMAGE], METIS_TAC[IN_IMAGE]]], GEN_TAC THEN DISCH_TAC
  THEN ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC lemma THEN REWRITE_TAC[SUPPORT_CLAUSES] THEN REPEAT STRIP_TAC THENL
  [MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN ASM_MESON_TAC[IN_SUPPORT],
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[IN_SUPPORT]]]
QED

Theorem ITERATE_BIJECTION:
   !op. monoidal op
        ==>  !(f:'a->'b) p s.
                (!x. x IN s ==> (p x IN s)) /\
                (!y. y IN s ==> ?!x. x IN s /\ (p x = y))
                ==> (iterate op s f = iterate op s (f o p))
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC ``iterate op (IMAGE (p:'a->'a) s) (f:'a->'b)`` THEN CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN SIMP_TAC std_ss[EXTENSION, IN_IMAGE] THEN METIS_TAC [],
    METIS_TAC[ITERATE_IMAGE]]
QED

Theorem ITERATE_PERMUTES :
    !op. monoidal op
         ==> !(f:'a->'b) p s. p PERMUTES s
                ==> (iterate op s f = iterate op s (f o p))
Proof
    RW_TAC std_ss [BIJ_ALT, IN_FUNSET]
 >> irule ITERATE_BIJECTION
 >> RW_TAC std_ss []
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

val lemma1 = prove (
 ``{a,b | F} = {}``,
  SRW_TAC [][EXTENSION]);

val lemma2 = prove (
 ``{i,j | i IN a INSERT s /\ j IN t i} =
            IMAGE (\j. a,j) (t a) UNION {i,j | i IN s /\ j IN t i}``,
  SRW_TAC [][EXTENSION] THEN SET_TAC []);

Theorem ITERATE_ITERATE_PRODUCT:
   !op. monoidal op
        ==> !s:'a->bool t:'a->'b->bool x:'a->'b->'c.
                FINITE s /\ (!i. i IN s ==> FINITE(t i))
                ==> (iterate op s (\i. iterate op (t i) (x i)) =
                     iterate op {i,j | i IN s /\ j IN t i} (\(i,j). x i j))
Proof
  GEN_TAC THEN DISCH_TAC THEN
  SIMP_TAC std_ss [GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN
  KNOW_TAC ``(!t:'a->'b->bool. (!i. i IN s ==> FINITE (t i)) ==>
        !x:'a->'b->'c. iterate op s (\i. iterate op (t i) (x i)) =
            iterate op {(i,j) | i IN s /\ j IN t i} (\(i,j). x i j)) =
             (\s. !t:'a->'b->bool. (!i. i IN s ==> FINITE (t i)) ==>
        !x:'a->'b->'c. iterate op s (\i. iterate op (t i) (x i)) =
            iterate op {(i,j) | i IN s /\ j IN t i} (\(i,j). x i j)) (s:'a->bool)``
  THENL [FULL_SIMP_TAC std_ss [], ALL_TAC] THEN DISC_RW_KILL THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  ASM_SIMP_TAC std_ss [NOT_IN_EMPTY, lemma1, ITERATE_CLAUSES] THEN
  REWRITE_TAC[lemma2] THEN ASM_SIMP_TAC std_ss [FINITE_INSERT, ITERATE_CLAUSES,
  IN_INSERT] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fn th =>
   W(MP_TAC o PART_MATCH (lhand o rand) (MATCH_MP ITERATE_UNION th) o
   rand o snd)) THEN
   KNOW_TAC ``FINITE (IMAGE (\j. (e,j)) ((t:'a->'b->bool) e)) /\
     FINITE {(i,j) | i IN (s:'a->bool) /\ j IN t i} /\
     DISJOINT (IMAGE (\j. (e,j)) (t e)) {(i,j) | i IN s /\ j IN t i}`` THENL
  [ASM_SIMP_TAC std_ss [IMAGE_FINITE, FINITE_PRODUCT_DEPENDENT, IN_INSERT] THEN
    SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_IMAGE, IN_INTER, NOT_IN_EMPTY,
    GSPECIFICATION, EXISTS_PROD, FORALL_PROD, PAIR_EQ] THEN ASM_MESON_TAC[],
    ALL_TAC] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  FIRST_ASSUM(fn th =>
   W(MP_TAC o PART_MATCH (lhand o rand) (MATCH_MP ITERATE_IMAGE th) o
   rand o snd)) THEN KNOW_TAC ``(!x:'b y:'b. x IN (t:'a->'b->bool) (e:'a) /\
       y IN t e /\ ((\j. (e,j)) x = (\j. (e,j)) y) ==> (x = y))`` THENL
  [SIMP_TAC std_ss [FORALL_PROD], ALL_TAC] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF] THEN
  CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN FULL_SIMP_TAC std_ss [ETA_AX]
  THEN AP_TERM_TAC THEN METIS_TAC []
QED

Theorem ITERATE_EQ:
   !op. monoidal op
        ==> !f:'a->'b g s.
              (!x. x IN s ==> (f x = g x)) ==> (iterate op s f = iterate op s g)
Proof
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN
  SUBGOAL_THEN ``support op g s = support op (f:'a->'b) s`` SUBST1_TAC THENL
  [REWRITE_TAC[EXTENSION, IN_SUPPORT] THEN ASM_MESON_TAC[], COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN SUBGOAL_THEN
   ``FINITE(support op (f:'a->'b) s) /\
    (!x. x IN (support op f s) ==> (f x = g x))``
  MP_TAC THENL [ASM_MESON_TAC[IN_SUPPORT], REWRITE_TAC[GSYM AND_IMP_INTRO] THEN
  SPEC_TAC(``support op (f:'a->'b) s``,``t:'a->bool``) THEN GEN_TAC THEN
  KNOW_TAC ``(!x. x IN t ==> (f x = g x)) ==> (iterate op t f = iterate op t g) <=>
        (\t. (!x. x IN t ==> (f x = g x)) ==> (iterate op t f = iterate op t g)) t``
  THENL [FULL_SIMP_TAC std_ss [], DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN ASM_SIMP_TAC std_ss [ITERATE_CLAUSES] THEN
  MESON_TAC[IN_INSERT]]]]
QED

Theorem ITERATE_EQ_GENERAL:
   !op. monoidal op
        ==> !s:'a->bool t:'b->bool f:'a->'c g h.
                (!y. y IN t ==> ?!x. x IN s /\ (h(x) = y)) /\
                (!x. x IN s ==> h(x) IN t /\ (g(h x) = f x))
                ==> (iterate op s f = iterate op t g)
Proof
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN ``t = IMAGE (h:'a->'b) s`` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION, IN_IMAGE] THEN ASM_MESON_TAC[],
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC ``iterate op s ((g:'b->'c) o (h:'a->'b))`` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[ITERATE_EQ, o_THM],
    CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_IMAGE) THEN
    ASM_MESON_TAC[]]]
QED

Theorem ITERATE_EQ_GENERAL_INVERSES:
   !op. monoidal op
        ==> !s:'a->bool t:'b->bool f:'a->'c g h k.
                (!y. y IN t ==> k(y) IN s /\ (h(k y) = y)) /\
                (!x. x IN s ==> h(x) IN t /\ (k(h x) = x) /\ (g(h x) = f x))
                ==> (iterate op s f = iterate op t g)
Proof
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_EQ_GENERAL) THEN
  EXISTS_TAC ``h:'a->'b`` THEN ASM_MESON_TAC[]
QED

Theorem ITERATE_INJECTION:
   !op. monoidal op
          ==> !f:'a->'b p:'a->'a s.
                      FINITE s /\
                      (!x. x IN s ==> p x IN s) /\
                      (!x y. x IN s /\ y IN s /\ (p x = p y) ==> (x = y))
                      ==> (iterate op s (f o p) = iterate op s f)
Proof
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_BIJECTION) THEN
  MP_TAC(ISPECL [``s:'a->bool``, ``p:'a->'a``] SURJECTIVE_IFF_INJECTIVE) THEN
  ASM_REWRITE_TAC[SUBSET_DEF, IN_IMAGE] THEN ASM_MESON_TAC[]
QED

Theorem ITERATE_UNION_NONZERO:
   !op. monoidal op
        ==> !f:'a->'b s t.
                FINITE(s) /\ FINITE(t) /\
                (!x. x IN (s INTER t) ==> (f x = neutral(op)))
                ==> (iterate op (s UNION t) f =
                    op (iterate op s f) (iterate op t f))
Proof
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM ITERATE_SUPPORT] THEN
  REWRITE_TAC[SUPPORT_CLAUSES] THEN KNOW_TAC
  ``FINITE (support op (f :'a -> 'b) (s :'a -> bool)) /\
    FINITE (support op f (t :'a -> bool)) /\
    DISJOINT (support op f s) (support op f t)`` THENL
  [ASM_SIMP_TAC std_ss [FINITE_SUPPORT, DISJOINT_DEF, IN_INTER,
  IN_SUPPORT, EXTENSION] THEN ASM_MESON_TAC[IN_INTER, NOT_IN_EMPTY],
  ASM_MESON_TAC[ITERATE_UNION]]
QED

Theorem ITERATE_OP:
   !op. monoidal op
        ==> !f g s. FINITE s
                    ==> (iterate op s (\x. op (f x) (g x)) =
                        op (iterate op s f) (iterate op s g))
Proof
  GEN_TAC THEN DISCH_TAC THEN
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  KNOW_TAC ``((iterate :('a -> 'a -> 'a) -> ('b -> bool) -> ('b -> 'a) -> 'a)
       (op :'a -> 'a -> 'a) s
       (\(x :'b). op ((f :'b -> 'a) x) ((g :'b -> 'a) x)) =
     op (iterate op s f) (iterate op s g)) =
           (\s. ((iterate :('a -> 'a -> 'a) -> ('b -> bool) -> ('b -> 'a) -> 'a)
       (op :'a -> 'a -> 'a) s
       (\(x :'b). op ((f :'b -> 'a) x) ((g :'b -> 'a) x)) =
     op (iterate op s f) (iterate op s g)))s ``THENL [FULL_SIMP_TAC std_ss [],
  DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  ASM_SIMP_TAC std_ss [ITERATE_CLAUSES, MONOIDAL_AC]]
QED

Theorem ITERATE_SUPERSET:
   !op. monoidal op
        ==> !f:'a->'b u v.
            u SUBSET v /\
            (!x. x IN v /\ ~(x IN u) ==> (f(x) = neutral op))
            ==> (iterate op v f = iterate op u f)
Proof
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM ITERATE_SUPPORT] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC std_ss [support, EXTENSION, GSPECIFICATION] THEN
  ASM_MESON_TAC[SUBSET_DEF]
QED

Theorem ITERATE_IMAGE_NONZERO:
   !op. monoidal op
        ==> !g:'b->'c f:'a->'b s.
                    FINITE s /\
                    (!x y. x IN s /\ y IN s /\ ~(x = y) /\ (f x = f y)
                           ==> (g(f x) = neutral op))
                    ==> (iterate op (IMAGE f s) g = iterate op s (g o f))
Proof
  GEN_TAC THEN DISCH_TAC THEN
  GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] THEN GEN_TAC THEN
  KNOW_TAC `` ((!(x :'a) (y :'a).
       x IN s /\ y IN s /\ x <> y /\ ((f :'a -> 'b) x = f y) ==>
       ((g :'b -> 'c) (f x) = neutral (op :'c -> 'c -> 'c))) ==>
    (iterate op (IMAGE f s) g = iterate op s (g o f))) = (\s. (!(x :'a) (y :'a).
       x IN s /\ y IN s /\ x <> y /\ ((f :'a -> 'b) x = f y) ==>
       ((g :'b -> 'c) (f x) = neutral (op :'c -> 'c -> 'c))) ==>
    (iterate op (IMAGE f s) g = iterate op s (g o f))) s`` THENL
  [FULL_SIMP_TAC std_ss [], DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  ASM_SIMP_TAC std_ss [IMAGE_EMPTY, IMAGE_INSERT, ITERATE_CLAUSES, IMAGE_FINITE]
  THEN SIMP_TAC std_ss [GSYM RIGHT_FORALL_IMP_THM] THEN
  MAP_EVERY X_GEN_TAC [``s':'a->bool``,``a:'a``] THEN
  REWRITE_TAC[IN_INSERT] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN ``iterate op s' ((g:'b->'c) o (f:'a->'b)) = iterate op (IMAGE f s') g``
  SUBST1_TAC THENL [ASM_MESON_TAC[], ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN ``(g:'b->'c) ((f:'a->'b) a) = neutral op`` SUBST1_TAC THEN
  ASM_MESON_TAC[MONOIDAL_AC]]
QED

val lemma = prove (
  ``!s. DISJOINT {x | x IN s /\ P x} {x | x IN s /\ ~P x}``,
  GEN_TAC THEN SIMP_TAC std_ss [DISJOINT_DEF, INTER_DEF, EXTENSION, GSPECIFICATION]
  THEN GEN_TAC THEN EQ_TAC THENL
  [RW_TAC std_ss [], RW_TAC std_ss [NOT_IN_EMPTY]]);

Theorem ITERATE_CASES:
    !op. monoidal op
        ==> !s P f g:'a->'b.
                FINITE s
                ==> (iterate op s (\x. if P x then f x else g x) =
                    op (iterate op {x | x IN s /\ P x} f)
                       (iterate op {x | x IN s /\ ~P x} g))
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   ``op (iterate op {x | x IN s /\ P x} (\x. if P x then f x else (g:'a->'b) x))
       (iterate op {x | x IN s /\ ~P x} (\x. if P x then f x else g x))`` THEN
  CONJ_TAC THENL [KNOW_TAC ``FINITE {(x:'a) | x IN s /\ P x} /\
  FINITE {x | x IN s /\ ~P x} /\ DISJOINT {x | x IN s /\ P x} {x | x IN s /\ ~P x}``
  THENL [FULL_SIMP_TAC std_ss [FINITE_RESTRICT, lemma], STRIP_TAC THEN
  FULL_SIMP_TAC std_ss [GSYM ITERATE_UNION] THEN AP_THM_TAC THEN AP_TERM_TAC
  THEN FULL_SIMP_TAC std_ss [UNION_DEF, EXTENSION, GSPECIFICATION] THEN METIS_TAC []],
  BINOP_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_EQ) THEN
    SIMP_TAC std_ss [GSPECIFICATION]]
QED

Theorem ITERATE_OP_GEN:
   !op. monoidal op
        ==> !f g:'a->'b s.
                FINITE(support op f s) /\ FINITE(support op g s)
                ==> (iterate op s (\x. op (f x) (g x)) =
                    op (iterate op s f) (iterate op s g))
Proof
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM ITERATE_SUPPORT] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC ``iterate op (support op f s UNION support op g s)
                         (\x. op ((f:'a->'b) x) (g x))`` THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV,
    ASM_SIMP_TAC std_ss [ITERATE_OP, FINITE_UNION] THEN BINOP_TAC] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_SUPERSET) THEN
  SIMP_TAC std_ss [support, GSPECIFICATION, SUBSET_DEF, IN_UNION] THEN
  ASM_MESON_TAC[monoidal]
QED

Theorem ITERATE_CLAUSES_NUMSEG:
    !op. monoidal op
        ==> (!m. iterate op {m..0} f = if m = 0 then f(0) else neutral op) /\
            (!m n. iterate op {m..SUC n} f =
                      if m <= SUC n then op (iterate op {m..n} f) (f(SUC n))
                      else iterate op {m..n} f)
Proof
  REWRITE_TAC[NUMSEG_CLAUSES] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC std_ss [ITERATE_CLAUSES, FINITE_NUMSEG, IN_NUMSEG, FINITE_EMPTY] THEN
  REWRITE_TAC[ARITH_PROVE ``~(SUC n <= n)``, NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[monoidal]
QED

Theorem ITERATE_PAIR:
    !op. monoidal op
        ==> !f m n. iterate op {2*m..2*n+1} f =
                    iterate op {m..n} (\i. op (f(2*i)) (f(2*i+1)))
Proof
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN GEN_TAC THEN
  INDUCT_TAC THEN CONV_TAC REDUCE_CONV THENL
   [REWRITE_TAC [ONE] THEN ASM_SIMP_TAC std_ss [ITERATE_CLAUSES_NUMSEG] THEN
    REWRITE_TAC [ONE] THEN
    REWRITE_TAC[ARITH_PROVE ``2 * m <= SUC 0 <=> (m = 0)``] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[MULT_EQ_0],
    REWRITE_TAC[ARITH_PROVE ``2 * SUC n + 1 = SUC(SUC(2 * n + 1))``] THEN
    ASM_SIMP_TAC std_ss [ITERATE_CLAUSES_NUMSEG] THEN
    REWRITE_TAC[ARITH_PROVE ``2 * m <= SUC(SUC(2 * n + 1)) <=> m <= SUC n``,
                ARITH_PROVE ``2 * m <= SUC(2 * n + 1) <=> m <= SUC n``] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_PROVE ``2 * SUC n = SUC(2 * n + 1)``,
                ARITH_PROVE ``2 * SUC n + 1 = SUC(SUC(2 * n + 1))``] THEN
    ASM_MESON_TAC[monoidal]]
QED

(* ------------------------------------------------------------------------- *)
(* Sums of natural numbers.                                                  *)
(* ------------------------------------------------------------------------- *)

Definition nsum :
   (nsum :('a->bool)->('a->num)->num) = iterate (+)
End

Theorem NEUTRAL_ADD:
    neutral((+):num->num->num) = 0
Proof
  REWRITE_TAC[neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  MESON_TAC[ADD_CLAUSES]
QED

Theorem NEUTRAL_MUL:
    neutral(( * ):num->num->num) = 1
Proof
  REWRITE_TAC[neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  MESON_TAC[MULT_CLAUSES, MULT_EQ_1]
QED

Theorem MONOIDAL_ADD:
    monoidal((+):num->num->num)
Proof
  REWRITE_TAC[monoidal, NEUTRAL_ADD] THEN ARITH_TAC
QED

Theorem MONOIDAL_MUL:
   monoidal(( * ):num->num->num)
Proof
  REWRITE_TAC[monoidal, NEUTRAL_MUL] THEN ARITH_TAC
QED

Theorem NSUM_DEGENERATE:
   !f s. ~(FINITE {x | x IN s /\ ~(f x = 0:num)}) ==> (nsum s f = 0:num)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[nsum] THEN
  SIMP_TAC std_ss [iterate, support, NEUTRAL_ADD]
QED

Theorem NSUM_CLAUSES:
   (!f. nsum {} f = 0) /\
   (!x f s. FINITE(s)
            ==> (nsum (x INSERT s) f =
                 if x IN s then nsum s f else f(x) + nsum s f))
Proof
  REWRITE_TAC[nsum, GSYM NEUTRAL_ADD] THEN
  KNOW_TAC ``monoidal ((+):num->num->num)`` THENL [REWRITE_TAC[MONOIDAL_ADD],
  METIS_TAC [ITERATE_CLAUSES]]
QED

Theorem NSUM_UNION:
   !f s t. FINITE s /\ FINITE t /\ DISJOINT s t
           ==> (nsum (s UNION t) f = nsum s f + nsum t f)
Proof
  SIMP_TAC std_ss [nsum, ITERATE_UNION, MONOIDAL_ADD]
QED

Theorem NSUM_DIFF:
   !f s t. FINITE s /\ t SUBSET s
           ==> (nsum (s DIFF t) f = nsum s f - nsum t f)
Proof
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ARITH_PROVE ``(x + z = y:num) ==> (x = y - z)``) THEN
  ASM_SIMP_TAC std_ss [nsum, ITERATE_DIFF, MONOIDAL_ADD]
QED

Theorem NSUM_INCL_EXCL:
   !s t (f:'a->num).
     FINITE s /\ FINITE t
     ==> (nsum s f + nsum t f = nsum (s UNION t) f + nsum (s INTER t) f)
Proof
  REWRITE_TAC[nsum, GSYM NEUTRAL_ADD] THEN
  MATCH_MP_TAC ITERATE_INCL_EXCL THEN REWRITE_TAC[MONOIDAL_ADD]
QED

Theorem NSUM_SUPPORT:
   !f s. nsum (support (+) f s) f = nsum s f
Proof
  SIMP_TAC std_ss [nsum, iterate, SUPPORT_SUPPORT]
QED

Theorem NSUM_ADD:
   !f g s. FINITE s ==> (nsum s (\x. f(x) + g(x)) = nsum s f + nsum s g)
Proof
  SIMP_TAC std_ss [nsum, ITERATE_OP, MONOIDAL_ADD]
QED

Theorem NSUM_ADD_GEN:
   !f g s.
       FINITE {x | x IN s /\ ~(f x = 0)} /\ FINITE {x | x IN s /\ ~(g x = 0:num)}
       ==> (nsum s (\x. f x + g x) = nsum s f + nsum s g)
Proof
  REWRITE_TAC[GSYM NEUTRAL_ADD, GSYM support, nsum] THEN
  MATCH_MP_TAC ITERATE_OP_GEN THEN ACCEPT_TAC MONOIDAL_ADD
QED

Theorem NSUM_EQ_0:
   !f s. (!x:'a. x IN s ==> (f(x) = 0:num)) ==> (nsum s f = 0:num)
Proof
  REWRITE_TAC[nsum, GSYM NEUTRAL_ADD] THEN
  SIMP_TAC std_ss [ITERATE_EQ_NEUTRAL, MONOIDAL_ADD]
QED

Theorem NSUM_0:
   !s:'a->bool. nsum s (\n. 0:num) = 0:num
Proof
  SIMP_TAC std_ss [NSUM_EQ_0]
QED

Theorem NSUM_LMUL:
   !f c s:'a->bool. nsum s (\x. c * f(x)) = c * nsum s f
Proof
  REPEAT GEN_TAC THEN ASM_CASES_TAC ``c = 0:num`` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES, NSUM_0] THEN REWRITE_TAC[nsum] THEN
  ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN
  SUBGOAL_THEN ``support (+) (\x:'a. (c:num) * f(x)) s = support (+) f s`` SUBST1_TAC
  THENL [ASM_SIMP_TAC std_ss [support, MULT_EQ_0, NEUTRAL_ADD], ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[NEUTRAL_ADD, MULT_CLAUSES] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(``support (+) f (s:'a->bool)``,``t:'a->bool``) THEN
  REWRITE_TAC[GSYM nsum] THEN Q.ABBREV_TAC `ss = support $+ f s` THEN
  KNOW_TAC ``((nsum ss (\x. c * f x) = c * nsum ss f) =
        (\ss. (nsum ss (\x. c * f x) = c * nsum ss f)) ss)`` THENL
  [FULL_SIMP_TAC  std_ss [], ALL_TAC] THEN DISCH_TAC THEN
  ONCE_ASM_REWRITE_TAC [] THEN HO_MATCH_MP_TAC FINITE_INDUCT THEN
  BETA_TAC THEN SIMP_TAC std_ss [NSUM_CLAUSES, MULT_CLAUSES, LEFT_ADD_DISTRIB]
QED

Theorem NSUM_RMUL:
   !f c s:'a->bool. nsum s (\x. f(x) * c) = nsum s f * c
Proof
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[NSUM_LMUL]
QED

Theorem NSUM_LE:
   !f g s. FINITE(s) /\ (!x. x IN s ==> f(x) <= g(x))
           ==> nsum s f <= nsum s g
Proof
  ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] THEN REPEAT GEN_TAC THEN
  KNOW_TAC ``((!x. x IN s ==> f x <= g x) ==> nsum s f <= nsum s g) =
         (\s. (!x. x IN s ==> f x <= g x) ==> nsum s f <= nsum s g) s`` THENL
  [FULL_SIMP_TAC std_ss [], ALL_TAC] THEN DISCH_TAC THEN ONCE_ASM_REWRITE_TAC []
  THEN MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC std_ss [NSUM_CLAUSES, LESS_EQ_REFL, LESS_EQ_LESS_EQ_MONO, IN_INSERT]
QED

Theorem NSUM_LT:
   !f g s:'a->bool.
        FINITE(s) /\ (!x. x IN s ==> f(x) <= g(x)) /\
        (?x. x IN s /\ f(x) < g(x))
         ==> nsum s f < nsum s g
Proof
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN ``a:'a`` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN ``s = (a:'a) INSERT (s DELETE a)`` SUBST1_TAC THENL
   [UNDISCH_TAC ``a:'a IN s`` THEN SET_TAC[], ALL_TAC] THEN
  ASM_SIMP_TAC std_ss [NSUM_CLAUSES, FINITE_DELETE, IN_DELETE] THEN
  ASM_SIMP_TAC std_ss [ARITH_PROVE ``m < p /\ n <= q ==> m + n < p + q:num``,
  NSUM_LE, IN_DELETE, FINITE_DELETE]
QED

Theorem NSUM_LT_ALL:
   !f g s. FINITE s /\ ~(s = {}) /\ (!x. x IN s ==> f(x) < g(x))
           ==> nsum s f < nsum s g
Proof
  MESON_TAC[MEMBER_NOT_EMPTY, LESS_IMP_LESS_OR_EQ, NSUM_LT]
QED

Theorem NSUM_EQ:
   !f g s. (!x. x IN s ==> (f x = g x)) ==> (nsum s f = nsum s g)
Proof
  REWRITE_TAC[nsum] THEN
  MATCH_MP_TAC ITERATE_EQ THEN REWRITE_TAC[MONOIDAL_ADD]
QED

Theorem NSUM_CONST:
   !c s. FINITE s ==> (nsum s (\n. c) = (CARD s) * c)
Proof
  REPEAT GEN_TAC THEN KNOW_TAC ``(nsum s (\n. c) = CARD s * c) =
                            (\s. (nsum s (\n. c) = CARD s * c)) s ``
  THENL [FULL_SIMP_TAC std_ss [], ALL_TAC] THEN DISCH_TAC THEN
  ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC FINITE_INDUCT THEN
  BETA_TAC THEN SIMP_TAC std_ss [NSUM_CLAUSES, CARD_DEF] THEN
  REPEAT STRIP_TAC THEN SIMP_TAC std_ss [ADD1, RIGHT_ADD_DISTRIB]
  THEN ARITH_TAC
QED

Theorem NSUM_POS_BOUND:
   !f b s. FINITE s /\ nsum s f <= b ==> !x:'a. x IN s ==> f x <= b
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM AND_IMP_INTRO] THEN
  KNOW_TAC ``(nsum s f <= b ==> !x. x IN s ==> f x <= b) =
         (\s. nsum s f <= b ==> !x. x IN s ==> f x <= b) s`` THENL
  [FULL_SIMP_TAC std_ss [], ALL_TAC] THEN DISCH_TAC THEN
  ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC FINITE_INDUCT THEN
  BETA_TAC THEN SIMP_TAC std_ss [NSUM_CLAUSES, NOT_IN_EMPTY, IN_INSERT]
  THEN MESON_TAC[ZERO_LESS_EQ, ARITH_PROVE
   ``0:num <= x /\ 0:num <= y /\ x + y <= b ==> x <= b /\ y <= b``]
QED

Theorem NSUM_EQ_0_IFF:
   !s. FINITE s ==> ((nsum s f = 0:num) <=> !x. x IN s ==> (f x = 0:num))
Proof
  REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC std_ss [NSUM_EQ_0] THEN
  ASM_MESON_TAC[LESS_EQ_0, NSUM_POS_BOUND]
QED

Theorem NSUM_POS_LT:
   !f s:'a->bool.
        FINITE s /\ (?x. x IN s /\ 0:num < f x)
        ==> 0:num < nsum s f
Proof
  SIMP_TAC std_ss [ARITH_PROVE ``0:num < n <=> ~(n = 0:num)``, NSUM_EQ_0_IFF]
  THEN MESON_TAC[]
QED

Theorem NSUM_POS_LT_ALL:
   !s f:'a->num.
     FINITE s /\ ~(s = {}) /\ (!i. i IN s ==> 0:num < f i) ==> 0:num < nsum s f
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NSUM_POS_LT THEN
  ASM_MESON_TAC[MEMBER_NOT_EMPTY]
QED

Theorem NSUM_DELETE:
   !f s a. FINITE s /\ a IN s ==> (f(a) + nsum(s DELETE a) f = nsum s f)
Proof
  SIMP_TAC std_ss [nsum, ITERATE_DELETE, MONOIDAL_ADD]
QED

Theorem NSUM_SING:
   !f x. nsum {x} f = f(x)
Proof
  SIMP_TAC std_ss [NSUM_CLAUSES, FINITE_EMPTY, FINITE_INSERT,
  NOT_IN_EMPTY, ADD_CLAUSES]
QED

Theorem NSUM_DELTA:
   !s a. nsum s (\x. if x = a:'a then b else 0:num) = if a IN s then b else 0:num
Proof
  REWRITE_TAC[nsum, GSYM NEUTRAL_ADD] THEN
  SIMP_TAC std_ss [ITERATE_DELTA, MONOIDAL_ADD]
QED

Theorem NSUM_SWAP:
   !f:'a->'b->num s t.
      FINITE(s) /\ FINITE(t)
      ==> (nsum s (\i. nsum t (f i)) = nsum t (\j. nsum s (\i. f i j)))
Proof
  GEN_TAC THEN SIMP_TAC std_ss [GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN KNOW_TAC ``( !t. FINITE t ==>
        (nsum s (\i. nsum t (f i)) = nsum t (\j. nsum s (\i. (f:'a->'b->num) i j)))) =
                      (\s.  !t. FINITE t ==>
        (nsum s (\i. nsum t (f i)) = nsum t (\j. nsum s (\i. (f:'a->'b->num) i j)))) s`` THENL
  [FULL_SIMP_TAC std_ss [], ALL_TAC] THEN DISCH_TAC THEN ONCE_ASM_REWRITE_TAC []
  THEN MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC std_ss [NSUM_CLAUSES, NSUM_0, NSUM_ADD, ETA_AX] THEN METIS_TAC []
QED

Theorem NSUM_IMAGE:
   !f g s. (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
           ==> (nsum (IMAGE f s) g = nsum s (g o f))
Proof
  REWRITE_TAC[nsum, GSYM NEUTRAL_ADD] THEN
  MATCH_MP_TAC ITERATE_IMAGE THEN REWRITE_TAC[MONOIDAL_ADD]
QED

Theorem NSUM_SUPERSET:
   !f:'a->num u v.
        u SUBSET v /\ (!x. x IN v /\ ~(x IN u) ==> (f(x) = 0:num))
        ==> (nsum v f = nsum u f)
Proof
  SIMP_TAC std_ss [nsum, GSYM NEUTRAL_ADD, ITERATE_SUPERSET, MONOIDAL_ADD]
QED

Theorem NSUM_UNION_RZERO:
   !f:'a->num u v.
        FINITE u /\ (!x. x IN v /\ ~(x IN u) ==> (f(x) = 0:num))
        ==> (nsum (u UNION v) f = nsum u f)
Proof
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [SET_RULE ``u UNION v = u UNION (v DIFF u)``] THEN
  MATCH_MP_TAC NSUM_SUPERSET THEN ASM_MESON_TAC[IN_UNION, IN_DIFF, SUBSET_DEF]
QED

Theorem NSUM_UNION_LZERO:
   !f:'a->num u v.
        FINITE v /\ (!x. x IN u /\ ~(x IN v) ==> (f(x) = 0:num))
        ==> (nsum (u UNION v) f = nsum v f)
Proof
  MESON_TAC[NSUM_UNION_RZERO, UNION_COMM]
QED

Theorem NSUM_RESTRICT:
   !f s. FINITE s ==> (nsum s (\x. if x IN s then f(x) else 0:num) = nsum s f)
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NSUM_EQ THEN ASM_SIMP_TAC std_ss []
QED

Theorem NSUM_BOUND:
   !s f b. FINITE s /\ (!x:'a. x IN s ==> f(x) <= b)
           ==> nsum s f <= (CARD s) * b
Proof
  SIMP_TAC std_ss [GSYM NSUM_CONST, NSUM_LE]
QED

Theorem NSUM_BOUND_GEN:
   !s f b. FINITE s /\ ~(s = {}) /\ (!x:'a. x IN s ==> f(x) <= b DIV (CARD s))
           ==> nsum s f <= b
Proof
  REPEAT STRIP_TAC THEN KNOW_TAC ``0 < CARD s`` THENL
  [METIS_TAC [CARD_EQ_0, NOT_ZERO_LT_ZERO], ALL_TAC] THEN
  STRIP_TAC THEN FULL_SIMP_TAC std_ss [X_LE_DIV] THEN
  SUBGOAL_THEN ``nsum s (\x. CARD(s:'a->bool) * f x) <= CARD s * b`` MP_TAC THENL
   [ASM_SIMP_TAC arith_ss [NSUM_BOUND],
    ASM_SIMP_TAC std_ss [NSUM_LMUL, LE_MULT_LCANCEL, CARD_EQ_0]]
QED

Theorem NSUM_BOUND_LT:
   !s f b. FINITE s /\ (!x:'a. x IN s ==> f x <= b) /\ (?x. x IN s /\ f x < b)
           ==> nsum s f < (CARD s) * b
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LESS_LESS_EQ_TRANS THEN
  EXISTS_TAC ``nsum s (\x:'a. b)`` THEN CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_LT THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[],
    ASM_SIMP_TAC std_ss [NSUM_CONST, LESS_EQ_REFL]]
QED

Theorem NSUM_BOUND_LT_ALL:
   !s f b. FINITE s /\ ~(s = {}) /\ (!x. x IN s ==> f(x) < b)
           ==> nsum s f <  (CARD s) * b
Proof
  MESON_TAC[MEMBER_NOT_EMPTY, LESS_IMP_LESS_OR_EQ, NSUM_BOUND_LT]
QED

Theorem NSUM_BOUND_LT_GEN:
   !s f b. FINITE s /\ ~(s = {}) /\ (!x:'a. x IN s ==> f(x) < b DIV (CARD s))
           ==> nsum s f < b
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LESS_LESS_EQ_TRANS THEN
  EXISTS_TAC ``nsum (s:'a->bool) (\a. f(a) + 1:num)`` THEN CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_LT_ALL THEN ASM_SIMP_TAC std_ss [] THEN ARITH_TAC,
    MATCH_MP_TAC NSUM_BOUND_GEN THEN
    ASM_SIMP_TAC std_ss [ARITH_PROVE ``a + 1:num <= b <=> a < b``]]
QED

Theorem NSUM_UNION_EQ:
   !s t u. FINITE u /\ (s INTER t = {}) /\ (s UNION t = u)
           ==> (nsum s f + nsum t f = nsum u f)
Proof
  MESON_TAC[NSUM_UNION, DISJOINT_DEF, SUBSET_FINITE, SUBSET_UNION]
QED

Theorem NSUM_EQ_SUPERSET:
   !f s t:'a->bool.
        FINITE t /\ t SUBSET s /\
        (!x. x IN t ==> (f x = g x)) /\
        (!x. x IN s /\ ~(x IN t) ==> (f(x) = 0:num))
        ==> (nsum s f = nsum t g)
Proof
  MESON_TAC[NSUM_SUPERSET, NSUM_EQ]
QED

Theorem NSUM_RESTRICT_SET:
   !P s f. nsum {x:'a | x IN s /\ P x} f = nsum s (\x. if P x then f(x) else 0:num)
Proof
  ONCE_REWRITE_TAC[GSYM NSUM_SUPPORT] THEN
  SIMP_TAC std_ss [support, NEUTRAL_ADD, GSPECIFICATION] THEN
  REWRITE_TAC[METIS []``~((if P x then f x else a) = a) <=> P x /\ ~(f x = a)``,
              GSYM CONJ_ASSOC] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC NSUM_EQ THEN SIMP_TAC std_ss [GSPECIFICATION]
QED

Theorem NSUM_NSUM_RESTRICT:
   !R f s t.
        FINITE s /\ FINITE t
        ==> (nsum s (\x. nsum {y | y IN t /\ R x y} (\y. f x y)) =
             nsum t (\y. nsum {x | x IN s /\ R x y} (\x. f x y)))
Proof
  REPEAT GEN_TAC THEN SIMP_TAC std_ss [NSUM_RESTRICT_SET] THEN
  ASSUME_TAC NSUM_SWAP THEN POP_ASSUM (MP_TAC o Q.SPECL
  [`(\x y. if R x y then f x y else 0)`,`s`, `t`]) THEN
  FULL_SIMP_TAC std_ss []
QED

Theorem CARD_EQ_NSUM:
   !s. FINITE s ==> ((CARD s) = nsum s (\x. 1:num))
Proof
  SIMP_TAC std_ss [NSUM_CONST, MULT_CLAUSES]
QED

Theorem NSUM_MULTICOUNT_GEN:
   !R:'a->'b->bool s t k.
        FINITE s /\ FINITE t /\
        (!j. j IN t ==> (CARD {i | i IN s /\ R i j} = k(j)))
        ==> (nsum s (\i. (CARD {j | j IN t /\ R i j})) =
             nsum t (\i. (k i)))
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC ``nsum s (\i:'a. nsum {j:'b | j IN t /\ R i j} (\j. 1:num))`` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC std_ss [CARD_EQ_NSUM, FINITE_RESTRICT],
    ASSUME_TAC NSUM_NSUM_RESTRICT THEN POP_ASSUM (MP_TAC o Q.SPEC `R`)
    THEN FULL_SIMP_TAC std_ss [] THEN DISCH_TAC THEN MATCH_MP_TAC NSUM_EQ
    THEN ASM_SIMP_TAC std_ss [NSUM_CONST, FINITE_RESTRICT] THEN
    REWRITE_TAC[MULT_CLAUSES]]
QED

Theorem NSUM_MULTICOUNT:
   !R:'a->'b->bool s t k.
        FINITE s /\ FINITE t /\
        (!j. j IN t ==> (CARD {i | i IN s /\ R i j} = k))
        ==> (nsum s (\i. (CARD {j | j IN t /\ R i j})) = (k * CARD t))
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC ``nsum t (\i:'b. k)`` THEN CONJ_TAC THENL
  [KNOW_TAC ``?j. !i:'b. &k = &(j i):num`` THENL
  [EXISTS_TAC ``(\i:'b. k:num)`` THEN METIS_TAC [], ALL_TAC] THEN
   STRIP_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC NSUM_MULTICOUNT_GEN THEN FULL_SIMP_TAC std_ss [],
   ASM_SIMP_TAC std_ss [NSUM_CONST] THEN ARITH_TAC]
QED

Theorem NSUM_IMAGE_GEN:
   !f:'a->'b g s.
        FINITE s
        ==> (nsum s g =
             nsum (IMAGE f s) (\y. nsum {x | x IN s /\ (f(x) = y)} g))
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   ``nsum s (\x:'a. nsum {y:'b | y IN IMAGE f s /\ (f x = y)} (\y. g x))`` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC ``x:'a`` THEN
    DISCH_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN ``{y | y IN IMAGE (f:'a->'b) s /\ (f x = y)} = {(f x)}``
     (fn th => REWRITE_TAC[th, NSUM_SING, o_THM]) THEN
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_SING, IN_IMAGE] THEN
    ASM_MESON_TAC[],
    GEN_REWR_TAC (funpow 2 RAND_CONV o ABS_CONV o RAND_CONV)
     [GSYM ETA_AX] THEN KNOW_TAC ``FINITE (IMAGE (f:'a->'b) s)`` THENL
    [METIS_TAC [IMAGE_FINITE], ALL_TAC] THEN DISCH_TAC THEN
    ASSUME_TAC NSUM_NSUM_RESTRICT THEN
    POP_ASSUM (MP_TAC o Q.SPEC `(\x y. f x = y)`) THEN
    FULL_SIMP_TAC std_ss []]
QED

Theorem NSUM_GROUP:
   !f:'a->'b g s t.
        FINITE s /\ IMAGE f s SUBSET t
        ==> (nsum t (\y. nsum {x | x IN s /\ (f(x) = y)} g) = nsum s g)
Proof
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [``f:'a->'b``, ``g:'a->num``, ``s:'a->bool``] NSUM_IMAGE_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC NSUM_SUPERSET THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC NSUM_EQ_0 THEN
  FULL_SIMP_TAC std_ss [GSPECIFICATION, IN_IMAGE] THEN METIS_TAC []
QED

Theorem NSUM_SUBSET:
   !u v f. FINITE u /\ FINITE v /\ (!x:'a. x IN (u DIFF v) ==> (f(x) = 0:num))
           ==> nsum u f <= nsum v f
Proof
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [``f:'a->num``, ``u INTER v :'a->bool``] NSUM_UNION) THEN
  DISCH_THEN(fn th => MP_TAC(SPEC ``v DIFF u :'a->bool`` th) THEN
                      MP_TAC(SPEC ``u DIFF v :'a->bool`` th)) THEN
  REWRITE_TAC[SET_RULE ``(u INTER v) UNION (u DIFF v) = u``,
              SET_RULE ``(u INTER v) UNION (v DIFF u) = v``] THEN
  ASM_SIMP_TAC std_ss [FINITE_DIFF, FINITE_INTER] THEN
  KNOW_TAC ``DISJOINT (u INTER v) (u DIFF v) /\ DISJOINT (u INTER v) (v DIFF u)``
  THENL [SET_TAC[], ALL_TAC] THEN RW_TAC std_ss [] THEN
  ASM_SIMP_TAC std_ss [NSUM_EQ_0]
QED

Theorem NSUM_SUBSET_SIMPLE:
   !u v f. FINITE v /\ u SUBSET v ==> nsum u f <= nsum v f
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NSUM_SUBSET THEN
  ASM_MESON_TAC[IN_DIFF, SUBSET_DEF, SUBSET_FINITE]
QED

Theorem NSUM_LE_GEN:
   !f g s. (!x:'a. x IN s ==> f x <= g x) /\ FINITE {x | x IN s /\ ~(g x = 0:num)}
           ==> nsum s f <= nsum s g
Proof
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM NSUM_SUPPORT] THEN
  REWRITE_TAC[support, NEUTRAL_ADD] THEN
  MATCH_MP_TAC LESS_EQ_TRANS THEN
  EXISTS_TAC ``nsum {x | x IN s /\ ~(g(x:'a) = 0:num)} f`` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_SUBSET THEN
    ASM_SIMP_TAC std_ss [GSPECIFICATION, IN_DIFF] THEN
    CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC[LE]] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO]
      SUBSET_FINITE)) THEN
    SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN ASM_MESON_TAC[LE],
    MATCH_MP_TAC NSUM_LE THEN ASM_SIMP_TAC std_ss [GSPECIFICATION]]
QED

Theorem NSUM_IMAGE_NONZERO:
   !d:'b->num i:'a->'b s.
    FINITE s /\
    (!x y. x IN s /\ y IN s /\ ~(x = y) /\ (i x = i y) ==> (d(i x) = 0:num))
    ==> (nsum (IMAGE i s) d = nsum s (d o i))
Proof
  REWRITE_TAC[GSYM NEUTRAL_ADD, nsum] THEN
  MATCH_MP_TAC ITERATE_IMAGE_NONZERO THEN REWRITE_TAC[MONOIDAL_ADD]
QED

Theorem NSUM_BIJECTION:
   !f p s:'a->bool.
                (!x. x IN s ==> p(x) IN s) /\
                (!y. y IN s ==> ?!x. x IN s /\ (p(x) = y))
                ==> (nsum s f = nsum s (f o p))
Proof
  REWRITE_TAC[nsum] THEN MATCH_MP_TAC ITERATE_BIJECTION THEN
  REWRITE_TAC[MONOIDAL_ADD]
QED

Theorem NSUM_NSUM_PRODUCT:
   !s:'a->bool t:'a->'b->bool x.
        FINITE s /\ (!i. i IN s ==> FINITE(t i))
        ==> (nsum s (\i. nsum (t i) (x i)) =
             nsum {i,j | i IN s /\ j IN t i} (\(i,j). x i j))
Proof
  REWRITE_TAC[nsum] THEN MATCH_MP_TAC ITERATE_ITERATE_PRODUCT THEN
  REWRITE_TAC[MONOIDAL_ADD]
QED

Theorem NSUM_EQ_GENERAL:
   !s:'a->bool t:'b->bool f g h.
        (!y. y IN t ==> ?!x. x IN s /\ (h(x) = y)) /\
        (!x. x IN s ==> h(x) IN t /\ (g(h x) = f x))
        ==> (nsum s f = nsum t g)
Proof
  REWRITE_TAC[nsum] THEN MATCH_MP_TAC ITERATE_EQ_GENERAL THEN
  REWRITE_TAC[MONOIDAL_ADD]
QED

Theorem NSUM_EQ_GENERAL_INVERSES:
   !s:'a->bool t:'b->bool f g h k.
        (!y. y IN t ==> k(y) IN s /\ (h(k y) = y)) /\
        (!x. x IN s ==> h(x) IN t /\ (k(h x) = x) /\ (g(h x) = f x))
        ==> (nsum s f = nsum t g)
Proof
  REWRITE_TAC[nsum] THEN MATCH_MP_TAC ITERATE_EQ_GENERAL_INVERSES THEN
  REWRITE_TAC[MONOIDAL_ADD]
QED

Theorem NSUM_INJECTION:
   !f p s. FINITE s /\
           (!x. x IN s ==> p x IN s) /\
           (!x y. x IN s /\ y IN s /\ (p x = p y) ==> (x = y))
           ==> (nsum s (f o p) = nsum s f)
Proof
  REWRITE_TAC[nsum] THEN MATCH_MP_TAC ITERATE_INJECTION THEN
  REWRITE_TAC[MONOIDAL_ADD]
QED

Theorem NSUM_UNION_NONZERO:
   !f s t. FINITE s /\ FINITE t /\ (!x. x IN s INTER t ==> (f(x) = 0:num))
           ==> (nsum (s UNION t) f = nsum s f + nsum t f)
Proof
  REWRITE_TAC[nsum, GSYM NEUTRAL_ADD] THEN
  MATCH_MP_TAC ITERATE_UNION_NONZERO THEN REWRITE_TAC[MONOIDAL_ADD]
QED

Theorem NSUM_BIGUNION_NONZERO:
   !f s. FINITE s /\ (!t:'a->bool. t IN s ==> FINITE t) /\
         (!t1 t2 x. t1 IN s /\ t2 IN s /\ ~(t1 = t2) /\ x IN t1 /\ x IN t2
                    ==> (f x = 0))
         ==> (nsum (BIGUNION s) f = nsum s (\t. nsum t f))
Proof
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] THEN GEN_TAC THEN
  KNOW_TAC ``((!(t:'a->bool). t IN s ==> FINITE t) /\
    (!t1 t2 x.
       t1 IN s /\ t2 IN s /\ t1 <> t2 /\ x IN t1 /\ x IN t2 ==>
       (f x = 0)) ==>
    (nsum (BIGUNION s) f = nsum s (\t. nsum t f))) =
    (\s. (!(t:'a->bool). t IN s ==> FINITE t) /\
    (!t1 t2 x.
       t1 IN s /\ t2 IN s /\ t1 <> t2 /\ x IN t1 /\ x IN t2 ==>
       (f x = 0)) ==>
    (nsum (BIGUNION s) f = nsum s (\t. nsum t f))) s `` THENL
  [FULL_SIMP_TAC std_ss [], ALL_TAC] THEN DISCH_TAC THEN
  ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  REWRITE_TAC[BIGUNION_EMPTY, BIGUNION_INSERT, NSUM_CLAUSES, IN_INSERT] THEN
  SIMP_TAC std_ss [GSYM RIGHT_FORALL_IMP_THM] THEN
  MAP_EVERY X_GEN_TAC [``(s':('a->bool)->bool)``, ``t:'a->bool``] THEN
  DISCH_THEN(fn th => STRIP_TAC THEN MP_TAC th) THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC ``FINITE (s':('a->bool)->bool)`` THEN
  UNDISCH_TAC ``(t :'a -> bool) NOTIN (s' :('a -> bool) -> bool) `` THEN
  ONCE_REWRITE_TAC[AND_IMP_INTRO] THEN ASM_SIMP_TAC std_ss [NSUM_CLAUSES]
  THEN KNOW_TAC ``nsum (BIGUNION s') f = nsum s' (\t. nsum t f)`` THENL
  [METIS_TAC [], ALL_TAC] THEN GEN_REWR_TAC (LAND_CONV) [EQ_SYM_EQ]
  THEN DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN MATCH_MP_TAC NSUM_UNION_NONZERO THEN
  ASM_SIMP_TAC std_ss [FINITE_BIGUNION, IN_INTER, IN_BIGUNION] THEN
  ASM_MESON_TAC[]
QED

Theorem NSUM_CASES:
   !s P f g. FINITE s
             ==> (nsum s (\x:'a. if P x then f x else g x) =
                  nsum {x | x IN s /\ P x} f + nsum {x | x IN s /\ ~P x} g)
Proof
  REWRITE_TAC[nsum, GSYM NEUTRAL_ADD] THEN
  MATCH_MP_TAC ITERATE_CASES THEN REWRITE_TAC[MONOIDAL_ADD]
QED

Theorem NSUM_CLOSED:
   !P f:'a->num s.
        P(0) /\ (!x y. P x /\ P y ==> P(x + y)) /\ (!a. a IN s ==> P(f a))
        ==> P(nsum s f)
Proof
  REPEAT STRIP_TAC THEN MP_TAC(MATCH_MP ITERATE_CLOSED MONOIDAL_ADD) THEN
  DISCH_THEN(MP_TAC o SPEC ``P:num->bool``) THEN
  ASM_SIMP_TAC std_ss [NEUTRAL_ADD, GSYM nsum]
QED

Theorem NSUM_ADD_NUMSEG:
   !f g m n. nsum{m..n} (\i. f(i) + g(i)) = nsum{m..n} f + nsum{m..n} g
Proof
  SIMP_TAC std_ss [NSUM_ADD, FINITE_NUMSEG]
QED

Theorem NSUM_LE_NUMSEG:
   !f g m n. (!i. m <= i /\ i <= n ==> f(i) <= g(i))
             ==> nsum{m..n} f <= nsum{m..n} g
Proof
  SIMP_TAC std_ss [NSUM_LE, FINITE_NUMSEG, IN_NUMSEG]
QED

Theorem NSUM_EQ_NUMSEG:
   !f g m n. (!i. m <= i /\ i <= n ==> (f(i) = g(i)))
             ==> (nsum{m..n} f = nsum{m..n} g)
Proof
  MESON_TAC[NSUM_EQ, FINITE_NUMSEG, IN_NUMSEG]
QED

Theorem NSUM_CONST_NUMSEG:
   !c m n. nsum{m..n} (\n. c) = ((n + 1:num) - m) * c
Proof
  SIMP_TAC std_ss [NSUM_CONST, FINITE_NUMSEG, CARD_NUMSEG]
QED

Theorem NSUM_EQ_0_NUMSEG:
   !f m n. (!i. m <= i /\ i <= n ==> (f(i) = 0:num)) ==> (nsum{m..n} f = 0:num)
Proof
  SIMP_TAC std_ss [NSUM_EQ_0, IN_NUMSEG]
QED

Theorem NSUM_EQ_0_IFF_NUMSEG:
   !f m n. (nsum {m..n} f = 0:num) <=> !i. m <= i /\ i <= n ==> (f i = 0:num)
Proof
  SIMP_TAC std_ss [NSUM_EQ_0_IFF, FINITE_NUMSEG, IN_NUMSEG]
QED

Theorem NSUM_TRIV_NUMSEG:
   !f m n. n < m ==> (nsum{m..n} f = 0:num)
Proof
  MESON_TAC[NSUM_EQ_0_NUMSEG, LESS_EQ_TRANS, NOT_LESS]
QED

Theorem NSUM_SING_NUMSEG:
   !f n. nsum{n..n} f = f(n)
Proof
  SIMP_TAC std_ss [NSUM_SING, NUMSEG_SING]
QED

Theorem NSUM_CLAUSES_NUMSEG:
   (!m. nsum{m..0} f = if m = 0:num then f 0 else 0) /\
   (!m n. nsum{m..SUC n} f = if m <= SUC n then nsum{m..n} f + f(SUC n)
                             else nsum{m..n} f)
Proof
  MP_TAC(MATCH_MP ITERATE_CLAUSES_NUMSEG MONOIDAL_ADD) THEN
  REWRITE_TAC[NEUTRAL_ADD, nsum]
QED

Theorem NSUM_SWAP_NUMSEG:
   !a b c d f.
     nsum{a..b} (\i. nsum{c..d} (f i)) =
     nsum{c..d} (\j. nsum{a..b} (\i. f i j))
Proof
  REPEAT GEN_TAC THEN MATCH_MP_TAC NSUM_SWAP THEN REWRITE_TAC[FINITE_NUMSEG]
QED

Theorem NSUM_ADD_SPLIT:
   !f m n p.
        m <= n + 1:num ==> (nsum {m..n+p} f = nsum{m..n} f + nsum{n+1..n+p} f)
Proof
  METIS_TAC [NUMSEG_ADD_SPLIT, NSUM_UNION, DISJOINT_NUMSEG, FINITE_NUMSEG,
           ARITH_PROVE ``x:num < x + 1:num``]
QED

Theorem NSUM_OFFSET:
   !p f m n. nsum{m+p..n+p} f = nsum{m..n} (\i. f(i + p))
Proof
  SIMP_TAC std_ss [NUMSEG_OFFSET_IMAGE, NSUM_IMAGE, EQ_ADD_RCANCEL, FINITE_NUMSEG] THEN
  SIMP_TAC std_ss [o_DEF]
QED

Theorem NSUM_OFFSET_0:
   !f m n. m <= n ==> (nsum{m..n} f = nsum{0..n-m} (\i. f(i + m)))
Proof
  SIMP_TAC std_ss [GSYM NSUM_OFFSET, ADD_CLAUSES, SUB_ADD]
QED

Theorem NSUM_CLAUSES_LEFT:
   !f m n. m <= n ==> (nsum{m..n} f = f(m) + nsum{m+1..n} f)
Proof
  SIMP_TAC std_ss [GSYM NUMSEG_LREC, NSUM_CLAUSES, FINITE_NUMSEG, IN_NUMSEG] THEN
  ARITH_TAC
QED

Theorem NSUM_CLAUSES_RIGHT:
   !f m n. 0:num < n /\ m <= n ==> (nsum{m..n} f = nsum{m..n-1} f + f(n))
Proof
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  SIMP_TAC std_ss [LESS_REFL, NSUM_CLAUSES_NUMSEG, SUC_SUB1]
QED

Theorem NSUM_PAIR:
   !f m n. nsum{2*m..2*n+1} f = nsum{m..n} (\i. f(2*i) + f(2*i+1:num))
Proof
  MP_TAC(MATCH_MP ITERATE_PAIR MONOIDAL_ADD) THEN
  REWRITE_TAC[nsum, NEUTRAL_ADD]
QED

Theorem MOD_NSUM_MOD:
   !f:'a->num n s.
        FINITE s /\ ~(n = 0:num)
        ==> ((nsum s f) MOD n = nsum s (\i. f(i) MOD n) MOD n)
Proof
  GEN_TAC THEN GEN_TAC THEN
  ASM_CASES_TAC ``n = 0:num`` THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN KNOW_TAC ``(nsum s f MOD n = nsum s (\i. f i MOD n) MOD n) =
                     (\s. (nsum s f MOD n = nsum s (\i. f i MOD n) MOD n))s``
  THENL [FULL_SIMP_TAC std_ss [], ALL_TAC] THEN DISCH_TAC THEN
  ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC FINITE_INDUCT THEN
  BETA_TAC THEN FULL_SIMP_TAC std_ss [NSUM_CLAUSES, NOT_ZERO_LT_ZERO] THEN
  REPEAT STRIP_TAC THEN ASSUME_TAC MOD_PLUS THEN
  POP_ASSUM (MP_TAC o Q.SPEC `n`) THEN FULL_SIMP_TAC std_ss [] THEN DISCH_TAC
  THEN POP_ASSUM (MP_TAC o Q.SPECL [`f e`, `nsum s f`]) THEN ASM_REWRITE_TAC []
  THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FULL_SIMP_TAC std_ss [MOD_PLUS, ADD_MOD]
QED

Theorem MOD_NSUM_MOD_NUMSEG:
   !f a b n.
        ~(n = 0:num)
        ==> ((nsum{a..b} f) MOD n = nsum{a..b} (\i. f i MOD n) MOD n)
Proof
  METIS_TAC[MOD_NSUM_MOD, FINITE_NUMSEG]
QED

Theorem NSUM_CONG:
    (!f g s.   (!x. x IN s ==> (f(x) = g(x)))
           ==> (nsum s (\i. f(i)) = nsum s g)) /\
    (!f g a b. (!i. a <= i /\ i <= b ==> (f(i) = g(i)))
           ==> (nsum{a..b} (\i. f(i)) = nsum{a..b} g)) /\
    (!f g p.   (!x. p x ==> (f x = g x))
           ==> (nsum {y | p y} (\i. f(i)) = nsum {y | p y} g))
Proof
    REPEAT STRIP_TAC
 >> MATCH_MP_TAC NSUM_EQ
 >> ASM_SIMP_TAC std_ss [GSPECIFICATION, IN_NUMSEG]
QED

(* ------------------------------------------------------------------------- *)
(* Thanks to finite sums, we can express cardinality of finite union.        *)
(* ------------------------------------------------------------------------- *)

Theorem CARD_BIGUNION:
   !s:('a->bool)->bool.
        FINITE s /\ (!t. t IN s ==> FINITE t) /\
        (!t u. t IN s /\ u IN s /\ ~(t = u) ==> (t INTER u = {}))
        ==> (CARD(BIGUNION s) = nsum s CARD)
Proof
  ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] THEN GEN_TAC THEN
  KNOW_TAC ``((!t. t IN s ==> FINITE t) /\
    (!t u. t IN s /\ u IN s /\ t <> u ==> (t INTER u = {})) ==>
    (CARD (BIGUNION s) = nsum s CARD)) =
    (\s. (!t. t IN s ==> FINITE t) /\
    (!t u. t IN s /\ u IN s /\ t <> u ==> (t INTER u = {})) ==>
    (CARD (BIGUNION s) = nsum s CARD)) (s:('a->bool)->bool)`` THENL
  [FULL_SIMP_TAC std_ss [], DISC_RW_KILL THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  REWRITE_TAC[BIGUNION_EMPTY, BIGUNION_INSERT, NOT_IN_EMPTY, IN_INSERT] THEN
  REWRITE_TAC[CARD_DEF, NSUM_CLAUSES] THEN
  SIMP_TAC std_ss [GSYM RIGHT_FORALL_IMP_THM] THEN
  MAP_EVERY X_GEN_TAC [``f:('a->bool)->bool``, ``t:'a->bool``] THEN
  DISCH_THEN(fn th => STRIP_TAC THEN MP_TAC th) THEN
  ASM_SIMP_TAC std_ss [NSUM_CLAUSES] THEN REPEAT STRIP_TAC THEN
  FULL_SIMP_TAC std_ss [] THEN
  UNDISCH_TAC ``CARD (BIGUNION f) = nsum f CARD`` THEN
  GEN_REWR_TAC LAND_CONV [EQ_SYM_EQ] THEN RW_TAC std_ss [] THEN
  MATCH_MP_TAC (GSYM CARD_UNION_EQ) THEN FULL_SIMP_TAC std_ss [] THEN
  CONJ_TAC THENL [METIS_TAC [FINITE_BIGUNION, FINITE_UNION], ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN
  KNOW_TAC ``(!s t. t INTER BIGUNION s = BIGUNION {t INTER x | x IN s})`` THENL
  [ONCE_REWRITE_TAC[EXTENSION] THEN
  SIMP_TAC std_ss [IN_BIGUNION, GSPECIFICATION, IN_INTER] THEN
  MESON_TAC[IN_INTER], ALL_TAC] THEN
  DISC_RW_KILL THEN
  SIMP_TAC std_ss [SET_RULE ``!s. (BIGUNION s = {}) <=> !t. t IN s ==> (t = {})``, GSPECIFICATION] THEN
  METIS_TAC[]]
QED

(* ========================================================================= *)
(*     Products of natural numbers and real numbers (productScript.sml)      *)
(* ========================================================================= *)

Definition nproduct :
   nproduct = iterate(( * ):num->num->num)
End

Theorem NPRODUCT_CLAUSES:
   (!f. nproduct {} f = 1) /\
   (!x f s. FINITE(s)
            ==> (nproduct (x INSERT s) f =
                 if x IN s then nproduct s f else f(x) * nproduct s f))
Proof
  REWRITE_TAC[nproduct, GSYM NEUTRAL_MUL] THEN
  METIS_TAC [SWAP_FORALL_THM, ITERATE_CLAUSES, MONOIDAL_MUL]
QED

Theorem NPRODUCT_SUPPORT:
   !f s. nproduct (support ( * ) f s) f = nproduct s f
Proof
  REWRITE_TAC[nproduct, ITERATE_SUPPORT]
QED

Theorem NPRODUCT_UNION:
   !f s t. FINITE s /\ FINITE t /\ DISJOINT s t
           ==> ((nproduct (s UNION t) f = nproduct s f * nproduct t f))
Proof
  SIMP_TAC std_ss [nproduct, ITERATE_UNION, MONOIDAL_MUL]
QED

Theorem NPRODUCT_IMAGE:
   !f g s. (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
           ==> (nproduct (IMAGE f s) g = nproduct s (g o f))
Proof
  REWRITE_TAC[nproduct, GSYM NEUTRAL_MUL] THEN
  MATCH_MP_TAC ITERATE_IMAGE THEN REWRITE_TAC[MONOIDAL_MUL]
QED

Theorem NPRODUCT_ADD_SPLIT:
   !f m n p.
        m <= n + 1
        ==> ((nproduct {m..n+p} f = nproduct{m..n} f * nproduct{n+1..n+p} f))
Proof
  METIS_TAC [NUMSEG_ADD_SPLIT, NPRODUCT_UNION, DISJOINT_NUMSEG, FINITE_NUMSEG,
           ARITH_PROVE ``x < x + 1:num``]
QED

Theorem NPRODUCT_POS_LT:
   !f s. FINITE s /\ (!x. x IN s ==> 0 < f x) ==> 0 < nproduct s f
Proof
  GEN_TAC THEN REWRITE_TAC[CONJ_EQ_IMP] THEN
  ONCE_REWRITE_TAC [METIS []
   ``!s. ((!x. x IN s ==> 0 < f x) ==> 0 < nproduct s f) =
     (\s. (!x. x IN s ==> 0 < f x) ==> 0 < nproduct s f) s``] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC arith_ss [NPRODUCT_CLAUSES, IN_INSERT, ZERO_LESS_MULT]
QED

Theorem NPRODUCT_POS_LT_NUMSEG:
   !f m n. (!x. m <= x /\ x <= n ==> 0 < f x) ==> 0 < nproduct{m..n} f
Proof
  SIMP_TAC std_ss [NPRODUCT_POS_LT, FINITE_NUMSEG, IN_NUMSEG]
QED

Theorem NPRODUCT_OFFSET:
   !f m p. nproduct{m+p..n+p} f = nproduct{m..n} (\i. f(i + p))
Proof
  SIMP_TAC std_ss [NUMSEG_OFFSET_IMAGE, NPRODUCT_IMAGE,
           EQ_ADD_RCANCEL, FINITE_NUMSEG] THEN
  SIMP_TAC std_ss [o_DEF]
QED

Theorem NPRODUCT_SING:
   !f x. nproduct {x} f = f(x)
Proof
  SIMP_TAC std_ss [NPRODUCT_CLAUSES, FINITE_EMPTY, FINITE_INSERT, NOT_IN_EMPTY, MULT_CLAUSES]
QED

Theorem NPRODUCT_SING_NUMSEG:
   !f n. nproduct{n..n} f = f(n)
Proof
  REWRITE_TAC[NUMSEG_SING, NPRODUCT_SING]
QED

Theorem NPRODUCT_CLAUSES_NUMSEG:
   (!m. nproduct{m..0n} f = if m = 0 then f(0) else 1) /\
   (!m n. nproduct{m..SUC n} f = if m <= SUC n then nproduct{m..n} f * f(SUC n)
                                else nproduct{m..n} f)
Proof
  REWRITE_TAC[NUMSEG_CLAUSES] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC std_ss [NPRODUCT_SING, NPRODUCT_CLAUSES, FINITE_NUMSEG, IN_NUMSEG] THEN
  SIMP_TAC arith_ss [ARITH_PROVE ``~(SUC n <= n)``]
QED

Theorem NPRODUCT_EQ:
   !f g s. (!x. x IN s ==> (f x = g x)) ==> (nproduct s f = nproduct s g)
Proof
  REWRITE_TAC[nproduct] THEN MATCH_MP_TAC ITERATE_EQ THEN
  SIMP_TAC std_ss [MONOIDAL_MUL]
QED

Theorem NPRODUCT_EQ_NUMSEG:
   !f g m n. (!i. m <= i /\ i <= n ==> (f(i) = g(i)))
             ==> (nproduct{m..n} f = nproduct{m..n} g)
Proof
  MESON_TAC[NPRODUCT_EQ, FINITE_NUMSEG, IN_NUMSEG]
QED

Theorem NPRODUCT_EQ_0:
   !f s. FINITE s ==> ((nproduct s f = 0) <=> ?x. x IN s /\ (f(x) = 0))
Proof
  GEN_TAC THEN
  ONCE_REWRITE_TAC [METIS []
   ``!s. ((nproduct s f = 0) <=> ?x. x IN s /\ (f x = 0)) =
         (\s. ((nproduct s f = 0) <=> ?x. x IN s /\ (f x = 0))) s``] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC arith_ss [NPRODUCT_CLAUSES, MULT_EQ_0, IN_INSERT, NOT_IN_EMPTY] THEN
  MESON_TAC[]
QED

Theorem NPRODUCT_EQ_0_NUMSEG:
   !f m n. (nproduct{m..n} f = 0) <=> ?x. m <= x /\ x <= n /\ (f(x) = 0)
Proof
  SIMP_TAC std_ss [NPRODUCT_EQ_0, FINITE_NUMSEG, IN_NUMSEG, GSYM CONJ_ASSOC]
QED

Theorem NPRODUCT_LE:
   !f s. FINITE s /\ (!x. x IN s ==> 0 <= f(x) /\ f(x) <= g(x))
         ==> nproduct s f <= nproduct s g
Proof
  GEN_TAC THEN REWRITE_TAC[CONJ_EQ_IMP] THEN
  ONCE_REWRITE_TAC [METIS []
   ``!s. ((!x. x IN s ==> 0 <= f x /\ f x <= g x) ==>
  nproduct s f <= nproduct s g) =
     (\s. (!x. x IN s ==> 0 <= f x /\ f x <= g x) ==>
  nproduct s f <= nproduct s g) s``] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC std_ss [IN_INSERT, NPRODUCT_CLAUSES, NOT_IN_EMPTY, LESS_EQ_REFL] THEN
  MESON_TAC[LESS_MONO_MULT2, ZERO_LESS_EQ]
QED

Theorem NPRODUCT_LE_NUMSEG:
   !f m n. (!i. m <= i /\ i <= n ==> 0 <= f(i) /\ f(i) <= g(i))
           ==> nproduct{m..n} f <= nproduct{m..n} g
Proof
  SIMP_TAC std_ss [NPRODUCT_LE, FINITE_NUMSEG, IN_NUMSEG]
QED

Theorem NPRODUCT_EQ_1:
   !f s. (!x:'a. x IN s ==> (f(x) = 1)) ==> (nproduct s f = 1)
Proof
  REWRITE_TAC[nproduct, GSYM NEUTRAL_MUL] THEN
  SIMP_TAC std_ss [ITERATE_EQ_NEUTRAL, MONOIDAL_MUL]
QED

Theorem NPRODUCT_EQ_1_NUMSEG:
   !f m n. (!i. m <= i /\ i <= n ==> (f(i) = 1)) ==> (nproduct{m..n} f = 1)
Proof
  SIMP_TAC std_ss [NPRODUCT_EQ_1, IN_NUMSEG]
QED

Theorem NPRODUCT_MUL_GEN:
   !f g s.
       FINITE {x | x IN s /\ ~(f x = 1)} /\ FINITE {x | x IN s /\ ~(g x = 1)}
       ==> (nproduct s (\x. f x * g x) = nproduct s f * nproduct s g)
Proof
  SIMP_TAC std_ss [GSYM NEUTRAL_MUL, GSYM support, nproduct] THEN
  MATCH_MP_TAC ITERATE_OP_GEN THEN ACCEPT_TAC MONOIDAL_MUL
QED

Theorem NPRODUCT_MUL:
   !f g s. FINITE s
           ==> (nproduct s (\x. f x * g x) = nproduct s f * nproduct s g)
Proof
  GEN_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC [METIS []
    ``(nproduct s (\x. f x * g x) = nproduct s f * nproduct s g) =
 (\s. (nproduct s (\x. f x * g x) = nproduct s f * nproduct s g)) s``] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC arith_ss [NPRODUCT_CLAUSES, MULT_CLAUSES]
QED

Theorem NPRODUCT_MUL_NUMSEG:
   !f g m n.
     nproduct{m..n} (\x. f x * g x) = nproduct{m..n} f * nproduct{m..n} g
Proof
  SIMP_TAC std_ss [NPRODUCT_MUL, FINITE_NUMSEG]
QED

Theorem NPRODUCT_CONST:
   !c s. FINITE s ==> (nproduct s (\x. c) = c EXP (CARD s))
Proof
  GEN_TAC THEN
  ONCE_REWRITE_TAC [METIS []
   ``(nproduct s (\x. c) = c EXP (CARD s)) =
     (\s. (nproduct s (\x. c) = c EXP (CARD s))) s``] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC arith_ss [NPRODUCT_CLAUSES, CARD_EMPTY, CARD_INSERT, EXP]
QED

Theorem NPRODUCT_CONST_NUMSEG:
   !c m n. nproduct {m..n} (\x. c) = c EXP ((n + 1) - m)
Proof
  SIMP_TAC std_ss [NPRODUCT_CONST, CARD_NUMSEG, FINITE_NUMSEG]
QED

Theorem NPRODUCT_CONST_NUMSEG_1:
   !c n. nproduct{1n..n} (\x. c) = c EXP n
Proof
  SIMP_TAC arith_ss [NPRODUCT_CONST, CARD_NUMSEG_1, FINITE_NUMSEG]
QED

Theorem NPRODUCT_ONE:
   !s. nproduct s (\n. 1) = 1
Proof
  SIMP_TAC std_ss [NPRODUCT_EQ_1]
QED

Theorem NPRODUCT_CLOSED:
   !P f:'a->num s.
        P(1) /\ (!x y. P x /\ P y ==> P(x * y)) /\ (!a. a IN s ==> P(f a))
        ==> P(nproduct s f)
Proof
  REPEAT STRIP_TAC THEN MP_TAC(MATCH_MP ITERATE_CLOSED MONOIDAL_MUL) THEN
  DISCH_THEN(MP_TAC o SPEC ``P:num->bool``) THEN
  ASM_SIMP_TAC std_ss [NEUTRAL_MUL, GSYM nproduct]
QED

Theorem NPRODUCT_CLAUSES_LEFT:
   !f m n. m <= n ==> (nproduct{m..n} f = f(m) * nproduct{m+1n..n} f)
Proof
  SIMP_TAC std_ss [GSYM NUMSEG_LREC, NPRODUCT_CLAUSES, FINITE_NUMSEG, IN_NUMSEG] THEN
  ARITH_TAC
QED

Theorem NPRODUCT_CLAUSES_RIGHT:
   !f m n. 0 < n /\ m <= n ==> (nproduct{m..n} f = nproduct{m..n-1n} f * f(n))
Proof
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  SIMP_TAC std_ss [LESS_REFL, NPRODUCT_CLAUSES_NUMSEG, SUC_SUB1]
QED

Theorem NPRODUCT_SUPERSET:
   !f:'a->num u v.
        u SUBSET v /\ (!x. x IN v /\ ~(x IN u) ==> (f(x) = 1))
        ==> (nproduct v f = nproduct u f)
Proof
  SIMP_TAC std_ss [nproduct, GSYM NEUTRAL_MUL, ITERATE_SUPERSET, MONOIDAL_MUL]
QED

Theorem NPRODUCT_PAIR:
   !f m n. nproduct{2n*m..2n*n+1n} f = nproduct{m..n} (\i. f(2*i) * f(2*i+1))
Proof
  MP_TAC(MATCH_MP ITERATE_PAIR MONOIDAL_MUL) THEN
  REWRITE_TAC[nproduct, NEUTRAL_MUL]
QED

Theorem NPRODUCT_DELETE:
   !f s a. FINITE s /\ a IN s
           ==> (f(a) * nproduct(s DELETE a) f = nproduct s f)
Proof
  SIMP_TAC std_ss [nproduct, ITERATE_DELETE, MONOIDAL_MUL]
QED

Theorem NPRODUCT_FACT:
   !n. nproduct{1n..n} (\m. m) = FACT n
Proof
  INDUCT_TAC THEN SIMP_TAC arith_ss [NPRODUCT_CLAUSES_NUMSEG, FACT] THEN
  ASM_SIMP_TAC std_ss [ARITH_PROVE ``1 <= SUC n``, MULT_SYM]
QED

Theorem NPRODUCT_DELTA:
   !s a. nproduct s (\x. if x = a then b else 1) =
         (if a IN s then b else 1)
Proof
  REWRITE_TAC[nproduct, GSYM NEUTRAL_MUL] THEN
  SIMP_TAC std_ss [ITERATE_DELTA, MONOIDAL_MUL]
QED

(* ------------------------------------------------------------------------- *)
(* Extend congruences.                                                       *)
(* ------------------------------------------------------------------------- *)

Theorem NPRODUCT_CONG :
    (!f g s.   (!x. x IN s ==> (f(x) = g(x)))
           ==> (nproduct s (\i. f(i)) = nproduct s g)) /\
    (!f g a b. (!i. a <= i /\ i <= b ==> (f(i) = g(i)))
           ==> (nproduct{a..b} (\i. f(i)) = nproduct{a..b} g)) /\
    (!f g p.   (!x. p x ==> (f x = g x))
           ==> (nproduct {y | p y} (\i. f(i)) = nproduct {y | p y} g))
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC NPRODUCT_EQ
 >> ASM_SIMP_TAC std_ss [GSPECIFICATION, IN_NUMSEG]
QED

(* ------------------------------------------------------------------------- *)
(* Using additivity of lifted function to encode definedness.                *)
(* ------------------------------------------------------------------------- *)

(* moved here from integrationTheory *)
Definition lifted :
   (lifted op NONE _ = NONE) /\
   (lifted op _ NONE = NONE) /\
   (lifted op (SOME x) (SOME y) = SOME(op x y))
End

Theorem NEUTRAL_LIFTED:
   !op. monoidal op ==> (neutral(lifted op) = SOME(neutral op))
Proof
  REWRITE_TAC[neutral, monoidal] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN
  SIMP_TAC std_ss [FORALL_OPTION, lifted, NOT_NONE_SOME, option_CLAUSES] THEN
  ASM_MESON_TAC[]
QED

Theorem MONOIDAL_LIFTED:
   !op. monoidal op ==> monoidal(lifted op)
Proof
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC std_ss [NEUTRAL_LIFTED, monoidal] THEN
  SIMP_TAC std_ss [FORALL_OPTION, lifted, NOT_NONE_SOME, option_CLAUSES] THEN
  ASM_MESON_TAC[monoidal]
QED

Theorem ITERATE_SOME:
   !op. monoidal op ==> !f s. FINITE s
   ==> (iterate (lifted op) s (\x. SOME(f x)) =
           SOME(iterate op s f))
Proof
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  KNOW_TAC ``!(s :'b -> bool).
               FINITE s ==>
               (\s. (iterate (lifted (op :'a -> 'a -> 'a)) s
                   (\(x :'b). SOME ((f :'b -> 'a) x)) =
                 SOME (iterate op s f))) s`` THENL
  [ALL_TAC, SIMP_TAC std_ss []] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  ASM_SIMP_TAC std_ss [ITERATE_CLAUSES, MONOIDAL_LIFTED, NEUTRAL_LIFTED] THEN
  SIMP_TAC std_ss [lifted]
QED

Theorem NEUTRAL_AND:
   neutral(/\) = T
Proof
  SIMP_TAC std_ss [neutral, FORALL_BOOL] THEN METIS_TAC[]
QED

Theorem MONOIDAL_AND:
   monoidal(/\)
Proof
  REWRITE_TAC [monoidal] THEN
  SIMP_TAC std_ss [NEUTRAL_AND, CONJ_ACI]
QED

Theorem ITERATE_AND:
   !p s. FINITE s ==> (iterate(/\) s p <=> !x. x IN s ==> p x)
Proof
  GEN_TAC THEN
  ONCE_REWRITE_TAC [METIS [] ``!s. ((iterate(/\) s p <=> !x. x IN s ==> p x)) =
                          (\s. (iterate(/\) s p <=> !x. x IN s ==> p x)) s``] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  ASM_SIMP_TAC std_ss [MONOIDAL_AND, NEUTRAL_AND, ITERATE_CLAUSES] THEN SET_TAC[]
QED

(* ------------------------------------------------------------------------- *)
(* Permutations of index set for iterated operations.                        *)
(* ------------------------------------------------------------------------- *)

Theorem ITERATE_PERMUTE :
  !op. monoidal op ==>
       !(f:'a -> 'b) p s. p permutes s ==>
                          (iterate op s f = iterate op s (f o p))
Proof
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_BIJECTION) THEN
  PROVE_TAC[permutes]
QED

Theorem NSUM_PERMUTE :
   !f p s. p permutes s ==> (nsum s f = nsum s (f o p))
Proof
  REWRITE_TAC[nsum] THEN MATCH_MP_TAC ITERATE_PERMUTE THEN
  REWRITE_TAC[MONOIDAL_ADD]
QED

Theorem NSUM_PERMUTE_COUNT :
   !f p n. p permutes (count n) ==> (nsum (count n) f = nsum (count n) (f o p))
Proof
  PROVE_TAC[NSUM_PERMUTE, FINITE_COUNT]
QED

Theorem NSUM_PERMUTE_NUMSEG :
   !f p m n. p permutes (count n DIFF count m) ==>
            (nsum (count n DIFF count m) f = nsum (count n DIFF count m) (f o p))
Proof
  PROVE_TAC[NSUM_PERMUTE, FINITE_COUNT, FINITE_DIFF]
QED

Theorem TRANSFORM_2D_NUM :
    !P. (!m n : num. P m n ==> P n m) /\ (!m n. P m (m + n)) ==> (!m n. P m n)
Proof
    rpt STRIP_TAC
 >> Know `m <= n \/ n <= m` >- DECIDE_TAC
 >> RW_TAC std_ss [LESS_EQ_EXISTS]
 >> PROVE_TAC []
QED

Theorem TRIANGLE_2D_NUM :
    !P. (!d n. P n (d + n)) ==> (!m n : num. m <= n ==> P m n)
Proof
    RW_TAC std_ss [LESS_EQ_EXISTS]
 >> PROVE_TAC [ADD_COMM]
QED

