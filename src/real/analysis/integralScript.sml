(* ======================================================================== *)
(* Formalization of Kurzweil-Henstock gauge integral [1]                    *)
(* ======================================================================== *)

(* =====================================================================
    Theory: GAUGE INTEGRALS [2]
    Description: Generalized gauge intgrals and related theorems
       (ported from the HOL Light theory of the same)

    Email: grace_gwq@163.com
    DATE: 08-10-2012

    Ported by:
      Weiqing Gu, Zhiping Shi, Yong Guan, Shengzhen Jin, Xiaojuan Li

    Beijing Engineering Research Center of High Reliable Embedded System

    College of Information Engineering, Capital Normal University (CNU)
                        Beijing, China
   ===================================================================== *)

open HolKernel Parse bossLib boolLib;

open boolTheory powserTheory PairedLambda Diff mesonLib tautLib
     limTheory numLib reduceLib pairLib real_sigmaTheory
     pairTheory arithmeticTheory numTheory prim_recTheory jrhUtils realTheory
     realLib metricTheory netsTheory seqTheory pred_setTheory relationTheory;

open topologyTheory iterateTheory real_topologyTheory integrationTheory;

val _ = new_theory "integral";

local
  val ss = ["lift_disj_eq", "lift_imp_disj"];
in
  val bool_ss  = bool_ss  -* ss;
  val std_ss   = std_ss   -* ss;
  val arith_ss = arith_ss -* ss;
  val real_ss  = real_ss  -* ss;
  val _ = temp_delsimps ss;
end;

val _ = Parse.reveal "B";

(* Mini HOL-Light compatibility layer *)
val LE_0   = arithmeticTheory.ZERO_LESS_EQ;
val LT_0   = prim_recTheory.LESS_0;
val EQ_SUC = prim_recTheory.INV_SUC_EQ;

fun LE_MATCH_TAC th (asl,w) =
  let val thi = PART_MATCH (rand o rator) th (rand(rator w))
      val tm = rand(concl thi)
  in
   (MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC tm THEN CONJ_TAC THENL
    [MATCH_ACCEPT_TAC th, ALL_TAC]) (asl,w)
  end;

(* Mini hurdUtils *)
val Suff = Q_TAC SUFF_TAC;
val Know = Q_TAC KNOW_TAC;
fun wrap a = [a];
val Rewr  = DISCH_THEN (REWRITE_TAC o wrap);
val Rewr' = DISCH_THEN (ONCE_REWRITE_TAC o wrap);
val art = ASM_REWRITE_TAC;
val POP_ORW = POP_ASSUM (ONCE_REWRITE_TAC o wrap);
fun K_TAC _ = ALL_TAC;
val KILL_TAC = POP_ASSUM_LIST K_TAC;
local
  val th = prove (“!a b. a /\ (a ==> b) ==> a /\ b”, PROVE_TAC [])
in
  val STRONG_CONJ_TAC = MATCH_MP_TAC th >> CONJ_TAC;
end;

(* ------------------------------------------------------------------------ *)
(* Some miscellaneous lemmas                                                *)
(* ------------------------------------------------------------------------ *)

Theorem LESS_1[local] :
    !n:num. n < 1 <=> (n = 0)
Proof
  INDUCT_TAC >> REWRITE_TAC [ONE,LESS_0,LESS_MONO_EQ,NOT_LESS_0,GSYM SUC_NOT]
QED

(* ------------------------------------------------------------------------ *)
(* Divisions and tagged divisions etc.                                      *)
(* ------------------------------------------------------------------------ *)

(* D represents a finite order set of points as a partition of I = [a,b] *)
Definition division :
   division(a,b) D <=>
     (D 0 = a) /\
     (?N. (!n. n < N ==> D(n) < D(SUC n)) /\
          (!n. n >= N ==> (D(n) = b)))
End

(* The "infinite tail" of D remains the value of the last point D(N) *)
Definition dsize :
   dsize D =
      @N. (!n. n < N ==> D(n) < D(SUC n)) /\
          (!n. n >= N ==> (D(n) = D(N)))
End

(* tagged division, p(n) is the tag of each intervals of the division D *)
Definition tdiv :
   tdiv(a,b) (D,p) <=>
     division(a,b) D /\
     (!n. D(n) <= p(n) /\ p(n) <= D(SUC n))
End

(* ------------------------------------------------------------------------ *)
(* Gauges and gauge-fine divisions                                          *)
(* ------------------------------------------------------------------------ *)

(* A function g is said to be a gauge on E if g(x) > 0 for all x IN E [1, p.8]

   cf. integrationTheory.gauge_def (Gauge)
 *)
Definition gauge :
   gauge(E) (g:real->real) = !x. E x ==> &0 < g(x)
End

(* connection to integrationTheory, thus the function g (as the gauge) will be
   used as the radius of each division as open intervals. *)
Theorem gauge_alt :
    !c E g. 0 < c ==> (gauge E g <=> Gauge (\x. ball(x, if E x then c * g(x) else 1)))
Proof
    rw [gauge, gauge_def, CENTRE_IN_BALL, OPEN_BALL]
 >> EQ_TAC >> rw []
 >- (Cases_on ‘E x’ >> rw [] \\
     MATCH_MP_TAC REAL_LT_MUL >> rw [])
 >> Q.PAT_X_ASSUM ‘!x. P’ (MP_TAC o (Q.SPEC ‘x’))
 >> Cases_on ‘E x’ >> fs []
 >> rw [REAL_LT_LMUL_0]
QED

Theorem gauge_alt_univ :
    !c g. 0 < c ==> (gauge univ(:real) g <=> Gauge (\x. ball(x,c * g(x))))
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘c’, ‘univ(:real)’, ‘g’] gauge_alt) >> rw []
QED

(* g is the gauge function (the range E is ignored), D is a division, p is the
   tag of each intervals in the division
 *)
Definition fine :
   fine(g:real->real) (D,p) =
     !n. n < dsize D ==> D(SUC n) - D(n) < g(p(n))
End

(* ------------------------------------------------------------------------ *)
(* Riemann sum                                                              *)
(* ------------------------------------------------------------------------ *)

Definition rsum :
   rsum (D,(p:num->real)) f =
        sum(0,dsize(D))(\n. f(p n) * (D(SUC n) - D(n)))
End

(* ------------------------------------------------------------------------ *)
(* Gauge integrability (definite)                                           *)
(* ------------------------------------------------------------------------ *)

(* cf. integrationTheory.has_integral

   NOTE: only integration on (closed) intervals are supported in integralTheory.
 *)
Definition Dint :
   Dint(a,b) f k <=>
       !e. &0 < e ==>
           ?g. gauge(\x. a <= x /\ x <= b) g /\
               !D p. tdiv(a,b) (D,p) /\ fine(g)(D,p) ==>
                   abs(rsum(D,p) f - k) < e
End

(* ------------------------------------------------------------------------ *)
(* Useful lemmas about the size of `trivial` divisions etc.                 *)
(* ------------------------------------------------------------------------ *)

Theorem DIVISION_0 :
    !a b. (a = b) ==> dsize(\n:num. if (n = 0) then a else b) = 0
Proof
  REPEAT GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC[COND_ID] THEN
  REWRITE_TAC[dsize] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC (Term `n:num`) THEN BETA_TAC THEN
  REWRITE_TAC[REAL_LT_REFL, NOT_LESS] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC (Term `0:num`)) THEN
     REWRITE_TAC[LESS_OR_EQ,NOT_LESS_0],
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ZERO_LESS_EQ]]
QED

Theorem DIVISION_1 :
    !a b. a < b ==> dsize(\n. if (n = 0) then a else b) = 1
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[dsize] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC (Term `n:num`) THEN BETA_TAC THEN
  REWRITE_TAC[NOT_SUC] THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC LESS_EQUAL_ANTISYM THEN CONJ_TAC THENL
     [POP_ASSUM(MP_TAC o SPEC (Term`1:num`) o CONJUNCT1) THEN
      REWRITE_TAC[ONE, GSYM SUC_NOT] THEN
      REWRITE_TAC[REAL_LT_REFL, NOT_LESS],
      POP_ASSUM(MP_TAC o SPEC (Term `2:num`) o CONJUNCT2) THEN
      REWRITE_TAC[TWO, GSYM SUC_NOT, GREATER_EQ] THEN
      CONV_TAC CONTRAPOS_CONV THEN
      REWRITE_TAC[ONE, NOT_SUC_LESS_EQ, CONJUNCT1 LE] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NOT_SUC, NOT_IMP] THEN
      REWRITE_TAC[LE] THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
      MATCH_MP_TAC REAL_LT_IMP_NE THEN POP_ASSUM ACCEPT_TAC],
    DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[ONE,LESS_THM, NOT_LESS_0] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[],
      X_GEN_TAC (Term `n:num`) THEN REWRITE_TAC[GREATER_EQ,ONE]
      THEN ASM_CASES_TAC (Term `n:num = 0`) THEN
      ASM_REWRITE_TAC[CONJUNCT1 LE, GSYM NOT_SUC, NOT_SUC]]]
QED

Theorem DIVISION_SINGLE :
    !a b. a <= b ==> division(a,b)(\n. if (n = 0) then a else b)
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[division] THEN
  BETA_TAC THEN REWRITE_TAC[] THEN
  POP_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
   [EXISTS_TAC (Term `1:num`) THEN CONJ_TAC THEN X_GEN_TAC (Term `n:num`) THENL
     [REWRITE_TAC[LESS_1] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[NOT_SUC],
      REWRITE_TAC[GREATER_EQ] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[ONE] THEN
      REWRITE_TAC[LE, NOT_SUC]],
    EXISTS_TAC (Term `0:num`) THEN REWRITE_TAC[NOT_LESS_0] THEN
    ASM_REWRITE_TAC[COND_ID]]
QED

Theorem DIVISION_LHS :
    !D a b. division(a,b) D ==> (D(0) = a)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[division] THEN
  DISCH_THEN(fn th => REWRITE_TAC[th])
QED

Theorem DIVISION_THM :
  !D a b. division(a,b) D <=>
         (D(0) = a) /\
         (!n. n < dsize D ==> D(n) < D(SUC n)) /\
         (!n. n >= dsize D ==> D(n) = b)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[division] THEN
  EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC, EXISTS_TAC (Term `dsize D`) THEN ASM_REWRITE_TAC[]] THEN
  POP_ASSUM(X_CHOOSE_THEN (Term `N:num`) STRIP_ASSUME_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN (Term `dsize D:num = N`) (fn th => ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[dsize] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC (Term `M:num`) THEN BETA_TAC THEN EQ_TAC THENL
   [ALL_TAC, DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC (Term `N:num`) (ASSUME (Term `!n:num. n >= N ==> (D n:real = b)`)))
    THEN DISCH_THEN(MP_TAC o REWRITE_RULE[GREATER_EQ, LESS_EQ_REFL]) THEN
    DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC] THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (SPECL [Term `M:num`, Term `N:num`] LESS_LESS_CASES) THEN
  ASM_REWRITE_TAC[] THENL
   [DISCH_THEN(MP_TAC o SPEC (Term `SUC M`) o CONJUNCT2) THEN
    REWRITE_TAC[GREATER_EQ, LESS_EQ_SUC_REFL] THEN DISCH_TAC THEN
    UNDISCH_TAC (Term `!n:num. n < N ==> (D n) < (D(SUC n))`) THEN
    DISCH_THEN(MP_TAC o SPEC (Term`M:num`)) THEN ASM_REWRITE_TAC[REAL_LT_REFL],
    DISCH_THEN(MP_TAC o SPEC (Term`N:num`) o CONJUNCT1) THEN ASM_REWRITE_TAC[]
    THEN UNDISCH_TAC (Term`!n:num. n >= N ==> (D n:real = b)`) THEN
    DISCH_THEN(fn th => MP_TAC(SPEC (Term`N:num`) th) THEN
    MP_TAC(SPEC (Term`SUC N`) th)) THEN
    REWRITE_TAC[GREATER_EQ, LESS_EQ_SUC_REFL, LESS_EQ_REFL] THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_LT_REFL]]
QED

Theorem DIVISION_RHS :
    !D a b. division(a,b) D ==> (D(dsize D) = b)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[DIVISION_THM] THEN
  DISCH_THEN(MP_TAC o SPEC (Term`dsize D`) o last o CONJUNCTS) THEN
  REWRITE_TAC[GREATER_EQ, LESS_EQ_REFL]
QED

Theorem DIVISION_LT_GEN :
   !D a b m n. division(a,b) D /\ m < n /\ n <= (dsize D) ==> D(m) < D(n)
Proof
  REPEAT STRIP_TAC THEN UNDISCH_TAC (Term`m:num < n`) THEN
  DISCH_THEN(X_CHOOSE_THEN (Term`d:num`) MP_TAC o MATCH_MP LESS_ADD_1) THEN
  REWRITE_TAC[GSYM ADD1] THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC (Term `m + SUC d <= dsize D`) THEN
  SPEC_TAC(Term`d:num`,Term`d:num`) THEN INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OR_LESS) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[DIVISION_THM]) THEN ASM_REWRITE_TAC[],
    REWRITE_TAC[ADD_CLAUSES] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OR_LESS) THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LT_TRANS THEN
    EXISTS_TAC (Term`D(m + SUC d):real`) THEN CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
      MATCH_MP_TAC LESS_IMP_LESS_OR_EQ THEN ASM_REWRITE_TAC[],
      REWRITE_TAC[ADD_CLAUSES] THEN
      FIRST_ASSUM(MATCH_MP_TAC o el 2 o
        CONJUNCTS o REWRITE_RULE[DIVISION_THM]) THEN
      ASM_REWRITE_TAC[]]]
QED

Theorem DIVISION_LT :
   !D a b. division(a,b) D ==> !n. n < (dsize D) ==> D(0) < D(SUC n)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[DIVISION_THM] THEN STRIP_TAC THEN
  INDUCT_TAC THEN DISCH_THEN(fn th => ASSUME_TAC th THEN
      FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (Term`D(SUC n):real`) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC (Term`D(0:num):real = a`) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC (Term`SUC n`) THEN
  ASM_REWRITE_TAC[LESS_SUC_REFL]
QED

Theorem DIVISION_LE :
   !D a b. division(a,b) D ==> a <= b
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIVISION_LT) THEN
  POP_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[DIVISION_THM]) THEN
  UNDISCH_TAC (Term`D(0:num):real = a`) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC (Term`!n. n >= (dsize D) ==> (D n = b)`) THEN
  DISCH_THEN(MP_TAC o SPEC (Term`dsize D`)) THEN
  REWRITE_TAC[GREATER_EQ, LESS_EQ_REFL] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN(MP_TAC o SPEC (Term`PRE(dsize D)`)) THEN
  STRUCT_CASES_TAC(SPEC (Term`dsize D`) num_CASES) THEN
  ASM_REWRITE_TAC[PRE, REAL_LE_REFL, LESS_SUC_REFL, REAL_LT_IMP_LE]
QED

Theorem DIVISION_GT :
   !D a b. division(a,b) D ==> !n. n < (dsize D) ==> D(n) < D(dsize D)
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIVISION_LT_GEN THEN
  MAP_EVERY EXISTS_TAC [Term`a:real`, Term`b:real`] THEN
  ASM_REWRITE_TAC[LESS_EQ_REFL]
QED

Theorem DIVISION_EQ :
   !D a b. division(a,b) D ==> ((a = b) <=> (dsize D = 0))
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIVISION_LT) THEN
  POP_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[DIVISION_THM]) THEN
  UNDISCH_TAC (Term`D(0:num):real = a`) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC (Term`!n. n >= (dsize D) ==> (D n = b)`) THEN
  DISCH_THEN(MP_TAC o SPEC (Term`dsize D`)) THEN
  REWRITE_TAC[GREATER_EQ, LESS_EQ_REFL] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN(MP_TAC o SPEC (Term`PRE(dsize D)`)) THEN
  STRUCT_CASES_TAC(SPEC (Term`dsize D`) num_CASES) THEN
  ASM_REWRITE_TAC[PRE, NOT_SUC, LESS_SUC_REFL, REAL_LT_IMP_NE]
QED

Theorem DIVISION_LBOUND :
   !D a b. division(a,b) D ==> !r. a <= D(r)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[DIVISION_THM] THEN STRIP_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  DISJ_CASES_TAC(SPECL [Term`SUC r`, Term`dsize D`] LESS_CASES) THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (Term`(D:num->real) r`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC (Term`SUC r`) THEN
    ASM_REWRITE_TAC[LESS_SUC_REFL],
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (Term`b:real`) THEN CONJ_TAC
    THENL
     [MATCH_MP_TAC DIVISION_LE THEN
      EXISTS_TAC (Term`D:num->real`) THEN ASM_REWRITE_TAC[DIVISION_THM],
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[GREATER_EQ]]]
QED

Theorem DIVISION_LBOUND_LT :
   !D a b. division(a,b) D /\ ~(dsize D = 0) ==> !n. a < D(SUC n)
Proof
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP DIVISION_LHS) THEN
  DISJ_CASES_TAC(SPECL [Term`dsize D`, Term`SUC n`] LESS_CASES) THENL
   [FIRST_ASSUM(MP_TAC o el 3 o CONJUNCTS o REWRITE_RULE[DIVISION_THM]) THEN
    DISCH_THEN(MP_TAC o SPEC (Term`SUC n`)) THEN REWRITE_TAC[GREATER_EQ] THEN
    IMP_RES_THEN ASSUME_TAC LESS_IMP_LESS_OR_EQ THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP DIVISION_RHS) THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP DIVISION_GT) THEN
    ASM_REWRITE_TAC[GSYM NOT_LESS_EQUAL, CONJUNCT1 LE],
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP DIVISION_LT) THEN
    MATCH_MP_TAC OR_LESS THEN ASM_REWRITE_TAC[]]
QED

Theorem DIVISION_UBOUND :
   !D a b. division(a,b) D ==> !r. D(r) <= b
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[DIVISION_THM] THEN STRIP_TAC THEN
  GEN_TAC THEN DISJ_CASES_TAC(SPECL [Term`r:num`, Term`dsize D`] LESS_CASES)
  THENL [ALL_TAC,
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[GREATER_EQ]] THEN
  SUBGOAL_THEN (Term`!r. D((dsize D) - r) <= b`) MP_TAC THENL
   [ALL_TAC,
    DISCH_THEN(MP_TAC o SPEC (Term`(dsize D) - r`)) THEN
    MATCH_MP_TAC(TAUT_CONV “(a <=> b) ==> a ==> b”) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP SUB_SUB
         (MATCH_MP LESS_IMP_LESS_OR_EQ th)])
    THEN ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB]] THEN
  UNDISCH_TAC (Term`r < dsize D`) THEN DISCH_THEN(K ALL_TAC) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[SUB_0] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[GREATER_EQ, LESS_EQ_REFL],
    ALL_TAC] THEN
  DISJ_CASES_TAC(SPECL [Term`r:num`, Term`dsize D`] LESS_CASES) THENL
   [ALL_TAC,
    SUBGOAL_THEN (Term`(dsize D) - (SUC r) = 0`) SUBST1_TAC THENL
     [REWRITE_TAC[SUB_EQ_0] THEN MATCH_MP_TAC LESS_EQ_TRANS THEN
      EXISTS_TAC (Term`r:num`) THEN ASM_REWRITE_TAC[LESS_EQ_SUC_REFL],
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIVISION_LE THEN
      EXISTS_TAC (Term`D:num->real`) THEN ASM_REWRITE_TAC[DIVISION_THM]]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC (Term`D((dsize D) - r):real`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN (Term`(dsize D) - r = SUC((dsize D) - (SUC r))`)
  SUBST1_TAC THENL
   [ALL_TAC,
    MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LESS_CASES_IMP THEN
    REWRITE_TAC[NOT_LESS, SUB_LESS_EQ] THEN
    CONV_TAC(RAND_CONV SYM_CONV) THEN
    REWRITE_TAC[SUB_EQ_EQ_0, NOT_SUC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC (Term`r:num < 0`) THEN REWRITE_TAC[NOT_LESS_0]] THEN
  MP_TAC(SPECL [Term`dsize D`, Term`SUC r`] (CONJUNCT2 SUB)) THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[SUB_EQ_0, LESS_EQ_MONO] THEN
    ASM_REWRITE_TAC[GSYM NOT_LESS],
    DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC[SUB_MONO_EQ]]
QED

Theorem DIVISION_UBOUND_LT :
   !D a b n. division(a,b) D /\ n < dsize D ==> D(n) < b
Proof
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP DIVISION_RHS) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP DIVISION_GT) THEN
  ASM_REWRITE_TAC[]
QED

(* ------------------------------------------------------------------------ *)
(* Divisions of adjacent intervals can be combined into one                 *)
(* ------------------------------------------------------------------------ *)

val D_tm = Term`\n. if n < dsize D1 then D1(n) else D2(n - dsize D1)`
and p_tm = Term`\n. if n < dsize D1 then (p1:num->real)(n) else p2(n - dsize D1)`;

Theorem DIVISION_APPEND_LEMMA1[local] :
  !a b c D1 D2. division(a,b) D1 /\ division(b,c) D2 ==>
    (!n. n < dsize D1 + dsize D2 ==>
         (\n. if n < dsize D1 then D1(n) else D2(n - dsize D1)) (n)
            <
         (\n. if n < dsize D1 then D1(n) else D2(n - dsize D1)) (SUC n)) /\
    (!n. n >= dsize D1 + dsize D2 ==>
         (\n. if n<dsize D1 then D1(n) else D2(n - dsize D1)) (n)
            =
         (\n. if n<dsize D1 then D1(n) else D2(n - dsize D1)) (dsize D1 + dsize D2))
Proof
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN
  X_GEN_TAC (Term`n:num`) THEN DISCH_TAC THEN BETA_TAC THENL
   [ASM_CASES_TAC (Term`SUC n < dsize D1`) THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN (Term`n < dsize D1`) ASSUME_TAC THEN
      ASM_REWRITE_TAC[] THENL
       [MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC (Term`SUC n`) THEN
        ASM_REWRITE_TAC[LESS_SUC_REFL],
        UNDISCH_TAC (Term`division(a,b) D1`) THEN REWRITE_TAC[DIVISION_THM] THEN
        STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
        FIRST_ASSUM ACCEPT_TAC],
      ASM_CASES_TAC (Term`n < dsize D1`) THEN ASM_REWRITE_TAC[] THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[NOT_LESS]) THEN
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (Term`b:real`) THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC DIVISION_UBOUND_LT THEN
          EXISTS_TAC (Term`a:real`) THEN ASM_REWRITE_TAC[],
          MATCH_MP_TAC DIVISION_LBOUND THEN
          EXISTS_TAC (Term`c:real`) THEN ASM_REWRITE_TAC[]],
        UNDISCH_TAC (Term`~(n < dsize D1)`) THEN
        REWRITE_TAC[NOT_LESS] THEN
        DISCH_THEN(X_CHOOSE_THEN (Term`d:num`) SUBST_ALL_TAC o
          REWRITE_RULE[LESS_EQ_EXISTS]) THEN
        REWRITE_TAC[SUB, GSYM NOT_LESS_EQUAL, LESS_EQ_ADD] THEN
        ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB] THEN
        FIRST_ASSUM(MATCH_MP_TAC o Lib.trye el 2 o CONJUNCTS o
          REWRITE_RULE[DIVISION_THM]) THEN
        UNDISCH_TAC (Term`dsize D1 + d < dsize D1 + dsize D2`) THEN
        ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[LESS_MONO_ADD_EQ]]],
    REWRITE_TAC[GSYM NOT_LESS_EQUAL, LESS_EQ_ADD] THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB] THEN
    REWRITE_TAC[NOT_LESS_EQUAL] THEN COND_CASES_TAC THEN
    UNDISCH_TAC (Term`n >= dsize D1 + dsize D2`) THENL
     [CONV_TAC CONTRAPOS_CONV THEN DISCH_TAC THEN
      REWRITE_TAC[GREATER_EQ, NOT_LESS_EQUAL] THEN
      MATCH_MP_TAC LESS_IMP_LESS_ADD THEN ASM_REWRITE_TAC[],
      REWRITE_TAC[GREATER_EQ, LESS_EQ_EXISTS] THEN
      DISCH_THEN(X_CHOOSE_THEN (Term`d:num`) SUBST_ALL_TAC) THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
      REWRITE_TAC[ADD_SUB] THEN
      FIRST_ASSUM(CHANGED_TAC o
       (SUBST1_TAC o MATCH_MP DIVISION_RHS)) THEN
      FIRST_ASSUM(MATCH_MP_TAC o el 3 o CONJUNCTS o
        REWRITE_RULE[DIVISION_THM]) THEN
      REWRITE_TAC[GREATER_EQ, LESS_EQ_ADD]]]
QED

Theorem DIVISION_APPEND_LEMMA2[local] :
   !a b c D1 D2. division(a,b) D1 /\ division(b,c) D2 ==>
      (dsize(\n. if n < dsize D1 then D1(n) else D2(n - dsize D1))
         =
       dsize D1 + dsize D2)
Proof
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV empty_rewrites [dsize] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC (Term`N:num`) THEN BETA_TAC THEN EQ_TAC THENL
   [DISCH_THEN(curry op THEN (MATCH_MP_TAC LESS_EQUAL_ANTISYM) o MP_TAC) THEN
    CONV_TAC CONTRAPOS_CONV THEN
    REWRITE_TAC[DE_MORGAN_THM, NOT_LESS_EQUAL] THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [DISJ1_TAC THEN
      DISCH_THEN(MP_TAC o SPEC (Term`dsize D1 + dsize D2`)) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM NOT_LESS_EQUAL, LESS_EQ_ADD] THEN
      SUBGOAL_THEN (Term`!x y. x <= SUC(x + y)`) ASSUME_TAC THENL
       [REPEAT GEN_TAC THEN MATCH_MP_TAC LESS_EQ_TRANS THEN
        EXISTS_TAC (Term`(x:num) + y`) THEN
        REWRITE_TAC[LESS_EQ_ADD, LESS_EQ_SUC_REFL], ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUB, GSYM NOT_LESS_EQUAL] THEN
      REWRITE_TAC[LESS_EQ_ADD] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
      REWRITE_TAC[ADD_SUB] THEN
      MP_TAC(ASSUME (Term`division(b,c) D2`)) THEN REWRITE_TAC[DIVISION_THM]
      THEN DISCH_THEN(MP_TAC o SPEC (Term`SUC(dsize D2)`) o el 3 o CONJUNCTS)
      THEN REWRITE_TAC[GREATER_EQ, LESS_EQ_SUC_REFL] THEN
      DISCH_THEN SUBST1_TAC THEN
      FIRST_ASSUM(CHANGED_TAC o SUBST1_TAC o MATCH_MP DIVISION_RHS) THEN
      REWRITE_TAC[REAL_LT_REFL],
      DISJ2_TAC THEN
      DISCH_THEN(MP_TAC o SPEC (Term`dsize D1 + dsize D2`)) THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP LESS_IMP_LESS_OR_EQ) THEN
      ASM_REWRITE_TAC[GREATER_EQ] THEN
      REWRITE_TAC[GSYM NOT_LESS_EQUAL, LESS_EQ_ADD] THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB] THEN
      COND_CASES_TAC THENL
       [SUBGOAL_THEN (Term`D1(N:num) < D2(dsize D2)`) MP_TAC THENL
         [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (Term`b:real`) THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC DIVISION_UBOUND_LT THEN EXISTS_TAC (Term`a:real`) THEN
            ASM_REWRITE_TAC[GSYM NOT_LESS_EQUAL],
            MATCH_MP_TAC DIVISION_LBOUND THEN
            EXISTS_TAC (Term`c:real`) THEN ASM_REWRITE_TAC[]],
          CONV_TAC CONTRAPOS_CONV THEN ASM_REWRITE_TAC[] THEN
          DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_LT_REFL]],
        RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
        SUBGOAL_THEN (Term`D2(N - dsize D1) < D2(dsize D2)`) MP_TAC THENL
         [MATCH_MP_TAC DIVISION_LT_GEN THEN
          MAP_EVERY EXISTS_TAC [Term`b:real`, Term`c:real`] THEN
          ASM_REWRITE_TAC[LESS_EQ_REFL] THEN
          REWRITE_TAC[GSYM NOT_LESS_EQUAL] THEN
          REWRITE_TAC[SUB_LEFT_LESS_EQ, DE_MORGAN_THM] THEN
          ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[NOT_LESS_EQUAL] THEN
          UNDISCH_TAC (Term`dsize(D1) <= N`) THEN
          REWRITE_TAC[LESS_EQ_EXISTS] THEN
          DISCH_THEN(X_CHOOSE_THEN (Term`d:num`) SUBST_ALL_TAC) THEN
          RULE_ASSUM_TAC(ONCE_REWRITE_RULE[ADD_SYM]) THEN
          RULE_ASSUM_TAC(REWRITE_RULE[LESS_MONO_ADD_EQ]) THEN
          MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN EXISTS_TAC (Term`d:num`) THEN
          ASM_REWRITE_TAC[ZERO_LESS_EQ],
          CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
          DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_LT_REFL]]]],
  DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC (Term`n:num`) THEN DISCH_TAC THEN
    ASM_CASES_TAC (Term`SUC n < dsize D1`) THEN
    ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN (Term`n < dsize D1`) ASSUME_TAC THENL
       [MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC (Term`SUC n`) THEN
        ASM_REWRITE_TAC[LESS_SUC_REFL], ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIVISION_LT_GEN THEN
      MAP_EVERY EXISTS_TAC [Term`a:real`, Term`b:real`] THEN
      ASM_REWRITE_TAC[LESS_SUC_REFL] THEN
      MATCH_MP_TAC LESS_IMP_LESS_OR_EQ THEN ASM_REWRITE_TAC[],
      COND_CASES_TAC THENL
           [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (Term`b:real`) THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC DIVISION_UBOUND_LT THEN EXISTS_TAC (Term`a:real`) THEN
          ASM_REWRITE_TAC[],
          FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP DIVISION_LBOUND)],
        MATCH_MP_TAC DIVISION_LT_GEN THEN
        MAP_EVERY EXISTS_TAC [Term`b:real`, Term`c:real`] THEN
        ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL [ASM_REWRITE_TAC[SUB, LESS_SUC_REFL], ALL_TAC] THEN
        REWRITE_TAC[REWRITE_RULE[GREATER_EQ] SUB_LEFT_GREATER_EQ] THEN
        ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[GSYM LESS_EQ]]],
    X_GEN_TAC (Term`n:num`) THEN REWRITE_TAC[GREATER_EQ] THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM NOT_LESS_EQUAL,LESS_EQ_ADD] THEN
    SUBGOAL_THEN (Term`dsize D1 <= n`) ASSUME_TAC THENL
     [MATCH_MP_TAC LESS_EQ_TRANS THEN
      EXISTS_TAC (Term `dsize D1 + dsize D2`) THEN
      ASM_REWRITE_TAC[LESS_EQ_ADD],
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
      REWRITE_TAC[ADD_SUB] THEN
      FIRST_ASSUM(CHANGED_TAC o SUBST1_TAC o MATCH_MP DIVISION_RHS) THEN
      FIRST_ASSUM(MATCH_MP_TAC o el 3 o
        CONJUNCTS o REWRITE_RULE[DIVISION_THM]) THEN
      REWRITE_TAC[GREATER_EQ, SUB_LEFT_LESS_EQ] THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[]]]]
QED

Theorem DIVISION_APPEND_EXPLICIT[local] :
   !a b c g d1 p1 d2 p2.
        tdiv(a,b) (d1,p1) /\
        fine g (d1,p1) /\
        tdiv(b,c) (d2,p2) /\
        fine g (d2,p2)
        ==> tdiv(a,c)
              ((\n. if n < dsize d1 then  d1(n) else d2(n - (dsize d1))),
               (\n. if n < dsize d1
                    then p1(n) else p2(n - (dsize d1)))) /\
            fine g ((\n. if n < dsize d1 then  d1(n) else d2(n - (dsize d1))),
               (\n. if n < dsize d1
                    then p1(n) else p2(n - (dsize d1)))) /\
            !f. rsum((\n. if n < dsize d1 then  d1(n) else d2(n - (dsize d1))),
                     (\n. if n < dsize d1
                          then p1(n) else p2(n - (dsize d1)))) f =
                rsum(d1,p1) f + rsum(d2,p2) f
Proof
  MAP_EVERY X_GEN_TAC
   [Term`a:real`, Term`b:real`, Term`c:real`, Term`g:real->real`,
    Term`D1:num->real`, Term`p1:num->real`, Term`D2:num->real`,
    Term`p2:num->real`] THEN
  STRIP_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [DISJ_CASES_TAC(GSYM (SPEC “dsize(D1)” LESS_0_CASES)) THENL
    [ASM_REWRITE_TAC[NOT_LESS_0, SUB_0] THEN
         CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
         SUBGOAL_THEN “a:real = b” (fn th => ASM_REWRITE_TAC[th]) THEN
         MP_TAC(SPECL [Term`D1:num->real`,Term`a:real`,Term`b:real`]
                        DIVISION_EQ) THEN
         RULE_ASSUM_TAC(REWRITE_RULE[tdiv]) THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
         CONJ_TAC THENL
          [ALL_TAC,
           REWRITE_TAC[fine] THEN X_GEN_TAC (Term`n:num`) THEN
           RULE_ASSUM_TAC(REWRITE_RULE[tdiv]) THEN
           MP_TAC(SPECL [Term`a:real`, Term`b:real`, Term`c:real`,
                  Term`D1:num->real`, Term`D2:num->real`]
                                  DIVISION_APPEND_LEMMA2) THEN
           ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
           BETA_TAC THEN DISCH_TAC THEN ASM_CASES_TAC (Term`SUC n < dsize D1`) THEN
           ASM_REWRITE_TAC[] THENL
            [SUBGOAL_THEN (Term`n < dsize D1`) ASSUME_TAC THENL
                 [MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC (Term`SUC n`) THEN
                  ASM_REWRITE_TAC[LESS_SUC_REFL], ALL_TAC] THEN
                  ASM_REWRITE_TAC[] THEN
          FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[fine]) THEN
          ASM_REWRITE_TAC[],ALL_TAC] THEN
        ASM_CASES_TAC (Term`n < dsize D1`) THEN ASM_REWRITE_TAC[] THENL
         [SUBGOAL_THEN (Term`SUC n = dsize D1`) ASSUME_TAC THENL
           [MATCH_MP_TAC LESS_EQUAL_ANTISYM THEN
            ASM_REWRITE_TAC[GSYM NOT_LESS] THEN
            REWRITE_TAC[NOT_LESS] THEN MATCH_MP_TAC LESS_OR THEN
                ASM_REWRITE_TAC[],
            ASM_REWRITE_TAC[SUB_EQUAL_0] THEN
            FIRST_ASSUM(CHANGED_TAC o SUBST1_TAC o MATCH_MP DIVISION_LHS o
              CONJUNCT1) THEN
            FIRST_ASSUM(CHANGED_TAC o SUBST1_TAC o SYM o
              MATCH_MP DIVISION_RHS o CONJUNCT1) THEN
            SUBST1_TAC(SYM(ASSUME (Term`SUC n = dsize D1`))) THEN
            FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[fine]) THEN
            ASM_REWRITE_TAC[]],
          ASM_REWRITE_TAC[SUB] THEN UNDISCH_TAC (Term`~(n < (dsize D1))`) THEN
          REWRITE_TAC[LESS_EQ_EXISTS, NOT_LESS] THEN
          DISCH_THEN(X_CHOOSE_THEN (Term`d:num`) SUBST_ALL_TAC) THEN
          ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB] THEN
          FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[fine]) THEN
          RULE_ASSUM_TAC(ONCE_REWRITE_RULE[ADD_SYM]) THEN
          RULE_ASSUM_TAC(REWRITE_RULE[LESS_MONO_ADD_EQ]) THEN
          FIRST_ASSUM ACCEPT_TAC]] THEN
  REWRITE_TAC[tdiv] THEN BETA_TAC THEN CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[tdiv]) THEN
    REWRITE_TAC[DIVISION_THM] THEN CONJ_TAC THENL
         [BETA_TAC THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC DIVISION_LHS THEN EXISTS_TAC “b:real” THEN
          ASM_REWRITE_TAC[], ALL_TAC] THEN
        SUBGOAL_THEN “c = (\n. if (n < (dsize D1)) then  D1(n) else D2(n -
                  (dsize D1))) (dsize(D1) + dsize(D2))” SUBST1_TAC THENL
         [BETA_TAC THEN REWRITE_TAC[GSYM NOT_LESS_EQUAL, LESS_EQ_ADD] THEN
         ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB] THEN
         CONV_TAC SYM_CONV THEN MATCH_MP_TAC DIVISION_RHS THEN
         EXISTS_TAC (Term`b:real`) THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
        MP_TAC(SPECL [Term`a:real`, Term`b:real`, Term`c:real`,
                  Term`D1:num->real`, Term`D2:num->real`]
                                  DIVISION_APPEND_LEMMA2) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(fn th => REWRITE_TAC[th]) THEN
        MATCH_MP_TAC DIVISION_APPEND_LEMMA1 THEN
        MAP_EVERY EXISTS_TAC [Term`a:real`, Term`b:real`, Term`c:real`] THEN
        ASM_REWRITE_TAC[], ALL_TAC] THEN
  X_GEN_TAC (Term`n:num`) THEN RULE_ASSUM_TAC(REWRITE_RULE[tdiv]) THEN
  ASM_CASES_TAC (Term`SUC n < dsize D1`) THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN (Term`n < dsize D1`) ASSUME_TAC THENL
         [MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC (Term`SUC n`) THEN
          ASM_REWRITE_TAC[LESS_SUC_REFL], ALL_TAC] THEN
          ASM_REWRITE_TAC[],ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[SUB] THEN
    FIRST_ASSUM(CHANGED_TAC o SUBST1_TAC o MATCH_MP DIVISION_LHS o
          CONJUNCT1) THEN
        FIRST_ASSUM(CHANGED_TAC o SUBST1_TAC o SYM o
          MATCH_MP DIVISION_RHS o  CONJUNCT1) THEN
        SUBGOAL_THEN (Term`dsize D1 = SUC n`) (fn th => ASM_REWRITE_TAC[th]) THEN
        MATCH_MP_TAC LESS_EQUAL_ANTISYM THEN
        ASM_REWRITE_TAC[GSYM NOT_LESS] THEN REWRITE_TAC[NOT_LESS] THEN
        MATCH_MP_TAC LESS_OR THEN ASM_REWRITE_TAC[],
        ASM_REWRITE_TAC[SUB]],
 GEN_TAC THEN REWRITE_TAC[rsum] THEN
   SUBGOAL_THEN(Term`(dsize(\n. if n < dsize D1 then D1 n else D2(n- dsize D1))
      = dsize D1 + dsize D2)`)MP_TAC THENL
        [UNDISCH_TAC(Term`tdiv(a,b)(D1,p1)`) THEN
         UNDISCH_TAC(Term`tdiv(b,c)(D2,p2)`) THEN
         REWRITE_TAC[tdiv] THEN REPEAT STRIP_TAC THEN
         MP_TAC(SPECL [Term`a:real`, Term`b:real`, Term`c:real`,
                   Term`D1:num->real`, Term`D2:num->real`]
                                   DIVISION_APPEND_LEMMA2) THEN
         PROVE_TAC[],
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM SUM_SPLIT] THEN
        REWRITE_TAC[SUM_REINDEX] THEN BINOP_TAC THENL
         [MATCH_MP_TAC SUM_EQ THEN SIMP_TAC pure_ss[ADD_CLAUSES] THEN
          RW_TAC arith_ss[ETA_AX] THEN
          SUBGOAL_THEN(Term`dsize D1 = SUC r`)MP_TAC THENL
           [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[NOT_LESS] THEN
            REWRITE_TAC[LESS_EQ] THEN RW_TAC arith_ss[], DISCH_TAC THEN
                ASM_SIMP_TAC arith_ss[] THEN UNDISCH_TAC(Term`tdiv(a,b)(D1,p1)`) THEN
                UNDISCH_TAC(Term`tdiv(b,c)(D2,p2)`) THEN REWRITE_TAC[tdiv] THEN
                REWRITE_TAC[DIVISION_THM] THEN REPEAT STRIP_TAC THEN
                ASM_REWRITE_TAC[] THEN
                SUBGOAL_THEN(Term`D1(SUC r) - D1 r = D1(dsize D1) - D1 r`)MP_TAC THENL
                 [PROVE_TAC[], ASM_SIMP_TAC arith_ss[]]],
         ASM_SIMP_TAC arith_ss[GSYM ADD]]]]
QED

Theorem DIVISION_APPEND_STRONG :
    !a b c D1 p1 D2 p2.
        tdiv(a,b) (D1,p1) /\ fine(g) (D1,p1) /\
        tdiv(b,c) (D2,p2) /\ fine(g) (D2,p2)
        ==> ?D p. tdiv(a,c) (D,p) /\ fine(g) (D,p) /\
                  !f. rsum(D,p) f = rsum(D1,p1) f + rsum(D2,p2) f
Proof
  REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC
   [Term`\n. if n < dsize D1 then D1(n):real else D2(n - (dsize D1))`,
    Term`\n. if n < dsize D1 then p1(n):real else p2(n - (dsize D1))`] THEN
  MATCH_MP_TAC DIVISION_APPEND_EXPLICIT THEN ASM_MESON_TAC[]
QED

Theorem DIVISION_APPEND :
    !a b c.
      (?D1 p1. tdiv(a,b) (D1,p1) /\ fine(g) (D1,p1)) /\
      (?D2 p2. tdiv(b,c) (D2,p2) /\ fine(g) (D2,p2)) ==>
        ?D p. tdiv(a,c) (D,p) /\ fine(g) (D,p)
Proof
  MESON_TAC[DIVISION_APPEND_STRONG]
QED

(* ------------------------------------------------------------------------ *)
(* We can always find a division which is fine wrt any gauge                *)
(* ------------------------------------------------------------------------ *)

(* This is also called Cousin's theorem [1, p.11].
   cf. integrationTheory.FINE_DIVISION_EXISTS
 *)
Theorem DIVISION_EXISTS :
   !a b g. a <= b /\ gauge(\x. a <= x /\ x <= b) g
                ==>
                ?D p. tdiv(a,b) (D,p) /\ fine(g) (D,p)
Proof
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  (MP_TAC o C SPEC BOLZANO_LEMMA)
    (Term `\(u,v). a <= u /\ v <= b
                   ==> ?D p. tdiv(u,v) (D,p) /\ fine(g) (D,p)`) THEN
  CONV_TAC(ONCE_DEPTH_CONV PAIRED_BETA_CONV) THEN
  W(C SUBGOAL_THEN (fn t => REWRITE_TAC[t]) o
  funpow 2 (fst o dest_imp) o snd) THENL
   [CONJ_TAC,
    DISCH_THEN(MP_TAC o SPECL [Term`a:real`, Term`b:real`]) THEN
    REWRITE_TAC[REAL_LE_REFL]]
  THENL
   [MAP_EVERY X_GEN_TAC [Term`u:real`, Term`v:real`, Term`w:real`] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC DIVISION_APPEND THEN
    EXISTS_TAC (Term`v:real`) THEN CONJ_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (Term`w:real`),
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (Term`u:real`)] THEN
    ASM_REWRITE_TAC[], ALL_TAC] THEN
  X_GEN_TAC (Term`x:real`) THEN ASM_CASES_TAC (Term`a <= x /\ x <= b`) THENL
   [ALL_TAC,
    EXISTS_TAC (Term`&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
    MAP_EVERY X_GEN_TAC [Term`w:real`, Term`y:real`] THEN STRIP_TAC THEN
    CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
    FIRST_ASSUM(UNDISCH_TAC o assert is_neg o concl) THEN
    REWRITE_TAC[DE_MORGAN_THM, REAL_NOT_LE] THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [DISJ1_TAC THEN MATCH_MP_TAC REAL_LET_TRANS,
      DISJ2_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS] THEN
    EXISTS_TAC (Term`x:real`) THEN ASM_REWRITE_TAC[]] THEN
  UNDISCH_TAC (Term`gauge(\x. a <= x /\ x <= b) g`) THEN
  REWRITE_TAC[gauge] THEN BETA_TAC THEN
  DISCH_THEN(fn th => FIRST_ASSUM(ASSUME_TAC o MATCH_MP th)) THEN
  EXISTS_TAC (Term`(g:real->real) x`) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [Term`w:real`, Term`y:real`] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC (Term`\n:num. if (n = 0) then (w:real) else y`) THEN
  EXISTS_TAC (Term`\n:num. if (n = 0) then (x:real) else y`) THEN
  SUBGOAL_THEN (Term`w <= y`) ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (Term`x:real`) THEN
    ASM_REWRITE_TAC[], ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[tdiv] THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIVISION_SINGLE THEN FIRST_ASSUM ACCEPT_TAC,
      X_GEN_TAC (Term`n:num`) THEN BETA_TAC THEN REWRITE_TAC[NOT_SUC] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]],
    REWRITE_TAC[fine] THEN BETA_TAC THEN REWRITE_TAC[NOT_SUC] THEN
    X_GEN_TAC (Term`n:num`) THEN
    DISJ_CASES_THEN MP_TAC (REWRITE_RULE[REAL_LE_LT] (ASSUME(Term`w <= y`)))
    THENL
     [DISCH_THEN(ASSUME_TAC o MATCH_MP DIVISION_1) THEN
      ASM_REWRITE_TAC[num_CONV (Term`1:num`), LESS_THM, NOT_LESS_0] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[],
      DISCH_THEN(SUBST1_TAC o MATCH_MP DIVISION_0) THEN
      REWRITE_TAC[NOT_LESS_0]]]
QED

(* ------------------------------------------------------------------------- *)
(* Definition of integral and integrability.                                 *)
(* ------------------------------------------------------------------------- *)

val _ = hide "integrable";
Definition integrable :
    integrable(a,b) f = ?i. Dint(a,b) f i
End

val _ = hide "integral";
Definition integral :
    integral(a,b) f = @i. Dint(a,b) f i
End

val INTEGRABLE_DINT = store_thm("INTEGRABLE_DINT",
 “!f a b. integrable(a,b) f ==> Dint(a,b) f (integral(a,b) f)”,
  REPEAT GEN_TAC THEN REWRITE_TAC[integrable, integral] THEN
  CONV_TAC(RAND_CONV SELECT_CONV) THEN REWRITE_TAC[]);

(* ------------------------------------------------------------------------ *)
(* Lemmas about combining gauges                                            *)
(* ------------------------------------------------------------------------ *)

val GAUGE_MIN = store_thm("GAUGE_MIN",
  ``!E g1 g2. gauge(E) g1 /\ gauge(E) g2 ==>
        gauge(E) (\x. if g1(x) < g2(x) then g1(x) else g2(x))``,
  REPEAT GEN_TAC THEN REWRITE_TAC[gauge] THEN STRIP_TAC THEN
  X_GEN_TAC (Term`x:real`) THEN BETA_TAC THEN DISCH_TAC THEN
  COND_CASES_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  FIRST_ASSUM ACCEPT_TAC);;

val FINE_MIN = store_thm("FINE_MIN",
  ``!g1 g2 D p.
        fine (\x. if g1(x) < g2(x) then g1(x) else g2(x)) (D,p) ==>
        fine(g1) (D,p) /\ fine(g2) (D,p)``,
  REPEAT GEN_TAC THEN REWRITE_TAC[fine] THEN
  BETA_TAC THEN DISCH_TAC THEN CONJ_TAC THEN
  X_GEN_TAC (Term`n:num`) THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN DISCH_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LT]) THEN
    MATCH_MP_TAC REAL_LTE_TRANS,
    MATCH_MP_TAC REAL_LT_TRANS] THEN
  FIRST_ASSUM(fn th => EXISTS_TAC(rand(concl th)) THEN
                   ASM_REWRITE_TAC[] THEN NO_TAC));;

(* ------------------------------------------------------------------------ *)
(* The integral is unique if it exists                                      *)
(* ------------------------------------------------------------------------ *)

val DINT_UNIQ = store_thm("DINT_UNIQ",
 ``!a b f k1 k2.
        a <= b /\ Dint(a,b) f k1 /\ Dint(a,b) f k2 ==> (k1 = k2)``,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM REAL_SUB_0] THEN
  CONV_TAC CONTRAPOS_CONV THEN ONCE_REWRITE_TAC[ABS_NZ] THEN DISCH_TAC THEN
  REWRITE_TAC[Dint] THEN
  DISCH_THEN(CONJUNCTS_THEN(MP_TAC o SPEC (Term`abs(k1 - k2) / &2`))) THEN
  ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
  DISCH_THEN(X_CHOOSE_THEN (Term`g1:real->real`) STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN (Term`g2:real->real`) STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [Term`\x. a <= x /\ x <= b`,
                Term`g1:real->real`, Term`g2:real->real`] GAUGE_MIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [Term`a:real`, Term`b:real`,
                Term`\x:real. if g1(x) < g2(x) then g1(x) else g2(x)`]
         DIVISION_EXISTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN (Term`D:num->real`)
     (X_CHOOSE_THEN(Term`p:num->real`) STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP FINE_MIN) THEN
  REPEAT(FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPECL [Term`D:num->real`, Term`p:num->real`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC) THEN
  SUBGOAL_THEN (Term`abs((rsum(D,p) f - k2) - (rsum(D,p) f - k1))
                     < abs(k1 - k2)`) MP_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC (Term`abs(rsum(D,p) f - k2) + abs(rsum(D,p) f - k1)`) THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites [real_sub] THEN
      GEN_REWRITE_TAC (funpow 2 RAND_CONV) empty_rewrites [GSYM ABS_NEG] THEN
      MATCH_ACCEPT_TAC ABS_TRIANGLE,
      GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM REAL_HALF_DOUBLE] THEN
      MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC[]],
    REWRITE_TAC[real_sub, REAL_NEG_ADD, REAL_NEG_SUB] THEN
    ONCE_REWRITE_TAC[AC (REAL_ADD_ASSOC,REAL_ADD_SYM)
      (Term`(a + b) + (c + d) = (d + a) + (c + b)`)] THEN
    REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_LID, REAL_LT_REFL]]);

(* ------------------------------------------------------------------------- *)
(* Other more or less trivial lemmas.                                        *)
(* ------------------------------------------------------------------------- *)

val DIVISION_BOUNDS = store_thm("DIVISION_BOUNDS",
 “!d a b. division(a,b) d ==> !n. a <= d(n) /\ d(n) <= b”,
  MESON_TAC[DIVISION_UBOUND, DIVISION_LBOUND]);

val TDIV_BOUNDS = store_thm("TDIV_BOUNDS",
 “!d p a b. tdiv(a,b) (d,p)
             ==> !n. a <= d(n) /\ d(n) <= b /\ a <= p(n) /\ p(n) <= b”,
  REWRITE_TAC[tdiv] THEN ASM_MESON_TAC[DIVISION_BOUNDS, REAL_LE_TRANS]);

val TDIV_LE = store_thm("TDIV_LE",
 “!d p a b. tdiv(a,b) (d,p) ==> a <= b”,
  MESON_TAC[tdiv, DIVISION_LE]);

val DINT_WRONG = store_thm("DINT_WRONG",
 “!a b f i. b < a ==> Dint(a,b) f i”,
  REWRITE_TAC[Dint, gauge] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC “\x:real. &0” THEN
  ASM_SIMP_TAC std_ss[REAL_ARITH ``b < a ==> (a <= x /\ x <= b <=> F)``] THEN
  ASM_MESON_TAC[REAL_NOT_LE, TDIV_LE]);

val DINT_INTEGRAL = store_thm("DINT_INTEGRAL",
 “!f a b i. a <= b /\ Dint(a,b) f i ==> (integral(a,b) f = i)”,
  REPEAT STRIP_TAC THEN REWRITE_TAC[integral] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC[DINT_UNIQ]);

(* ------------------------------------------------------------------------- *)
(* Linearity.                                                                *)
(* ------------------------------------------------------------------------- *)

val DINT_NEG = store_thm("DINT_NEG",
 “!f a b i. Dint(a,b) f i ==> Dint(a,b) (\x. ~f x) (~i)”,
  REPEAT GEN_TAC THEN REWRITE_TAC[Dint] THEN
  SIMP_TAC arith_ss[rsum, REAL_MUL_LNEG, SUM_NEG] THEN
  SIMP_TAC arith_ss[REAL_SUB_LNEG, ABS_NEG, real_sub]);

val DINT_0 = store_thm("DINT_0",
 “!a b. Dint(a,b) (\x. &0) (&0)”,
  REPEAT GEN_TAC THEN REWRITE_TAC[Dint] THEN GEN_TAC THEN DISCH_TAC THEN
  EXISTS_TAC (Term`\x:real. &1`) THEN REWRITE_TAC[gauge,REAL_LT_01] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  REWRITE_TAC[rsum, REAL_MUL_LZERO, SUM_0, ABS_0] THEN RW_TAC arith_ss[]);

val DINT_ADD = store_thm("DINT_ADD",
“!f g a b i j.
        Dint(a,b) f i /\ Dint(a,b) g j
        ==> Dint(a,b) (\x. f x + g x) (i + j)”,
        REPEAT GEN_TAC THEN REWRITE_TAC[Dint] THEN STRIP_TAC THEN
        X_GEN_TAC (Term`e:real`) THEN DISCH_TAC THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC ``e / &2``)) THEN
        ASM_SIMP_TAC arith_ss[REAL_LT_DIV, REAL_LT] THEN
        DISCH_THEN(X_CHOOSE_THEN (Term`g1:real->real`) STRIP_ASSUME_TAC) THEN
        DISCH_THEN(X_CHOOSE_THEN (Term`g2:real->real`) STRIP_ASSUME_TAC) THEN
        EXISTS_TAC “\x:real. if g1(x) < g2(x) then g1(x) else g2(x)” THEN
        ASM_SIMP_TAC arith_ss[GAUGE_MIN, rsum] THEN REPEAT STRIP_TAC THEN
        SIMP_TAC arith_ss[REAL_ADD_RDISTRIB, SUM_ADD] THEN
        SIMP_TAC arith_ss[REAL_ADD2_SUB2] THEN REWRITE_TAC[GSYM rsum] THEN
        FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP FINE_MIN) THEN
        REPEAT(FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPECL [Term`D:num->real`, Term`p:num->real`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC) THEN
        SUBGOAL_THEN (Term`abs(rsum(D,p) f -i) + abs(rsum(D,p) g - j) < e`)
                MP_TAC THENL
         [GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM REAL_HALF_DOUBLE] THEN
          MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC[],
          STRIP_TAC THEN
          KNOW_TAC``abs (rsum (D,p) f - i + (rsum (D,p) g - j)) <=
          abs (rsum (D,p) f - i) + abs (rsum (D,p) g - j) /\ (abs (rsum (D,p) f - i) +
          abs (rsum (D,p) g - j)< e)`` THENL
           [CONJ_TAC THEN REWRITE_TAC[ABS_TRIANGLE], ASM_REWRITE_TAC[]]
            THEN PROVE_TAC [REAL_LET_TRANS]]);

val DINT_SUB = store_thm("DINT_SUB",
 “!f g a b i j.
        Dint(a,b) f i /\ Dint(a,b) g j
        ==> Dint(a,b) (\x. f x - g x) (i - j)”,
  SIMP_TAC arith_ss[real_sub, DINT_ADD, DINT_NEG]);

val DSIZE_EQ = store_thm("DSIZE_EQ",
“!a b D. division(a,b) D ==>
        (sum(0,dsize D)(\n. D(SUC n) - D n) - (b - a) = 0)”,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SIMP_TAC arith_ss[SUM_CANCEL] THEN
  RW_TAC arith_ss[REAL_SUB_0] THEN MP_TAC DIVISION_LHS THEN
  MP_TAC DIVISION_RHS THEN PROVE_TAC []);

val DINT_CONST = store_thm("DINT_CONST",
 “!a b c. Dint(a,b) (\x. c) (c * (b - a))”,
  REPEAT GEN_TAC THEN REWRITE_TAC[Dint] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC (Term`\x:real. &1`) THEN REWRITE_TAC[gauge,REAL_LT_01] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[rsum] THEN
  SIMP_TAC arith_ss[SUM_CMUL] THEN
  SIMP_TAC arith_ss[GSYM REAL_SUB_LDISTRIB] THEN REWRITE_TAC[ABS_MUL] THEN
  UNDISCH_TAC(Term`tdiv(a,b)(D,p)`) THEN REWRITE_TAC[tdiv] THEN
  STRIP_TAC THEN UNDISCH_TAC(Term`division(a,b) D`) THEN
  SIMP_TAC arith_ss[DSIZE_EQ] THEN REWRITE_TAC[ABS_0] THEN STRIP_TAC THEN
  RW_TAC arith_ss[REAL_MUL_RZERO]);

val DINT_CMUL = store_thm("DINT_CMUL",
“!f a b c i. Dint(a,b) f i ==> Dint(a,b) (\x. c * f x) (c * i)”,
  REPEAT GEN_TAC THEN ASM_CASES_TAC (Term`c = &0`) THENL
   [MP_TAC(SPECL [Term`a:real`, Term`b:real`, Term`c:real`] DINT_CONST) THEN
    ASM_SIMP_TAC arith_ss[REAL_MUL_LZERO],
        REWRITE_TAC[Dint] THEN STRIP_TAC THEN X_GEN_TAC(Term`e:real`) THEN
        DISCH_TAC THEN  FIRST_X_ASSUM(MP_TAC o SPEC “e / abs(c)”) THEN
        SUBGOAL_THEN(Term`0 < abs(c)`) MP_TAC THENL
         [UNDISCH_TAC(Term`c<>0`) THEN SIMP_TAC arith_ss[ABS_NZ],
          ASM_SIMP_TAC arith_ss[REAL_LT_DIV, REAL_LT] THEN STRIP_TAC THEN
          DISCH_THEN(X_CHOOSE_THEN (Term`g1:real->real`) STRIP_ASSUME_TAC) THEN
          EXISTS_TAC“g1:real->real” THEN ASM_SIMP_TAC arith_ss[] THEN
          REPEAT STRIP_TAC THEN REWRITE_TAC[rsum] THEN
          RW_TAC arith_ss[ETA_AX] THEN
          SUBGOAL_THEN“!a b c d. a*b*(c-d) = a*(b*(c-d))”
                (fn th => ONCE_REWRITE_TAC[GEN_ALL th]) THENL
           [RW_TAC arith_ss[GSYM REAL_MUL_ASSOC],
            SIMP_TAC arith_ss[SUM_CMUL] THEN
                SIMP_TAC arith_ss[GSYM REAL_SUB_LDISTRIB] THEN REWRITE_TAC[ABS_MUL] THEN
                REWRITE_TAC[GSYM rsum] THEN
                REPEAT(FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
                DISCH_THEN(MP_TAC o SPECL [Term`D:num->real`, Term`p:num->real`]) THEN
                ASM_REWRITE_TAC[] THEN DISCH_TAC) THEN
                POP_ASSUM MP_TAC THEN UNDISCH_TAC(Term`0 < abs c`) THEN
                RW_TAC arith_ss[REAL_LT_RDIV_EQ] THEN PROVE_TAC[REAL_MUL_SYM]]]]);

val DINT_LINEAR = store_thm("DINT_LINEAR",
  ``!f g a b i j.
        Dint(a,b) f i /\ Dint(a,b) g j
        ==> Dint(a,b) (\x. m*(f x) + n*(g x)) (m*i + n*j)``,
  REPEAT STRIP_TAC THEN HO_MATCH_MP_TAC DINT_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC DINT_CMUL THEN ASM_REWRITE_TAC[]);

(* ------------------------------------------------------------------------- *)
(* Ordering properties of integral.                                          *)
(* ------------------------------------------------------------------------- *)

Theorem INTEGRAL_LE :
    !f g a b i j.
        a <= b /\ integrable(a,b) f /\ integrable(a,b) g /\
        (!x. a <= x /\ x <= b ==> f(x) <= g(x))
        ==> integral(a,b) f <= integral(a,b) g
Proof
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP INTEGRABLE_DINT)) THEN
  MATCH_MP_TAC(REAL_ARITH ``~(&0 < x - y) ==> x <= y``) THEN
  ABBREV_TAC ``e = integral(a,b) f - integral(a,b) g`` THEN DISCH_TAC THEN
  NTAC 2(FIRST_X_ASSUM(MP_TAC o SPEC ``e / &2`` o REWRITE_RULE [Dint])) THEN
  ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
  DISCH_THEN(X_CHOOSE_THEN ``g1:real->real`` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN ``g2:real->real`` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [Term`\x. a <= x /\ x <= b`,
                                Term`g1:real->real`, Term`g2:real->real`] GAUGE_MIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [``a:real``, ``b:real``,
                ``\x:real. if g1(x) < g2(x) then g1(x) else g2(x)``]
               DIVISION_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN (Term`D:num->real`)
     (X_CHOOSE_THEN(Term`p:num->real`) STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP FINE_MIN) THEN
  REPEAT(FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPECL [Term`D:num->real`, Term`p:num->real`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC) THEN
  SUBGOAL_THEN (Term`abs((rsum(D,p) g - integral(a,b) g) -
                                (rsum(D,p) f - integral(a,b) f)) < e`) MP_TAC THENL
        [MATCH_MP_TAC REAL_LET_TRANS THEN
         EXISTS_TAC (Term`abs(rsum(D,p) g - integral(a,b) g) +
                                abs(rsum(D,p) f - integral(a,b) f)`) THEN
         CONJ_TAC THENL
          [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites [real_sub] THEN
           GEN_REWRITE_TAC (funpow 2 RAND_CONV) empty_rewrites [GSYM ABS_NEG] THEN
           MATCH_ACCEPT_TAC ABS_TRIANGLE,
           GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM REAL_HALF_DOUBLE] THEN
           MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC[]],
         REWRITE_TAC[real_sub, REAL_NEG_ADD, REAL_NEG_SUB] THEN
         ONCE_REWRITE_TAC[AC (REAL_ADD_ASSOC,REAL_ADD_SYM)
      (Term`(a + b) + (c + d) = (d + a) + (c + b)`)] THEN
         REWRITE_TAC[GSYM real_sub] THEN ASM_REWRITE_TAC[] THEN
         ONCE_REWRITE_TAC[GSYM ABS_NEG] THEN
         REWRITE_TAC[real_sub, REAL_NEG_ADD, REAL_NEGNEG] THEN
         REWRITE_TAC[GSYM real_sub] THEN DISCH_TAC THEN
         SUBGOAL_THEN``0<rsum(D,p) f - rsum(D,p) g``MP_TAC THENL
           [PROVE_TAC[ABS_SIGN], REWRITE_TAC[] THEN
            ONCE_REWRITE_TAC[REAL_NOT_LT] THEN REWRITE_TAC[real_sub] THEN
                ONCE_REWRITE_TAC[GSYM REAL_LE_RNEG] THEN REWRITE_TAC[REAL_NEGNEG] THEN
                REWRITE_TAC[rsum] THEN MATCH_MP_TAC SUM_LE THEN
                X_GEN_TAC``r:num`` THEN REWRITE_TAC[ADD_CLAUSES] THEN
                STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC REAL_LE_RMUL1 THEN
                REWRITE_TAC[REAL_SUB_LE] THEN
                ASM_MESON_TAC[TDIV_BOUNDS, REAL_LT_IMP_LE, DIVISION_THM, tdiv]]]
QED

val DINT_LE = store_thm("DINT_LE",
  ``!f g a b i j. a <= b /\ Dint(a,b) f i /\ Dint(a,b) g j /\
                 (!x. a <= x /\ x <= b ==> f(x) <= g(x))
                 ==> i <= j``,
  REPEAT GEN_TAC THEN MP_TAC(SPEC_ALL INTEGRAL_LE) THEN
  MESON_TAC[integrable, DINT_INTEGRAL]);

 val DINT_TRIANGLE = store_thm("DINT_TRIANGLE",
  ``!f a b i j. a <= b /\ Dint(a,b) f i /\ Dint(a,b) (\x. abs(f x)) j
               ==> abs(i) <= j``,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH``~a <= b /\ b <= a ==> abs(b) <= a``) THEN
  CONJ_TAC THEN MATCH_MP_TAC DINT_LE THENL
   [MAP_EVERY EXISTS_TAC [``\x:real. ~abs(f x)``, ``f:real->real``],
        MAP_EVERY EXISTS_TAC [``f:real->real``, ``\x:real. abs(f x)``]] THEN
        MAP_EVERY EXISTS_TAC [``a:real``, ``b:real``] THEN
        ASM_SIMP_TAC arith_ss[DINT_NEG] THEN REAL_ARITH_TAC);

val DINT_EQ = store_thm("DINT_EQ",
  ``!f g a b i j. a <= b /\ Dint(a,b) f i /\ Dint(a,b) g j /\
                 (!x. a <= x /\ x <= b ==> (f(x) = g(x)))
                 ==> (i = j)``,
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN MESON_TAC[DINT_LE]);

val INTEGRAL_EQ = store_thm("INTEGRAL_EQ",
  ``!f g a b i. Dint(a,b) f i /\
               (!x. a <= x /\ x <= b ==> (f(x) = g(x)))
               ==> Dint(a,b) g i``,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC ``a <= b`` THENL
   [UNDISCH_TAC``Dint(a,b) f i`` THEN REWRITE_TAC[Dint] THEN
        HO_MATCH_MP_TAC MONO_ALL THEN X_GEN_TAC ``e:real`` THEN
        ASM_CASES_TAC ``&0 < e`` THEN ASM_REWRITE_TAC[] THEN
        HO_MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ``d:real->real`` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        ASM_REWRITE_TAC[] THEN
        HO_MATCH_MP_TAC MONO_ALL THEN X_GEN_TAC ``D:num->real`` THEN
        HO_MATCH_MP_TAC MONO_ALL THEN X_GEN_TAC ``p:num->real`` THEN
        DISCH_THEN(fn th => STRIP_TAC THEN MP_TAC th) THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(REAL_ARITH ``(x = y) ==> (abs(x - i) < e) ==>
                                                                (abs(y - i) < e)``) THEN
        REWRITE_TAC[rsum] THEN MATCH_MP_TAC SUM_EQ THEN
        REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN BETA_TAC THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_MESON_TAC[tdiv, DIVISION_LBOUND, DIVISION_UBOUND,
                                        DIVISION_THM, REAL_LE_TRANS],
        ASM_MESON_TAC[REAL_NOT_LE, DINT_WRONG]]);

(* ------------------------------------------------------------------------ *)
(* Integral over a null interval is 0                                       *)
(* ------------------------------------------------------------------------ *)

Theorem INTEGRAL_NULL :
   !f a. Dint(a,a) f (&0)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[Dint] THEN GEN_TAC THEN
  DISCH_TAC THEN EXISTS_TAC (Term`\x:real. &1`) THEN
  REWRITE_TAC[gauge, REAL_LT_01] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[tdiv] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIVISION_EQ) THEN
  REWRITE_TAC[rsum] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[sum, REAL_SUB_REFL, ABS_0]
QED

(* ------------------------------------------------------------------------ *)
(* Fundamental theorem of calculus (Part I)                                 *)
(* ------------------------------------------------------------------------ *)

Theorem STRADDLE_LEMMA :
   !f f' a b e. (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x)) /\ &0 < e
    ==> ?g. gauge(\x. a <= x /\ x <= b) g /\
            !x u v. a <= u /\ u <= x /\
                    x <= v /\ v <= b /\ (v - u) < g(x)
                ==> abs((f(v) - f(u)) - (f'(x) * (v - u)))
                    <= e * (v - u)
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[gauge] THEN BETA_TAC THEN
  SUBGOAL_THEN
   (Term`!x. a <= x /\ x <= b ==>
        ?d. &0 < d /\
          !u v. u <= x /\ x <= v /\ (v - u) < d
                ==>
               abs((f(v) - f(u)) - (f'(x) * (v - u)))
               <= e * (v - u)`) MP_TAC THENL
   [ALL_TAC,
    FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(K ALL_TAC) THEN
    DISCH_THEN(MP_TAC o CONV_RULE
      ((ONCE_DEPTH_CONV RIGHT_IMP_EXISTS_CONV) THENC SKOLEM_CONV)) THEN
    DISCH_THEN(X_CHOOSE_THEN (Term`g:real->real`) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (Term`g:real->real`) THEN CONJ_TAC THENL
     [GEN_TAC THEN
      DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
      DISCH_THEN(fn th => REWRITE_TAC[th]),
      REPEAT STRIP_TAC THEN
      C SUBGOAL_THEN (fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th))
      (Term`a <= x /\ x <= b`) THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
         [EXISTS_TAC (Term`u:real`), EXISTS_TAC (Term`v:real`)] THEN
        ASM_REWRITE_TAC[],
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[]]]] THEN
  X_GEN_TAC (Term`x:real`) THEN
  DISCH_THEN(fn th => STRIP_ASSUME_TAC th THEN
    FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o C MATCH_MP th)) THEN
  REWRITE_TAC[diffl, LIM] THEN
  DISCH_THEN(MP_TAC o SPEC (Term`e / &2`)) THEN
  ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
  BETA_TAC THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN (Term`d:real`) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN (Term`!z. abs(z - x) < d ==>
        abs((f(z) - f(x)) - (f'(x) * (z - x)))
        <= (e / &2) * abs(z - x)`)
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_CASES_TAC (Term`&0 < abs(z - x)`) THENL
     [ALL_TAC,
      UNDISCH_TAC (Term`~(&0 < abs(z - x))`) THEN
      REWRITE_TAC[GSYM ABS_NZ, REAL_SUB_0] THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[REAL_SUB_REFL, REAL_MUL_RZERO, ABS_0, REAL_LE_REFL]] THEN
    DISCH_THEN(MP_TAC o CONJ (ASSUME (Term`&0 < abs(z - x)`))) THEN
    DISCH_THEN(curry op THEN (MATCH_MP_TAC REAL_LT_IMP_LE) o MP_TAC) THEN
    DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    FIRST_ASSUM(fn th => GEN_REWRITE_TAC LAND_CONV empty_rewrites
      [GSYM(MATCH_MP REAL_LT_RMUL th)]) THEN
    MATCH_MP_TAC (TAUT_CONV “(a <=> b) ==> a ==> b”) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM ABS_MUL] THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_SUB_RDISTRIB] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_SUB_ADD2] THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    ASM_REWRITE_TAC[ABS_NZ], ALL_TAC] THEN
  EXISTS_TAC (Term`d:real`) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN (Term`u <= v`) (DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT])
  THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (Term`x:real`) THEN
    ASM_REWRITE_TAC[],
    ALL_TAC,
    ASM_REWRITE_TAC[REAL_SUB_REFL, REAL_MUL_RZERO, ABS_0, REAL_LE_REFL]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC (Term`abs((f(v) - f(x)) - (f'(x) * (v - x))) +
                   abs((f(x) - f(u)) - (f'(x) * (x - u)))`) THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL[Term`(f(v) - f(x)) - (f'(x) * (v - x))`,
                 Term`(f(x) - f(u)) - (f'(x) * (x - u))`] ABS_TRIANGLE)
    THEN MATCH_MP_TAC(TAUT_CONV “(a <=> b) ==> a ==> b”) THEN
    AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[GSYM REAL_ADD2_SUB2] THEN
    REWRITE_TAC[REAL_SUB_LDISTRIB] THEN
    SUBGOAL_THEN (Term`!a b c. (a - b) + (b - c) = (a - c)`)
      (fn th => REWRITE_TAC[th]) THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[real_sub] THEN
    ONCE_REWRITE_TAC[AC (REAL_ADD_ASSOC,REAL_ADD_SYM)
      (Term`(a + b) + (c + d) = (b + c) + (a + d)`)] THEN
    REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_LID], ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM REAL_HALF_DOUBLE] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (Term`(e / &2) * abs(v - x)`) THEN CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[abs, REAL_SUB_LE] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (Term`v - u`) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_sub, REAL_LE_LADD] THEN
      ASM_REWRITE_TAC[REAL_LE_NEG],
      ASM_REWRITE_TAC[abs, REAL_SUB_LE] THEN REWRITE_TAC[real_div] THEN
      GEN_REWRITE_TAC LAND_CONV empty_rewrites [AC (REAL_MUL_ASSOC,REAL_MUL_SYM)
         (Term`(a * b) * c = (a * c) * b`)] THEN
     REWRITE_TAC[GSYM REAL_MUL_ASSOC,
        MATCH_MP REAL_LE_LMUL (ASSUME (Term`&0 < e`))] THEN
      SUBGOAL_THEN (Term`!x y. (x * inv(&2)) <= (y * inv(&2)) <=> x <= y`)
      (fn th => ASM_REWRITE_TAC[th, real_sub, REAL_LE_LADD, REAL_LE_NEG]) THEN
      REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      MATCH_MP_TAC REAL_INV_POS THEN
      REWRITE_TAC[REAL_LT, TWO, LESS_0]],
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (Term`(e / &2) * abs(x - u)`) THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites [real_sub] THEN
      ONCE_REWRITE_TAC[GSYM ABS_NEG] THEN
      REWRITE_TAC[REAL_NEG_ADD, REAL_NEG_SUB] THEN
      ONCE_REWRITE_TAC[REAL_NEG_RMUL] THEN
      REWRITE_TAC[REAL_NEG_SUB] THEN REWRITE_TAC[GSYM real_sub] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[ABS_SUB] THEN
      ASM_REWRITE_TAC[abs, REAL_SUB_LE] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (Term`v - u`) THEN
      ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[real_sub, REAL_LE_RADD],
      ASM_REWRITE_TAC[abs, REAL_SUB_LE] THEN REWRITE_TAC[real_div] THEN
      GEN_REWRITE_TAC LAND_CONV empty_rewrites [AC (REAL_MUL_ASSOC,REAL_MUL_SYM)
        (Term `(a * b) * c = (a * c) * b`)] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC,
        MATCH_MP REAL_LE_LMUL (ASSUME (Term`&0 < e`))] THEN
      SUBGOAL_THEN (Term`!x y. (x * inv(&2)) <= (y * inv(&2)) <=> x <= y`)
      (fn th => ASM_REWRITE_TAC[th, real_sub, REAL_LE_RADD, REAL_LE_NEG]) THEN
      REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      MATCH_MP_TAC REAL_INV_POS THEN
      REWRITE_TAC[REAL_LT, TWO, LESS_0]]]
QED

val FTC1 = store_thm("FTC1",
 Term `!f f' a b.
       a <= b /\ (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x))
        ==> Dint(a,b) f' (f(b) - f(a))`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC (Term`a <= b`) THEN REWRITE_TAC[REAL_LE_LT] THEN
  DISCH_THEN DISJ_CASES_TAC THENL
   [ALL_TAC, ASM_REWRITE_TAC[REAL_SUB_REFL, INTEGRAL_NULL]] THEN
  REWRITE_TAC[Dint] THEN X_GEN_TAC (Term`e:real`) THEN DISCH_TAC THEN
  SUBGOAL_THEN
    (Term`!e. &0 < e ==>
              ?g. gauge(\x. a <= x /\ x <= b) g /\
                  (!D p. tdiv(a,b)(D,p) /\ fine g(D,p)
                         ==>
                         (abs((rsum(D,p)f') - (f b - f a))) <= e)`)
  MP_TAC THENL
   [ALL_TAC,
    DISCH_THEN(MP_TAC o SPEC (Term`e / &2`)) THEN
    ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
    DISCH_THEN(X_CHOOSE_THEN (Term`g:real->real`) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (Term`g:real->real`) THEN ASM_REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN(fn th => FIRST_ASSUM(ASSUME_TAC o C MATCH_MP th)) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (Term`e / &2`) THEN
    ASM_REWRITE_TAC[REAL_LT_HALF2]] THEN
  UNDISCH_TAC (Term`&0 < e`) THEN DISCH_THEN(K ALL_TAC) THEN
  X_GEN_TAC (Term`e:real`) THEN DISCH_TAC THEN
  MP_TAC(SPECL [Term`f:real->real`, Term`f':real->real`,
    Term`a:real`, Term`b:real`, Term`e / (b - a)`] STRADDLE_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN (Term`&0 < e / (b - a)`) (fn th => REWRITE_TAC[th]) THENL
   [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_INV_POS THEN
    ASM_REWRITE_TAC[REAL_SUB_LT], ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN (Term`g:real->real`) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC (Term`g:real->real`) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [Term`D:num->real`, Term`p:num->real`] THEN
  REWRITE_TAC[tdiv] THEN STRIP_TAC THEN REWRITE_TAC[rsum] THEN
  SUBGOAL_THEN (Term`f b - f a = sum(0,dsize D)(\n. f(D(SUC n)) - f(D(n)))`)
  SUBST1_TAC THENL
   [MP_TAC(SPECL [Term`\n:num. (f:real->real)(D(n))`, Term`0:num`, Term`dsize D`]
      SUM_CANCEL) THEN BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    MAP_EVERY (IMP_RES_THEN SUBST1_TAC) [DIVISION_LHS, DIVISION_RHS] THEN
    REFL_TAC, ALL_TAC] THEN
  ONCE_REWRITE_TAC[ABS_SUB] THEN REWRITE_TAC[GSYM SUM_SUB] THEN BETA_TAC THEN
  LE_MATCH_TAC ABS_SUM THEN BETA_TAC THEN
  SUBGOAL_THEN (Term`e = sum(0,dsize D)
                            (\n. (e / (b - a)) * (D(SUC n) - D n))`)
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[SYM(BETA_CONV (Term`(\n. (D(SUC n) - D n)) n`))] THEN
    ASM_REWRITE_TAC[SUM_CMUL, SUM_CANCEL, ADD_CLAUSES] THEN
    MAP_EVERY (IMP_RES_THEN SUBST1_TAC) [DIVISION_LHS, DIVISION_RHS] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    REWRITE_TAC[REAL_SUB_0] THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
  MATCH_MP_TAC SUM_LE THEN X_GEN_TAC (Term`r:num`) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN BETA_TAC THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [IMP_RES_THEN (fn th => REWRITE_TAC[th]) DIVISION_LBOUND,
    IMP_RES_THEN (fn th => REWRITE_TAC[th]) DIVISION_UBOUND,
    UNDISCH_TAC (Term`fine(g)(D,p)`) THEN REWRITE_TAC[fine] THEN
    DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]);

(* ------------------------------------------------------------------------- *)
(* Integration by parts.                                                     *)
(* ------------------------------------------------------------------------- *)

val INTEGRATION_BY_PARTS = store_thm("INTEGRATION_BY_PARTS",
  ``!f g f' g' a b.
        a <= b /\
        (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x)) /\
        (!x. a <= x /\ x <= b ==> (g diffl g'(x))(x))
        ==> Dint(a,b) (\x. f'(x) * g(x) + f(x) * g'(x))
                        (f(b) * g(b) - f(a) * g(a))``,
  REPEAT STRIP_TAC THEN HO_MATCH_MP_TAC FTC1 THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[REAL_ARITH ``a + b * c = a + c * b``] THEN
  ASM_SIMP_TAC arith_ss[DIFF_MUL]);

(* ------------------------------------------------------------------------- *)
(* Various simple lemmas about divisions.                                    *)
(* ------------------------------------------------------------------------- *)

val DIVISION_LE_SUC = store_thm("DIVISION_LE_SUC",
 “!d a b. division(a,b) d ==> !n. d(n) <= d(SUC n)”,
  REWRITE_TAC[DIVISION_THM, GREATER_EQ] THEN
  MESON_TAC[LESS_CASES, LE, REAL_LE_REFL, REAL_LT_IMP_LE]);

Theorem DIVISION_MONO_LE:
  !d a b. division(a,b) d ==> !m n. m <= n ==> d(m) <= d(n)
Proof
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP DIVISION_LE_SUC) THEN
  SIMP_TAC arith_ss[LESS_EQ_EXISTS] THEN GEN_TAC THEN
  SIMP_TAC arith_ss[GSYM LEFT_FORALL_IMP_THM] THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES, REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  first_assum $ irule_at (Pat ‘_ <= d (SUC _)’) >>
  ASM_REWRITE_TAC[]
QED

val DIVISION_MONO_LE_SUC = store_thm("DIVISION_MONO_LE_SUC",
  ``!d a b. division(a,b) d ==> !n. d(n) <= d(SUC n)``,
  MESON_TAC[DIVISION_MONO_LE, LE, LESS_EQ_REFL]);

val DIVISION_DSIZE_LE = store_thm("DIVISION_DSIZE_LE",
  ``!a b d n. division(a,b) d /\ (d(SUC n) = d(n)) ==> (dsize d <= n)``,
  REWRITE_TAC[DIVISION_THM] THEN MESON_TAC[REAL_LT_REFL, NOT_LESS]);

val DIVISION_DSIZE_GE = store_thm("DIVISION_DSIZE_GE",
  ``!a b d n. division(a,b) d /\ d(n) < d(SUC n) ==> SUC n <= dsize d``,
  REWRITE_TAC[DIVISION_THM, GSYM LESS_EQ, GREATER_EQ] THEN
  MESON_TAC[REAL_LT_REFL, LE, NOT_LESS]);

val DIVISION_DSIZE_EQ = store_thm("DIVISION_DSIZE_EQ",
  ``!a b d n. division(a,b) d /\ (d(n) < d(SUC n)) /\ (d(SUC(SUC n)) = d(SUC n))
           ==> (dsize d = SUC n)``,
  REWRITE_TAC[EQ_LESS_EQ] THEN MESON_TAC[DIVISION_DSIZE_LE, DIVISION_DSIZE_GE]);

val DIVISION_DSIZE_EQ_ALT = store_thm("DIVISION_DSIZE_EQ_ALT",
  ``!a b d n. division(a,b) d /\ (d(SUC n) = d(n)) /\
             (!i. i < n ==> (d(i) < d(SUC i)))
             ==> (dsize d = n)``,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [SUBGOAL_THEN(Term`dsize d <=0 ==> (dsize d = 0)`)MP_TAC THENL
    [ASM_MESON_TAC[DIVISION_DSIZE_LE, DIVISION_DSIZE_GE, LE],
         MESON_TAC[DIVISION_DSIZE_LE]], REPEAT STRIP_TAC THEN
         REWRITE_TAC[EQ_LESS_EQ] THEN
         ASM_MESON_TAC[DIVISION_DSIZE_LE, DIVISION_DSIZE_GE, LT]]);

val DIVISION_INTERMEDIATE = store_thm("DIVISION_INTERMEDIATE",
  ``!d a b c. division(a,b) d /\ a <= c /\ c <= b
             ==> ?n. n <= dsize d /\ d(n) <= c /\ c <= d(SUC n)``,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC (Term`\n. n <= dsize d /\ (d:num->real)(n) <= c`) num_MAX) THEN
  DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
  SUBGOAL_THEN``(?x. (\n. n <= dsize d /\ d n <= c) x) /\
        (?M. !x. (\n. n <= dsize d /\ d n <= c) x ==> x <= M)``MP_TAC THENL
    [CONJ_TAC THEN BETA_TAC THENL
      [EXISTS_TAC``0:num`` THEN UNDISCH_TAC``division(a,b) d`` THEN
           REWRITE_TAC[DIVISION_THM] THEN STRIP_TAC THEN
           ASM_MESON_TAC[ZERO_LESS_EQ],
           EXISTS_TAC``dsize (d:num -> real)`` THEN
           X_GEN_TAC``x:num`` THEN STRIP_TAC],
     DISCH_TAC THEN ASM_REWRITE_TAC[] THEN HO_MATCH_MP_TAC MONO_EXISTS THEN
         X_GEN_TAC ``n:num`` THEN SIMP_TAC bool_ss[] THEN STRIP_TAC THEN
         FIRST_X_ASSUM(MP_TAC o SPEC ``SUC n``) THEN
         SUBGOAL_THEN``~(SUC n <= n)``ASSUME_TAC THENL
          [SIMP_TAC arith_ss[LESS_OR],
           CONV_TAC CONTRAPOS_CONV THEN
           REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
           ASM_SIMP_TAC arith_ss[REAL_LT_IMP_LE, GSYM LESS_EQ, LT_LE] THEN
           DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC``division(a,b) d`` THEN
           REWRITE_TAC[DIVISION_THM] THEN
           DISCH_THEN(MP_TAC o SPEC ``SUC(dsize d)`` o repeat CONJUNCT2) THEN
           REWRITE_TAC[GREATER_EQ, LE, LESS_EQ_REFL] THEN
           SUBGOAL_THEN``d(SUC (dsize d)) < b``ASSUME_TAC THENL
             [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC``c:real`` THEN
                  ASM_REWRITE_TAC[],
                  POP_ASSUM MP_TAC THEN REWRITE_TAC[REAL_LT_IMP_NE]]]]);

(* a variant of DIVISION_INTERMEDIATE for a < b *)
Theorem DIVISION_INTERMEDIATE' :
    !d a b c. division(a,b) d /\ a <= c /\ c <= b /\ a < b
          ==> ?n. n < dsize d /\ d(n) <= c /\ c <= d(SUC n)
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘d’, ‘a’, ‘b’, ‘c’] DIVISION_INTERMEDIATE)
 >> RW_TAC std_ss []
 >> ‘n < dsize d \/ n = dsize d’ by rw []
 >- (Q.EXISTS_TAC ‘n’ >> art [])
 >> Know ‘dsize d <> 0’
 >- (REWRITE_TAC [GSYM (MATCH_MP DIVISION_EQ (ASSUME “division (a,b) d”))] \\
     PROVE_TAC [REAL_LT_IMP_NE])
 >> DISCH_TAC
 >> ‘!n. n >= dsize d ==> d n = b’ by PROVE_TAC [DIVISION_THM]
 >> ‘d (SUC n) = b’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> Q.EXISTS_TAC ‘PRE n’
 >> ‘SUC (PRE n) = n’ by rw [SUC_PRE] >> POP_ORW
 >> ‘d n = b’ by rw []
 >> POP_ASSUM (rfs o wrap)
 >> ‘c = b’ by PROVE_TAC [REAL_LE_ANTISYM]
 >> POP_ASSUM (rfs o wrap)
 >> METIS_TAC [DIVISION_BOUNDS]
QED

(* ------------------------------------------------------------------------- *)
(* Combination of adjacent intervals (quite painful in the details).         *)
(* ------------------------------------------------------------------------- *)

val DINT_COMBINE = store_thm("DINT_COMBINE",
  ``!f a b c i j. a <= b /\ b <= c /\ (Dint(a,b) f i) /\ (Dint(b,c) f j)
                 ==> (Dint(a,c) f (i + j))``,
  REPEAT GEN_TAC THEN
  NTAC 2(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MP_TAC(ASSUME “a <= b”) THEN REWRITE_TAC[REAL_LE_LT] THEN
  ASM_CASES_TAC “a:real = b” THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[INTEGRAL_NULL, DINT_UNIQ, REAL_LE_TRANS, REAL_ADD_LID],
    DISCH_TAC] THEN
  MP_TAC(ASSUME “b <= c”) THEN REWRITE_TAC[REAL_LE_LT] THEN
  ASM_CASES_TAC “b:real = c” THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[INTEGRAL_NULL, DINT_UNIQ, REAL_LE_TRANS, REAL_ADD_RID],
    DISCH_TAC] THEN
  SIMP_TAC arith_ss[Dint, GSYM FORALL_AND_THM] THEN
  DISCH_THEN(fn th => X_GEN_TAC “e:real” THEN DISCH_TAC THEN MP_TAC th) THEN
  DISCH_THEN(MP_TAC o SPEC “e / &2”) THEN
  ASM_SIMP_TAC arith_ss[REAL_LT_DIV, REAL_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN “g1:real->real” STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN “g2:real->real” STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC
   “\x. if x < b then min (g1 x) (b - x)
        else if b < x then min (g2 x) (x - b)
        else min (g1 x) (g2 x)” THEN
  CONJ_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[gauge])) THEN
    REWRITE_TAC[gauge] THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
        REPEAT COND_CASES_TAC THEN
        ASM_SIMP_TAC arith_ss[REAL_LT_MIN, REAL_SUB_LT] THEN
        TRY CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_SIMP_TAC arith_ss[REAL_LT_IMP_LE,real_lte], ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [Term`d:num->real`, Term`p:num->real`] THEN
  REWRITE_TAC[tdiv, rsum] THEN STRIP_TAC THEN
  MP_TAC(SPECL [Term`d:num->real`, Term`a:real`, Term`c:real`,
                                Term`b:real`]DIVISION_INTERMEDIATE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN ``m:num``
   (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
   REWRITE_TAC[LESS_EQ_EXISTS] THEN
   DISCH_THEN(X_CHOOSE_TAC ``n:num``) THEN ASM_REWRITE_TAC[] THEN
   ASM_CASES_TAC ``(n:num) = 0`` THENL
    [FIRST_X_ASSUM SUBST_ALL_TAC THEN
         RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
         FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
         ASM_MESON_TAC[DIVISION_THM, GREATER_EQ, LESS_EQ_REFL, REAL_NOT_LT],
         ALL_TAC] THEN
        REWRITE_TAC[GSYM SUM_SPLIT, ADD_CLAUSES] THEN
        SUBGOAL_THEN``n= 1 + PRE n``ASSUME_TAC THENL
         [ASM_SIMP_TAC arith_ss[PRE_SUB1], ALL_TAC] THEN
        ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM SUM_SPLIT, SUM_1] THEN
        BETA_TAC THEN
        SUBGOAL_THEN ``(p:num->real) m = b`` ASSUME_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o SPEC ``m:num`` o REWRITE_RULE [fine]) THEN
          SUBGOAL_THEN``m < dsize d``ASSUME_TAC THENL
           [ONCE_ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LESS_ADD_NONZERO THEN
            ASM_REWRITE_TAC[],ALL_TAC] THEN
           ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPEC ``m:num``) THEN
           MAP_EVERY UNDISCH_TAC [``(d:num->real) m <= b``,
                                                          ``b:real <= d(SUC m)``] THEN BETA_TAC THEN
           REPEAT STRIP_TAC THEN
           SUBGOAL_THEN``(d:num->real)(SUC m) - d m <
                                min((g1:real->real)(p m)) (g2(p m))``MP_TAC THENL
            [POP_ASSUM MP_TAC THEN RW_TAC std_ss[] THEN
                 POP_ASSUM MP_TAC THEN CONV_TAC CONTRAPOS_CONV THEN DISCH_TAC THEN
                 REWRITE_TAC[GSYM real_lte,REAL_MIN_LE] THEN DISJ2_TAC THEN
                 REWRITE_TAC[real_sub] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
                 ASM_REWRITE_TAC[REAL_LE_NEG],ALL_TAC] THEN
             POP_ASSUM MP_TAC THEN RW_TAC std_ss[] THENL
              [UNDISCH_TAC``(d:num->real) (SUC m) - d m <
                                min ((g1:real->real) (p m)) (b - p m)`` THEN
                   CONV_TAC CONTRAPOS_CONV THEN DISCH_TAC THEN
                   REWRITE_TAC[GSYM real_lte,REAL_MIN_LE] THEN DISJ2_TAC THEN
                   REWRITE_TAC[real_sub] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
                   ASM_REWRITE_TAC[REAL_LE_NEG],
                   UNDISCH_TAC``(d:num->real) (SUC m) - d m <
                                min ((g2:real->real) (p m)) (p m - b)``THEN
           CONV_TAC CONTRAPOS_CONV THEN DISCH_TAC THEN
                   REWRITE_TAC[GSYM real_lte,REAL_MIN_LE] THEN DISJ2_TAC THEN
                   REWRITE_TAC[real_sub] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
                   ASM_REWRITE_TAC[REAL_LE_NEG],
                   ASM_SIMP_TAC arith_ss[GSYM REAL_LE_ANTISYM,real_lte]],ALL_TAC] THEN
        ONCE_ASM_REWRITE_TAC[] THEN SIMP_TAC arith_ss[PRE_SUB1] THEN
        REWRITE_TAC[GSYM PRE_SUB1] THEN
        ABBREV_TAC``s1 = sum(0,m)(\n.
                                (f:real->real)((p:num->real) n) * (d(SUC n) - d n))`` THEN
    ABBREV_TAC``s2 = sum(m + 1, PRE n)
                (\n. (f:real->real)((p:num->real) n) * (d(SUC n) - d n))`` THEN
        ONCE_REWRITE_TAC[REAL_ARITH
    ``(s1 + (f b * (d (SUC m) - d m) + s2) - (i + j)) =
      (s1 + (f b * (b - d m)) - i) + (s2 + (f b * (d(SUC m) - b)) - j)``] THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC``abs((s1 + f b * (b - d m)) - i) +
                          abs((s2 + f b * (d(SUC m) - b)) - j)`` THEN
        REWRITE_TAC[REAL_ABS_TRIANGLE] THEN
        GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM REAL_HALF_DOUBLE] THEN
        MATCH_MP_TAC REAL_LT_ADD2 THEN CONJ_TAC THENL
         [UNDISCH_TAC
      ``!D p. tdiv(a,b) (D,p) /\ fine g1 (D,p)
            ==> abs(rsum(D,p) f - i) < e / &2`` THEN
          DISCH_THEN(MP_TAC o SPEC ``\i.
                        if i <= m then (d:num->real)(i) else b``) THEN
          DISCH_THEN(MP_TAC o SPEC ``\i.
                        if i <= m then (p:num->real)(i) else b``) THEN
          MATCH_MP_TAC(TAUT_CONV ``a /\ (a ==> b) /\ (a /\ c ==> d)
                       ==> (a /\ b ==> c) ==> d``) THEN
          CONJ_TAC THENL
           [REWRITE_TAC[tdiv, division] THEN REPEAT CONJ_TAC THENL
             [BETA_TAC THEN REWRITE_TAC[LE_0] THEN ASM_MESON_TAC[division],
                  ASM_CASES_TAC ``(d:num->real) m = b`` THENL
                   [EXISTS_TAC ``m:num`` THEN
                    SIMP_TAC arith_ss[ARITH_CONV ``n < m ==> n <= m /\ SUC n <= m``] THEN
                        CONJ_TAC THENL
                         [UNDISCH_TAC``division(a,c) d`` THEN REWRITE_TAC[DIVISION_THM] THEN
                          STRIP_TAC THEN ASM_MESON_TAC[ARITH_CONV``(i:num) < m ==> i < m + n``],
                          RW_TAC arith_ss[] THEN SUBGOAL_THEN``(n':num) = m``ASSUME_TAC THENL
                           [ASM_SIMP_TAC arith_ss[REAL_LE_ANTISYM], ASM_SIMP_TAC arith_ss[]]],
                          EXISTS_TAC ``SUC m`` THEN
                          SIMP_TAC arith_ss[ARITH_CONV ``n >= SUC m ==> ~(n <= m)``] THEN
                          RW_TAC arith_ss[] THENL
                           [UNDISCH_TAC``division(a,c) d`` THEN
                            REWRITE_TAC[DIVISION_THM] THEN STRIP_TAC THEN
                            SUBGOAL_THEN``(n':num) < dsize d``ASSUME_TAC THENL
                             [MATCH_MP_TAC LESS_LESS_EQ_TRANS THEN EXISTS_TAC``m:num`` THEN
                              CONJ_TAC THENL
                                   [MATCH_MP_TAC OR_LESS THEN ASM_REWRITE_TAC[],
                                    ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC [LESS_EQ_ADD]],
                                   ASM_SIMP_TAC arith_ss[]],
                            SUBGOAL_THEN``(n':num) = m``ASSUME_TAC THENL
                             [ASM_SIMP_TAC arith_ss[],ONCE_ASM_REWRITE_TAC[] THEN
                              ONCE_REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[]]]],
                BETA_TAC THEN GEN_TAC THEN RW_TAC std_ss[] THENL
                 [REWRITE_TAC[REAL_LE_REFL],
                  SUBGOAL_THEN``(n':num) = m``ASSUME_TAC THENL
                   [ASM_SIMP_TAC arith_ss[],
                    MATCH_MP_TAC REAL_EQ_IMP_LE THEN RW_TAC arith_ss[]],
                  SUBGOAL_THEN``~(SUC n' <= m)``ASSUME_TAC THENL
                   [RW_TAC arith_ss[],ASM_MESON_TAC[]],
                  REWRITE_TAC[REAL_LE_REFL]]],ALL_TAC] THEN
          CONJ_TAC THENL
          [REWRITE_TAC[tdiv, fine] THEN BETA_TAC THEN
           STRIP_TAC THEN X_GEN_TAC ``k:num`` THEN
           UNDISCH_TAC``fine
                (\x.
                        if x < b then
                          min (g1 x) (b - x)
                        else if b < x then
                          min (g2 x) (x - b)
                        else
                          min (g1 x) (g2 x)) (d,p)`` THEN REWRITE_TAC[fine] THEN
          DISCH_THEN(MP_TAC o SPEC ``k:num``) THEN MATCH_MP_TAC MONO_IMP THEN
          ASM_CASES_TAC ``k:num = m`` THENL
           [ASM_SIMP_TAC arith_ss[LESS_EQ_REFL, REAL_LT_REFL] THEN DISCH_TAC THEN
            MATCH_MP_TAC REAL_LET_TRANS THEN
                EXISTS_TAC``(d:num->real) (SUC m) - d m`` THEN CONJ_TAC THENL
                 [REWRITE_TAC[real_sub] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
                  ASM_REWRITE_TAC[REAL_LE_REFL],
                  MATCH_MP_TAC REAL_LTE_TRANS THEN
                  EXISTS_TAC``min ((g1:real->real) b) ((g2:real->real) b)`` THEN
                  ASM_REWRITE_TAC[REAL_MIN_LE1]],ALL_TAC] THEN
          ASM_CASES_TAC ``k:num <= m`` THEN ONCE_ASM_REWRITE_TAC[] THENL
           [ASM_SIMP_TAC arith_ss[] THEN
            SUBGOAL_THEN ``(p:num->real) k <= b`` MP_TAC THENL
            [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC ``(d:num->real) m`` THEN
                 ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
                 EXISTS_TAC ``(d:num->real) (SUC k)`` THEN ASM_REWRITE_TAC[] THEN
                 ASM_MESON_TAC[DIVISION_MONO_LE, ARITH_CONV
                                ``k <= m /\ ~(k = m) ==> SUC k <= m``],ALL_TAC] THEN
                 COND_CASES_TAC THENL
                  [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
                   EXISTS_TAC``min ((g1 :real -> real)
                                        ((p :num -> real) k)) ((b :real) - p k)`` THEN
                   ASM_SIMP_TAC arith_ss[REAL_MIN_LE1],
                   DISCH_TAC THEN
                   SUBGOAL_THEN``(p :num -> real) k = b``ASSUME_TAC THENL
                   [ASM_SIMP_TAC arith_ss[REAL_ARITH
                                ``~(a < b) /\ (a <= b) ==> (a = b)``],
                        ASM_SIMP_TAC arith_ss[REAL_LT_REFL] THEN DISCH_TAC THEN
                        MATCH_MP_TAC REAL_LTE_TRANS THEN
                        EXISTS_TAC``min ((g1 :real -> real) b) (g2 b)`` THEN
                        ASM_SIMP_TAC arith_ss[REAL_MIN_LE1]]],ALL_TAC] THEN
                        CONJ_TAC THENL
                         [DISCH_TAC THEN
                          SUBGOAL_THEN``dsize
                                (\(i :num). if i <= (m :num) then (d :num -> real) i
                                        else (b :real)) <=  SUC (m:num)``MP_TAC THENL
                           [MATCH_MP_TAC DIVISION_DSIZE_LE THEN
                            MAP_EVERY EXISTS_TAC [``a:real``, ``b:real``] THEN
                            ASM_REWRITE_TAC[] THEN SIMP_TAC arith_ss[],
                            ASM_SIMP_TAC arith_ss[]],
                          UNDISCH_TAC ``gauge (\x. a <= x /\ x <= b) g1`` THEN
                          ASM_SIMP_TAC arith_ss[REAL_SUB_REFL, gauge, REAL_LE_REFL]],
          ALL_TAC] THEN
          DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
          HO_MATCH_MP_TAC(REAL_ARITH
                ``(x = y) ==> abs(x - i) < e ==> abs(y - i) < e``) THEN
          REWRITE_TAC[rsum] THEN ASM_CASES_TAC ``(d:num->real) m = b`` THENL
           [SUBGOAL_THEN ``dsize (\i. if i <= m then d i else b) = m`` ASSUME_TAC THENL
            [MATCH_MP_TAC DIVISION_DSIZE_EQ_ALT THEN
                 MAP_EVERY EXISTS_TAC [``a:real``, ``b:real``] THEN CONJ_TAC THENL
                  [ASM_MESON_TAC[tdiv], ALL_TAC] THEN
                 BETA_TAC THEN
                 ASM_SIMP_TAC arith_ss[LESS_EQ_REFL, ARITH_CONV ``~(SUC m <= m)``] THEN
                 UNDISCH_TAC``division (a,c) d`` THEN REWRITE_TAC[DIVISION_THM] THEN
                 ONCE_ASM_REWRITE_TAC[] THEN
                 MESON_TAC[ARITH_CONV ``i < m:num ==> i < m + n``], ALL_TAC] THEN
                ONCE_ASM_REWRITE_TAC[] THEN
                ASM_SIMP_TAC arith_ss[REAL_SUB_REFL, REAL_MUL_RZERO, REAL_ADD_RID] THEN
                UNDISCH_TAC``sum (0,m) (\n. (f:real->real) (p n) *
                                        ((d:num->real) (SUC n) - d n)) = s1`` THEN
                CONV_TAC(LAND_CONV SYM_CONV) THEN SIMP_TAC arith_ss[] THEN
                DISCH_TAC THEN MATCH_MP_TAC SUM_EQ THEN
                SIMP_TAC arith_ss[ADD_CLAUSES, LESS_IMP_LESS_OR_EQ, GSYM LESS_EQ],
                ALL_TAC] THEN
                SUBGOAL_THEN ``dsize (\i. if i <= m then d i else b) = SUC m``
                        ASSUME_TAC THENL
                 [MATCH_MP_TAC DIVISION_DSIZE_EQ THEN
                  MAP_EVERY EXISTS_TAC [``a:real``, ``b:real``] THEN CONJ_TAC THENL
                   [ASM_MESON_TAC[tdiv],
                    BETA_TAC THEN
                        ASM_SIMP_TAC arith_ss[LESS_EQ_REFL, ARITH_CONV ``~(SUC m <= m)``] THEN
                        ASM_REWRITE_TAC[REAL_LT_LE]],ALL_TAC] THEN
                ASM_SIMP_TAC arith_ss[sum, ADD_CLAUSES, LESS_EQ_REFL,
                      ARITH_CONV ``~(SUC m <= m)``] THEN
                UNDISCH_TAC``sum (0,m) (\n. (f:real->real) (p n) *
                                ((d:num->real) (SUC n) - d n)) = s1`` THEN
                CONV_TAC(LAND_CONV SYM_CONV) THEN SIMP_TAC arith_ss[] THEN
                DISCH_TAC THEN ONCE_REWRITE_TAC[REAL_EQ_RADD] THEN
                MATCH_MP_TAC SUM_EQ THEN
                SIMP_TAC arith_ss[ADD_CLAUSES, LESS_IMP_LESS_OR_EQ, GSYM LESS_EQ],
          ALL_TAC] THEN
        ASM_CASES_TAC ``d(SUC m):real = b`` THEN ASM_REWRITE_TAC[] THENL
         [ASM_REWRITE_TAC[REAL_SUB_REFL, REAL_MUL_RZERO, REAL_ADD_RID] THEN
          UNDISCH_TAC``sum (m + 1,PRE n)
                        (\n. (f:real->real) ((p:num->real) n) *
                                ((d:num->real) (SUC n) - d n)) = s2`` THEN
          CONV_TAC(LAND_CONV SYM_CONV) THEN SIMP_TAC arith_ss[] THEN DISCH_TAC THEN
          UNDISCH_TAC
                ``!D p. tdiv(b,c) (D,p) /\ fine g2 (D,p)
            ==> abs(rsum(D,p) f - j) < e / &2`` THEN
          DISCH_THEN(MP_TAC o SPEC ``\i. (d:num->real) (i + SUC m)``) THEN
          DISCH_THEN(MP_TAC o SPEC ``\i. (p:num->real) (i + SUC m)``) THEN
          MATCH_MP_TAC(TAUT_CONV ``a /\ (a ==> b /\ (b /\ c ==> d))
                       ==> (a /\ b ==> c) ==> d``) THEN
          CONJ_TAC THENL
           [ASM_SIMP_TAC arith_ss[tdiv, division, ADD_CLAUSES] THEN
            EXISTS_TAC ``PRE n`` THEN
                UNDISCH_TAC``division(a,c) d`` THEN REWRITE_TAC[DIVISION_THM] THEN
                ASM_MESON_TAC[ARITH_CONV
                     ``~(n = 0) /\ k < PRE n ==> SUC(k + m) < m + n``,
                    ARITH_CONV
                     ``~(n = 0) /\ k >= PRE n ==> SUC(k + m) >= m + n``],
                 DISCH_TAC] THEN
                SUBGOAL_THEN ``dsize(\i. d (i + SUC m)) = PRE n`` ASSUME_TAC THENL
                 [MATCH_MP_TAC DIVISION_DSIZE_EQ_ALT THEN
                  MAP_EVERY EXISTS_TAC [``b:real``, ``c:real``] THEN
                  CONJ_TAC THENL
                   [ASM_MESON_TAC[tdiv],
                    BETA_TAC THEN SIMP_TAC arith_ss[] THEN
                    UNDISCH_TAC``division(a,c) d`` THEN REWRITE_TAC[DIVISION_THM] THEN
                    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
                    ASM_SIMP_TAC arith_ss[ADD_CLAUSES]],ALL_TAC] THEN
                CONJ_TAC THENL
                 [ASM_SIMP_TAC arith_ss[fine] THEN X_GEN_TAC ``k:num`` THEN
                  DISCH_TAC THEN
                  UNDISCH_TAC``fine
                                                (\x.
                                                        if x < b then
                                                          min ((g1:real->real) x) (b - x)
                                                        else if b < x then
                                                          min ((g2:real->real) x) (x - b)
                                                        else
                                                          min (g1 x) (g2 x)) (d,p)`` THEN
                  REWRITE_TAC[fine] THEN DISCH_THEN(MP_TAC o SPEC ``k + SUC m``) THEN
                  UNDISCH_TAC ``b <= d (SUC m)`` THEN
                  ASM_SIMP_TAC arith_ss[ADD_CLAUSES] THEN REWRITE_TAC[REAL_LE_REFL] THEN
                  MATCH_MP_TAC(REAL_ARITH ``b <= a ==> x < b ==> x < a``) THEN
                  SUBGOAL_THEN ``~(p(SUC (k + m)) < b)``ASSUME_TAC THENL
                   [RW_TAC arith_ss[GSYM real_lte] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
                    EXISTS_TAC``(d:num->real)(SUC (k + m))`` THEN CONJ_TAC THENL
                         [SUBGOAL_THEN``SUC m <= SUC (k+m)``MP_TAC THENL
                           [SIMP_TAC arith_ss[], MATCH_MP_TAC DIVISION_MONO_LE THEN
                            MAP_EVERY EXISTS_TAC [``a:real``, ``c:real``] THEN
                                ASM_REWRITE_TAC[]],
                          UNDISCH_TAC``tdiv (d (SUC m),c)
                                        ((\i. d (i + SUC m)),(\i. p (i + SUC m)))`` THEN
                          REWRITE_TAC[tdiv] THEN BETA_TAC THEN STRIP_TAC THEN
                          ASM_SIMP_TAC arith_ss[]],ASM_SIMP_TAC arith_ss[]] THEN
                      RW_TAC arith_ss[] THENL
                        [REWRITE_TAC[REAL_MIN_LE1],REWRITE_TAC[REAL_MIN_LE2]],ALL_TAC] THEN
                REWRITE_TAC[rsum] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
                SUBGOAL_THEN``(m:num) + 1 = 0 + SUC m``ASSUME_TAC THENL
                 [SIMP_TAC arith_ss[],ALL_TAC] THEN
                ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUM_REINDEX] THEN
                SIMP_TAC arith_ss[PRE_SUB1] THEN
                SIMP_TAC arith_ss[ADD1, ADD_CLAUSES],ALL_TAC] THEN
        UNDISCH_TAC
                ``!D p. tdiv(b,c) (D,p) /\ fine g2 (D,p)
          ==> abs(rsum(D,p) f - j) < e / &2`` THEN
        DISCH_THEN(MP_TAC o SPEC ``\i. if i = 0 then (b:real)
                                else (d:num->real)(i + m)``) THEN
        DISCH_THEN(MP_TAC o SPEC ``\i. if i = 0 then (b:real)
                                else (p:num->real)(i + m)``) THEN
        MATCH_MP_TAC(TAUT_CONV ``a /\ (a ==> b /\ (b /\ c ==> d))
                     ==> (a /\ b ==> c) ==> d``) THEN
        CONJ_TAC THENL
         [SIMP_TAC arith_ss[tdiv, division, ADD_CLAUSES] THEN CONJ_TAC THENL
          [EXISTS_TAC ``n:num`` THEN UNDISCH_TAC``division(a,c) d`` THEN
           REWRITE_TAC[DIVISION_THM] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
           MATCH_MP_TAC MONO_AND THEN ASM_SIMP_TAC arith_ss[] THEN
           DISCH_THEN(fn th =>
                        X_GEN_TAC ``k:num`` THEN MP_TAC(SPEC ``k + m:num`` th)) THEN
           ASM_CASES_TAC ``k:num < n`` THENL
            [ASM_SIMP_TAC arith_ss[ARITH_CONV
                                                                ``(k + (m:num) < m + n) = (k < n)``] THEN
                 COND_CASES_TAC THENL
                  [ASM_SIMP_TAC arith_ss[ADD_CLAUSES,REAL_LT_LE],REWRITE_TAC[]],
                 ASM_SIMP_TAC arith_ss[ADD_CLAUSES]],ALL_TAC] THEN
                GEN_TAC THEN COND_CASES_TAC THENL
                 [ASM_SIMP_TAC arith_ss[REAL_LE_REFL],
                  ASM_SIMP_TAC arith_ss[REAL_LE_REFL]], ALL_TAC] THEN DISCH_TAC THEN
        SUBGOAL_THEN ``dsize(\i. if i = 0 then b else d (i + m)) = n``
                                ASSUME_TAC THENL
         [MATCH_MP_TAC DIVISION_DSIZE_EQ_ALT THEN
          MAP_EVERY EXISTS_TAC [``b:real``, ``c:real``] THEN
          CONJ_TAC THENL [ASM_MESON_TAC[tdiv],ALL_TAC] THEN BETA_TAC THEN
          UNDISCH_TAC``division(a,c) d`` THEN REWRITE_TAC[DIVISION_THM] THEN
          DISCH_THEN(MP_TAC o CONJUNCT2) THEN ONCE_ASM_REWRITE_TAC[ADD_CLAUSES] THEN
          GEN_REWRITE_TAC RAND_CONV empty_rewrites [CONJ_SYM] THEN
          MATCH_MP_TAC MONO_AND THEN
          CONJ_TAC THENL
           [DISCH_THEN(fn th =>
                        X_GEN_TAC ``k:num`` THEN MP_TAC(SPEC ``k + (m:num)`` th)) THEN
                ASM_CASES_TAC ``(k:num) < n`` THENL
                 [ASM_SIMP_TAC arith_ss[ARITH_CONV ``(k + (m:num) < m + n) = (k < n)``] THEN
                  COND_CASES_TAC THEN ASM_SIMP_TAC arith_ss[ADD_CLAUSES] THEN
                  ASM_SIMP_TAC arith_ss[REAL_LT_LE],
                  ASM_SIMP_TAC arith_ss[]], ASM_SIMP_TAC arith_ss[]],ALL_TAC] THEN
        CONJ_TAC THENL
         [ASM_SIMP_TAC arith_ss[fine] THEN X_GEN_TAC ``k:num`` THEN DISCH_TAC THEN
          UNDISCH_TAC``fine
                                        (\x.
                                                if x < b then
                                                  min ((g1:real->real) x) (b - x)
                                                else if b < x then
                                                  min ((g2:real->real) x) (x - b)
                                                else
                                                  min (g1 x) (g2 x)) (d,p)`` THEN REWRITE_TAC[fine] THEN
          DISCH_THEN(MP_TAC o SPEC ``k + m:num``) THEN
          ASM_SIMP_TAC arith_ss[ADD_CLAUSES,ARITH_CONV
                                                        ``(k + m < m + n) = ((k:num) < n)``] THEN
          ASM_CASES_TAC ``(k:num) = 0`` THENL
           [ASM_SIMP_TAC arith_ss[ADD_CLAUSES, REAL_LT_REFL] THEN DISCH_TAC THEN
            MATCH_MP_TAC REAL_LTE_TRANS THEN
                EXISTS_TAC``min (g1 b) ((g2:real->real) b)`` THEN
                REWRITE_TAC[REAL_MIN_LE2] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
                EXISTS_TAC``(d:num->real) (SUC m) - d m`` THEN
                ASM_SIMP_TAC arith_ss[] THEN
                ASM_REWRITE_TAC[real_sub,REAL_LE_LADD,REAL_LE_NEG2],ALL_TAC] THEN
          ASM_SIMP_TAC arith_ss[] THEN
          MATCH_MP_TAC(REAL_ARITH ``b <= a ==> x < b ==> x < a``) THEN
          SUBGOAL_THEN ``~((p:num->real) (k + m) < b)``ASSUME_TAC THENL
           [RW_TAC arith_ss[GSYM real_lte] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
            EXISTS_TAC``(d:num->real)(SUC m)`` THEN ASM_SIMP_TAC arith_ss[] THEN
                MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC``(d:num->real) (k + m)`` THEN
                CONJ_TAC THENL
                 [FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVISION_MONO_LE) THEN
                  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC arith_ss[],
                  FIRST_ASSUM(MP_TAC o CONJUNCT1 o SPEC ``(k + m):num``) THEN
                  SIMP_TAC arith_ss[]],ALL_TAC] THEN
          ASM_SIMP_TAC arith_ss[] THEN RW_TAC arith_ss[] THENL
           [REWRITE_TAC[REAL_MIN_LE1],REWRITE_TAC[REAL_MIN_LE2]],ALL_TAC] THEN
        ASM_SIMP_TAC arith_ss[rsum] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        MATCH_MP_TAC(REAL_ARITH
                ``(x = y) ==> abs(x - i) < e ==> abs(y - i) < e``) THEN
        ONCE_ASM_REWRITE_TAC[] THEN
        SIMP_TAC arith_ss[GSYM SUM_SPLIT, SUM_1, ADD_CLAUSES] THEN
        MATCH_MP_TAC(REAL_ARITH ``(a = b) ==> (x + a = b + x)``) THEN
        UNDISCH_TAC``sum(m + 1, PRE n)
                (\n. (f:real->real)((p:num->real) n) * (d(SUC n) - d n)) = s2`` THEN
        CONV_TAC(LAND_CONV SYM_CONV) THEN SIMP_TAC arith_ss[] THEN DISCH_TAC THEN
        SUBGOAL_THEN``(1:num) = 0 + 1``ASSUME_TAC THENL
         [SIMP_TAC arith_ss[],ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN``(m:num) + (0 + 1) = 0 + m + 1``ASSUME_TAC THENL
         [SIMP_TAC arith_ss[],ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUM_REINDEX] THEN MATCH_MP_TAC SUM_EQ THEN
        SIMP_TAC arith_ss[ADD_CLAUSES, ADD_EQ_0]);

(* ------------------------------------------------------------------------- *)
(* Pointwise perturbation and spike functions.                               *)
(* ------------------------------------------------------------------------- *)

val DINT_DELTA_LEFT = store_thm("DINT_DELTA_LEFT",
  ``!a b. Dint(a,b) (\x. if x = a then &1 else &0) (&0)``,
  REPEAT GEN_TAC THEN DISJ_CASES_TAC(REAL_ARITH ``b < a \/ a <= b``) THENL
   [ASM_SIMP_TAC arith_ss[DINT_WRONG],
    REWRITE_TAC[Dint] THEN X_GEN_TAC ``e:real`` THEN DISCH_TAC THEN
    EXISTS_TAC ``(\x. e):real->real`` THEN
        ASM_SIMP_TAC arith_ss[REAL_LT_DIV, REAL_LT, gauge,
                                                fine, rsum, tdiv, REAL_SUB_RZERO] THEN
    MAP_EVERY X_GEN_TAC[“d:num->real”,“p:num->real”] THEN
        STRIP_TAC THEN ASM_CASES_TAC(Term`dsize d = 0`) THEN
        ASM_REWRITE_TAC[sum, ABS_N] THEN
    SUBGOAL_THEN“dsize d = 1 + PRE (dsize d)”ASSUME_TAC THENL
     [ASM_SIMP_TAC arith_ss[PRE_SUB1],
          ONCE_ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[GSYM SUM_SPLIT, SUM_1, ADD_CLAUSES] THEN
          MATCH_MP_TAC(REAL_ARITH
       ``(&0 <= x /\ x < e) /\ (y = &0) ==> (abs(x + y) < e)``) THEN
          CONJ_TAC THENL
           [BETA_TAC THEN COND_CASES_TAC THENL
            [REWRITE_TAC[REAL_MUL_LID, REAL_SUB_LE] THEN
             ASM_MESON_TAC[DIVISION_THM, ZERO_LESS_EQ, NOT_ZERO_LT_ZERO],
             ASM_REWRITE_TAC [REAL_MUL_LZERO, REAL_LE_REFL]],
            MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC ``r:num`` THEN STRIP_TAC THEN
            BETA_TAC THEN REWRITE_TAC[REAL_ENTIRE] THEN DISJ1_TAC THEN
            SUBGOAL_THEN``(a:real) < (p:num->real) r``MP_TAC THENL
             [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC``(d:num->real)r`` THEN
              CONJ_TAC THENL
               [SUBGOAL_THEN``(a:real) = (d:num->real) 0``MP_TAC THENL
                [UNDISCH_TAC``division (a,b) d`` THEN REWRITE_TAC[DIVISION_THM] THEN
                     STRIP_TAC THEN UNDISCH_TAC``(d:num->real) 0 = a`` THEN
                     CONV_TAC(LAND_CONV SYM_CONV) THEN PROVE_TAC[],
                     DISCH_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN
                     MATCH_MP_TAC DIVISION_LT_GEN THEN
                     MAP_EVERY EXISTS_TAC[``a:real``,``b:real``] THEN
                     ASM_SIMP_TAC arith_ss[LESS_EQ, GSYM ONE]],
                     POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
                         ASM_SIMP_TAC arith_ss[]],
              SIMP_TAC arith_ss[REAL_LT_IMP_NE]]]]]);

val DINT_DELTA_RIGHT = store_thm("DINT_DELTA_RIGHT",
  ``!a b. Dint(a,b) (\x. if x = b then &1 else &0) (&0)``,
  REPEAT GEN_TAC THEN DISJ_CASES_TAC(REAL_ARITH ``b < a \/ a <= b``) THENL
   [ASM_SIMP_TAC arith_ss[DINT_WRONG],
    REWRITE_TAC[Dint] THEN
    X_GEN_TAC ``e:real`` THEN DISCH_TAC THEN
        EXISTS_TAC ``(\x. e):real->real`` THEN
        ASM_SIMP_TAC arith_ss[REAL_LT_DIV, REAL_LT,
                                                gauge, fine, rsum, tdiv, REAL_SUB_RZERO] THEN
    MAP_EVERY X_GEN_TAC [``d:num->real``, ``p:num->real``] THEN
        STRIP_TAC THEN ASM_CASES_TAC ``dsize d = 0`` THEN
        ASM_REWRITE_TAC[sum, ABS_N] THEN
        SUBGOAL_THEN``dsize d = PRE (dsize d) + 1``ASSUME_TAC THENL
         [ASM_SIMP_TAC arith_ss[PRE_SUB1],
          ONCE_ASM_REWRITE_TAC[] THEN ABBREV_TAC ``m = PRE(dsize d)`` THEN
          ASM_REWRITE_TAC[GSYM SUM_SPLIT, SUM_1, ADD_CLAUSES] THEN
          MATCH_MP_TAC(REAL_ARITH
        ``(&0 <= x /\ x < e) /\ (y = &0) ==> abs(y + x) < e``) THEN
      CONJ_TAC THENL
           [BETA_TAC THEN COND_CASES_TAC THENL
            [REWRITE_TAC[REAL_MUL_LID, REAL_SUB_LE] THEN CONJ_TAC THENL
                 [PROVE_TAC[DIVISION_MONO_LE_SUC], ASM_SIMP_TAC arith_ss[]],
                  ASM_REWRITE_TAC[REAL_MUL_LZERO, REAL_LE_REFL]],
                  MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC ``r:num`` THEN
                  REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN BETA_TAC THEN
                  REWRITE_TAC[REAL_ENTIRE] THEN DISJ1_TAC THEN
                  SUBGOAL_THEN``(p:num->real) r < b``MP_TAC THENL
                   [MATCH_MP_TAC REAL_LET_TRANS THEN
                    EXISTS_TAC``(d:num->real)(SUC r)`` THEN CONJ_TAC THENL
                         [ASM_REWRITE_TAC[],
                          SUBGOAL_THEN``b = d(dsize d)``MP_TAC THENL
                           [UNDISCH_TAC``division(a,b) (d:num->real)`` THEN
                            REWRITE_TAC[DIVISION_THM] THEN STRIP_TAC THEN
                                POP_ASSUM MP_TAC THEN SIMP_TAC arith_ss[],
                                DISCH_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN
                                ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUC_ONE_ADD] THEN
                                MATCH_MP_TAC DIVISION_LT_GEN THEN
                                MAP_EVERY EXISTS_TAC[``a:real``,``b:real``] THEN
                                ASM_SIMP_TAC arith_ss[LESS_EQ]]],
                                SIMP_TAC arith_ss[REAL_LT_IMP_NE]]]]]);

val DINT_DELTA = store_thm("DINT_DELTA",
  ``!a b c. Dint(a,b) (\x. if x = c then &1 else &0) (&0)``,
  REPEAT GEN_TAC THEN ASM_CASES_TAC ``a <= b`` THENL
   [ALL_TAC, ASM_MESON_TAC[REAL_NOT_LE, DINT_WRONG]] THEN
  ASM_CASES_TAC ``a <= c /\ c <= b`` THENL
   [ALL_TAC,
    MATCH_MP_TAC INTEGRAL_EQ THEN EXISTS_TAC ``\x:real. &0`` THEN
    ASM_REWRITE_TAC[DINT_0] THEN RW_TAC arith_ss[]] THEN
  GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM REAL_ADD_LID] THEN
  MATCH_MP_TAC DINT_COMBINE THEN EXISTS_TAC ``c:real`` THEN
  ASM_REWRITE_TAC[DINT_DELTA_LEFT, DINT_DELTA_RIGHT]);

val DINT_POINT_SPIKE = store_thm("DINT_POINT_SPIKE",
        ``!f g a b c i.
        (!x. a <= x /\ x <= b /\ ~(x = c) ==> (f x = g x)) /\ Dint(a,b) f i
        ==> Dint(a,b) g i``,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC ``a <= b`` THENL
   [ALL_TAC, ASM_MESON_TAC[REAL_NOT_LE, DINT_WRONG]] THEN
  MATCH_MP_TAC INTEGRAL_EQ THEN
  EXISTS_TAC ``\x:real. f(x) + (g c - f c) * (if x = c then &1 else &0)`` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBST1_TAC(REAL_ARITH ``i = i + ((g:real->real) c - f c) * &0``) THEN
    HO_MATCH_MP_TAC DINT_ADD THEN ASM_REWRITE_TAC[] THEN
    HO_MATCH_MP_TAC DINT_CMUL THEN REWRITE_TAC[DINT_DELTA],
    REPEAT STRIP_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC arith_ss[REAL_MUL_RZERO, REAL_ADD_RID] THEN
    REAL_ARITH_TAC]);

val DINT_FINITE_SPIKE = store_thm("DINT_FINITE_SPIKE",
  ``!f g a b s i.
        FINITE s /\
        (!x. a <= x /\ x <= b /\ ~(x IN s) ==> (f x = g x)) /\
        Dint(a,b) f i
        ==> Dint(a,b) g i``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[TAUT_CONV ``a /\ b /\ c ==> d <=> c ==> a ==> b ==> d``] THEN
  DISCH_TAC THEN
  MAP_EVERY (fn t => SPEC_TAC(t,t))[``g:real->real``, ``s:real->bool``] THEN
  SIMP_TAC bool_ss[RIGHT_FORALL_IMP_THM] THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN REWRITE_TAC[NOT_IN_EMPTY] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[INTEGRAL_EQ], ALL_TAC] THEN
  X_GEN_TAC``s:real->bool`` THEN DISCH_TAC THEN X_GEN_TAC``c:real`` THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[TAUT_CONV``a /\ b ==> c ==> d <=> b /\ c /\ a ==> d``] THEN
  STRIP_TAC THEN X_GEN_TAC ``g:real->real`` THEN
  REWRITE_TAC[IN_INSERT, DE_MORGAN_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC DINT_POINT_SPIKE THEN
  EXISTS_TAC ``\x. if x = c then (f:real->real) x else g x`` THEN
  EXISTS_TAC ``c:real`` THEN SIMP_TAC arith_ss[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN BETA_TAC THEN RW_TAC std_ss[]);

(* ------------------------------------------------------------------------- *)
(* Cauchy-type integrability criterion.                                      *)
(* ------------------------------------------------------------------------- *)

val GAUGE_MIN_FINITE = store_thm("GAUGE_MIN_FINITE",
    ``!s gs n. (!m:num. m <= n ==> gauge s (gs m))
            ==> ?g. gauge s g /\
                    !d p. fine g (d,p) ==> !m. m <= n ==> fine (gs m) (d,p)``,
        GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
        [MESON_TAC[LE],
         REWRITE_TAC[LE] THEN
         REWRITE_TAC[TAUT_CONV ``(a \/ b ==> c) = ((a ==> c) /\ (b ==> c))``] THEN
         SIMP_TAC arith_ss[FORALL_AND_THM, LEFT_FORALL_IMP_THM, EXISTS_REFL] THEN
         STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o assert (is_imp o concl)) THEN
         ASM_REWRITE_TAC[] THEN
         DISCH_THEN(X_CHOOSE_THEN ``gm:real->real`` STRIP_ASSUME_TAC) THEN
         EXISTS_TAC ``\x:real. if gm x <
                gs(SUC n) x then gm x else gs(SUC n) x`` THEN
         SUBGOAL_THEN``gauge s (\x:real. if gm x <
                gs(SUC n) x then gm x else gs(SUC n) x)``ASSUME_TAC THENL
          [MATCH_MP_TAC GAUGE_MIN THEN ASM_REWRITE_TAC[],
           ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
           DISCH_THEN(MP_TAC o MATCH_MP FINE_MIN) THEN
           ASM_SIMP_TAC arith_ss[ETA_AX]]]);

val INTEGRABLE_CAUCHY = store_thm("INTEGRABLE_CAUCHY",
  ``!f a b. integrable(a,b) f <=>
           !e. &0 < e
               ==> ?g. gauge (\x. a <= x /\ x <= b) g /\
                       !d1 p1 d2 p2.
                            tdiv (a,b) (d1,p1) /\ fine g (d1,p1) /\
                            tdiv (a,b) (d2,p2) /\ fine g (d2,p2)
                            ==> abs (rsum(d1,p1) f - rsum(d2,p2) f) < e``,
  REPEAT GEN_TAC THEN REWRITE_TAC[integrable] THEN EQ_TAC THENL
   [REWRITE_TAC[Dint] THEN DISCH_THEN(X_CHOOSE_TAC ``i:real``) THEN
    X_GEN_TAC ``e:real`` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC ``e / &2``) THEN
        ASM_SIMP_TAC arith_ss[REAL_LT_DIV, REAL_LT] THEN
        HO_MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ``g:real->real`` THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        MAP_EVERY X_GEN_TAC
     [``d1:num->real``, ``p1:num->real``,
                ``d2:num->real``, ``p2:num->real``] THEN STRIP_TAC THEN
          FIRST_X_ASSUM(fn th =>
        MP_TAC(SPECL [``d1:num->real``, ``p1:num->real``] th) THEN
        MP_TAC(SPECL [``d2:num->real``, ``p2:num->real``] th)) THEN
          ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
          ONCE_REWRITE_TAC[REAL_ARITH``abs(a - b) = abs(a - i + -(b - i))``] THEN
          MATCH_MP_TAC REAL_LET_TRANS THEN
          EXISTS_TAC``abs(rsum(d1,p1) f -i) + abs(-(rsum(d2,p2) f - i))`` THEN
          REWRITE_TAC[ABS_TRIANGLE] THEN REWRITE_TAC[ABS_NEG] THEN
          GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM REAL_HALF_DOUBLE] THEN
          MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC[],ALL_TAC] THEN
        DISCH_TAC THEN DISJ_CASES_TAC(REAL_ARITH ``b < a \/ a <= b``) THENL
        [ASM_MESON_TAC[DINT_WRONG], ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o GEN ``n:num`` o SPEC ``&1 / &2 pow n``) THEN
        SIMP_TAC arith_ss[REAL_LT_DIV, REAL_POW_LT, REAL_LT] THEN
        SIMP_TAC arith_ss[FORALL_AND_THM, SKOLEM_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN ``g:num->real->real`` STRIP_ASSUME_TAC) THEN
        MP_TAC(GEN ``n:num``
     (SPECL [``\x. a <= x /\ x <= b``, ``g:num->real->real``, ``n:num``]
          GAUGE_MIN_FINITE)) THEN
        ASM_SIMP_TAC arith_ss[SKOLEM_THM, FORALL_AND_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN ``G:num->real->real`` STRIP_ASSUME_TAC) THEN
        MP_TAC(GEN ``n:num``
     (SPECL [``a:real``, ``b:real``,
                         ``(G:num->real->real) n``] DIVISION_EXISTS)) THEN
        ASM_SIMP_TAC bool_ss[SKOLEM_THM,GSYM LEFT_FORALL_IMP_THM,
                                                        FORALL_AND_THM] THEN
        MAP_EVERY X_GEN_TAC [``d:num->num->real``, ``p:num->num->real``] THEN
        STRIP_TAC THEN
        SUBGOAL_THEN ``cauchy (\n. rsum(d n,p n) f)`` MP_TAC THENL
         [REWRITE_TAC[cauchy] THEN X_GEN_TAC ``e:real`` THEN DISCH_TAC THEN
          MP_TAC(SPEC ``&1 / e`` REAL_ARCH_POW2) THEN
          HO_MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ``N:num`` THEN
          ASM_SIMP_TAC arith_ss[REAL_LT_LDIV_EQ] THEN DISCH_TAC THEN
          REWRITE_TAC[GREATER_EQ] THEN
          MAP_EVERY X_GEN_TAC [``m:num``,``n:num``] THEN STRIP_TAC THEN
          FIRST_X_ASSUM(MP_TAC o SPECL
      [``N:num``, ``(d:num->num->real) m``, ``(p:num->num->real) m``,
       ``(d:num->num->real) n``, ``(p:num->num->real) n``]) THEN
          SUBGOAL_THEN
                ``tdiv (a,b) ((d:num->num->real) m,(p:num->num->real) m) /\
                fine ((g:num->real->real) N) (d m,p m) /\ tdiv (a,b) (d n,p n) /\
                fine (g N) (d n,p n)``ASSUME_TAC THENL
           [ASM_MESON_TAC[],ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC(REAL_ARITH ``d < e ==> x < d ==> x < e``) THEN
          ASM_SIMP_TAC arith_ss[REAL_LT_LDIV_EQ, REAL_POW_LT, REAL_LT] THEN
          ASM_MESON_TAC[REAL_MUL_SYM], ALL_TAC] THEN
         REWRITE_TAC[SEQ_CAUCHY, convergent, SEQ, Dint] THEN
         HO_MATCH_MP_TAC MONO_EXISTS THEN
         X_GEN_TAC ``i:real`` THEN STRIP_TAC THEN
         X_GEN_TAC ``e:real`` THEN DISCH_TAC THEN
         FIRST_X_ASSUM(MP_TAC o SPEC ``e / &2``) THEN
         ASM_SIMP_TAC arith_ss[REAL_LT_DIV, REAL_LT] THEN
         DISCH_THEN(X_CHOOSE_THEN ``N1:num`` MP_TAC) THEN
         X_CHOOSE_TAC ``N2:num`` (SPEC ``&2 / e`` REAL_ARCH_POW2) THEN
         DISCH_THEN(MP_TAC o SPEC ``N1 + N2:num``) THEN
         REWRITE_TAC[GREATER_EQ, LESS_EQ_ADD] THEN
         DISCH_TAC THEN EXISTS_TAC ``(G:num->real->real)(N1 + N2)`` THEN
         ASM_REWRITE_TAC[] THEN
         MAP_EVERY X_GEN_TAC [``dx:num->real``, ``px:num->real``] THEN
         STRIP_TAC THEN
         FIRST_X_ASSUM(MP_TAC o SPECL
     [``N1 + N2:num``, ``dx:num->real``, ``px:num->real``,
      ``(d:num->num->real)(N1 + N2)``, ``(p:num->num->real)(N1 + N2)``]) THEN
         SUBGOAL_THEN``tdiv (a,b) (dx,px) /\ fine (g ((N1:num) + N2)) (dx,px) /\
                tdiv (a,b) (d (N1 + N2),p (N1 + N2)) /\
                fine (g ((N1:num) + N2)) (d (N1 + N2),p (N1 + N2))``ASSUME_TAC THENL
         [ASM_MESON_TAC[LESS_EQ_REFL], ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN``1 / 2 pow ((N1:num)+ N2) < e / &2``ASSUME_TAC THENL
          [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC``inv(&2 / e)`` THEN
           CONJ_TAC THENL
            [REWRITE_TAC[GSYM REAL_INV_1OVER] THEN MATCH_MP_TAC REAL_LT_INV THEN
             ASM_SIMP_TAC arith_ss[REAL_LT_DIV, REAL_LT] THEN
                 MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC ``&2 pow N2`` THEN
                 ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_POW_ADD] THEN
                 GEN_REWRITE_TAC LAND_CONV empty_rewrites [GSYM REAL_MUL_LID] THEN
                 MATCH_MP_TAC REAL_LE_RMUL_IMP THEN REWRITE_TAC[POW_2_LE1] THEN
                 MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC``&1`` THEN
                 REWRITE_TAC[REAL_LE_01,POW_2_LE1],
                 MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
                 MATCH_MP_TAC REAL_LINV_UNIQ THEN
                 REWRITE_TAC[REAL_DIV_INNER_CANCEL2] THEN
                 MATCH_MP_TAC REAL_DIV_REFL THEN MATCH_MP_TAC REAL_POS_NZ THEN
                 ASM_REWRITE_TAC[]],
           DISCH_TAC THEN
           SUBGOAL_THEN``
                        abs (rsum (dx,px) f - rsum ((d :num -> num -> real) (N1 + N2),
                        p (N1 + N2)) f) < e / &2``ASSUME_TAC THENL
                 [MATCH_MP_TAC REAL_LT_TRANS THEN
                  EXISTS_TAC``1 / &2 pow(N1 + N2)`` THEN
                  ASM_REWRITE_TAC[],ALL_TAC] THEN
                MATCH_MP_TAC REAL_LET_TRANS THEN
                EXISTS_TAC``abs((rsum(dx,px) f -
                                rsum((d:num->num->real)(N1 + N2),p(N1 + N2)) f)
                                + (rsum((d:num->num->real)(N1 + N2),p(N1 + N2)) f - i))`` THEN
                CONJ_TAC THENL
                 [REWRITE_TAC[real_sub, REAL_ADD_ASSOC] THEN
                  REWRITE_TAC[GSYM real_sub] THEN
                  SIMP_TAC arith_ss[REAL_SUB_ADD,REAL_LE_REFL],
                  MATCH_MP_TAC REAL_LET_TRANS THEN
                  EXISTS_TAC``abs(rsum(dx,px) f -
                        rsum((d:num->num->real)(N1 + N2),p(N1 + N2)) f)
                    + abs(rsum((d:num->num->real)(N1 + N2),p(N1 + N2)) f - i)`` THEN
                   SIMP_TAC arith_ss[REAL_ABS_TRIANGLE] THEN
                   GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM REAL_HALF_DOUBLE] THEN
                   MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC[]]]);

(* ------------------------------------------------------------------------- *)
(* Limit theorem.                                                            *)
(* ------------------------------------------------------------------------- *)

val RSUM_BOUND = store_thm("RSUM_BOUND",
  ``!a b d p e f.
        tdiv(a,b) (d,p) /\
        (!x. a <= x /\ x <= b ==> abs(f x) <= e)
        ==> abs(rsum(d,p) f) <= e * (b - a)``,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rsum] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC (Term`sum(0,dsize d) (\i. abs(f(p i :real) * (d(SUC i) - d i)))`) THEN
  SIMP_TAC arith_ss[SUM_ABS_LE] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC (Term`sum(0,dsize d) (\i. e * abs(d(SUC i) - d(i)))`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[ADD_CLAUSES, REAL_ABS_MUL] THEN
    X_GEN_TAC (Term`r:num`) THEN STRIP_TAC THEN BETA_TAC THEN
        MATCH_MP_TAC REAL_LE_RMUL1 THEN REWRITE_TAC[REAL_ABS_POS] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_MESON_TAC[tdiv, DIVISION_UBOUND, DIVISION_LBOUND, REAL_LE_TRANS],
        ALL_TAC] THEN
   SIMP_TAC arith_ss[SUM_CMUL] THEN MATCH_MP_TAC REAL_LE_LMUL1 THEN
   CONJ_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o SPEC (Term`a:real`)) THEN
         ASM_MESON_TAC[REAL_LE_REFL, REAL_ABS_POS, REAL_LE_TRANS, DIVISION_LE,
                                        tdiv], ALL_TAC] THEN
         FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o REWRITE_RULE[tdiv]) THEN
         FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_LE_SUC) THEN
         ASM_REWRITE_TAC[abs, REAL_SUB_LE, SUM_DIFFS, ADD_CLAUSES] THEN
         PROVE_TAC[DIVISION_RHS, DIVISION_LHS, REAL_LE_REFL]);

val RSUM_DIFF_BOUND = store_thm ("RSUM_DIFF_BOUND",
  ``!a b d p e f g.
        tdiv(a,b) (d,p) /\
        (!x. a <= x /\ x <= b ==> abs(f x - g x) <= e)
        ==> abs(rsum (d,p) f - rsum (d,p) g) <= e * (b - a)``,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o HO_MATCH_MP RSUM_BOUND) THEN
  SIMP_TAC bool_ss[rsum, SUM_SUB, REAL_SUB_RDISTRIB]);

val INTEGRABLE_LIMIT = store_thm("INTEGRABLE_LIMIT",
  ``!f a b. (!e. &0 < e
                ==> ?g. (!x. a <= x /\ x <= b ==> abs(f x - g x) <= e) /\
                        integrable(a,b) g)
           ==> integrable(a,b) f``,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC ``a <= b`` THENL
  [FIRST_X_ASSUM(MP_TAC o GEN ``n:num`` o SPEC ``&1 / &2 pow n``) THEN
   SIMP_TAC arith_ss[REAL_LT_DIV, REAL_POW_LT, REAL_LT] THEN
   SIMP_TAC arith_ss[FORALL_AND_THM, SKOLEM_THM, integrable] THEN
   DISCH_THEN(X_CHOOSE_THEN ``g:num->real->real`` (CONJUNCTS_THEN2
    ASSUME_TAC (X_CHOOSE_TAC ``i:num->real``))) THEN
   SUBGOAL_THEN ``cauchy i`` MP_TAC THENL
    [REWRITE_TAC[cauchy] THEN X_GEN_TAC ``e:real`` THEN DISCH_TAC THEN
     MP_TAC(SPEC ``(&2 * &2 * (b - a)) / e`` REAL_ARCH_POW2) THEN
         HO_MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ``N:num`` THEN DISCH_TAC THEN
         MAP_EVERY X_GEN_TAC [``m:num``, ``n:num``] THEN REWRITE_TAC[GREATER_EQ] THEN
         STRIP_TAC THEN UNDISCH_TAC``!(n:num). Dint(a,b) (g n) (i n)`` THEN
         REWRITE_TAC[Dint] THEN SIMP_TAC bool_ss[Once SWAP_FORALL_THM] THEN
         DISCH_THEN(MP_TAC o SPEC ``e / &2 / &2``) THEN
         ASM_SIMP_TAC arith_ss[REAL_LT_DIV, REAL_LT] THEN
         DISCH_THEN(fn th => MP_TAC(SPEC ``m:num`` th) THEN
      MP_TAC(SPEC ``n:num`` th)) THEN
         DISCH_THEN(X_CHOOSE_THEN ``gn:real->real`` STRIP_ASSUME_TAC) THEN
         DISCH_THEN(X_CHOOSE_THEN ``gm:real->real`` STRIP_ASSUME_TAC) THEN
         MP_TAC(SPECL [``a:real``, ``b:real``,
                ``\x:real. if gm x < gn x then gm x else gn x``]
                DIVISION_EXISTS) THEN
         ASM_SIMP_TAC arith_ss[GAUGE_MIN, GSYM LEFT_FORALL_IMP_THM] THEN
         MAP_EVERY X_GEN_TAC [``d:num->real``, ``p:num->real``] THEN
         STRIP_TAC THEN
         FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o MATCH_MP FINE_MIN) THEN
         REPEAT(FIRST_X_ASSUM(MP_TAC o SPECL [``d:num->real``,
                                        ``p:num->real``])) THEN
         ASM_REWRITE_TAC[] THEN
         SUBGOAL_THEN ``abs(rsum(d,p) (g(m:num)) - rsum(d,p) (g n)) <= e / &2``
     (fn th => MP_TAC th) THENL
         [MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC ``&2 / &2 pow N * (b - a)`` THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC RSUM_DIFF_BOUND THEN ASM_REWRITE_TAC[] THEN
            REPEAT STRIP_TAC THEN REWRITE_TAC[real_div] THEN
                HO_MATCH_MP_TAC(REAL_ARITH
        ``!f. abs(f - gm) <= inv(k) /\ abs(f - gn) <= inv(k)
            ==> (abs(gm - gn) <= &2*inv(k))``) THEN
                EXISTS_TAC ``(f:real->real) x`` THEN CONJ_TAC THEN
                MATCH_MP_TAC REAL_LE_TRANS THENL
                 [EXISTS_TAC ``&1 / &2 pow m``,EXISTS_TAC``&1 / &2 pow n``] THEN
                ASM_SIMP_TAC arith_ss[] THEN REWRITE_TAC[real_div, REAL_MUL_LID] THEN
                MATCH_MP_TAC REAL_LE_INV2 THEN
                ASM_SIMP_TAC arith_ss[REAL_POW_LT, REAL_POW_MONO, REAL_LE,REAL_LT],
                MATCH_MP_TAC REAL_LE_RDIV THEN CONJ_TAC THENL
                 [REAL_ARITH_TAC, GEN_REWRITE_TAC LAND_CONV empty_rewrites [REAL_MUL_SYM] THEN
                  ONCE_REWRITE_TAC[REAL_MUL_ASSOC] THEN REWRITE_TAC [real_div] THEN
                  REWRITE_TAC [REAL_MUL_ASSOC] THEN
                  ONCE_REWRITE_TAC [GSYM REAL_MUL_ASSOC] THEN
                  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites [REAL_MUL_SYM] THEN
                  REWRITE_TAC [REAL_MUL_ASSOC] THEN REWRITE_TAC [GSYM real_div] THEN
                  ASM_SIMP_TAC arith_ss[REAL_LE_LDIV_EQ, REAL_POW_LT, REAL_LT] THEN
                  GEN_REWRITE_TAC RAND_CONV empty_rewrites [REAL_MUL_SYM] THEN
                  ASM_SIMP_TAC arith_ss[GSYM REAL_LE_LDIV_EQ, REAL_LT_IMP_LE]]],
          REPEAT STRIP_TAC THEN
          SUBGOAL_THEN ``abs(rsum(d,p) (g(m:num)) - rsum(d,p) (g n) -
                (i m - i n)) < e / &2``(fn th => MP_TAC th) THENL
           [SUBGOAL_THEN“!a b c d. a-b-(c-d) = a-c - (b-d)”
                (fn th => ONCE_REWRITE_TAC[GEN_ALL th]) THENL
                [REAL_ARITH_TAC, ALL_TAC] THEN
                MATCH_MP_TAC REAL_LET_TRANS THEN
                EXISTS_TAC``abs(rsum(d,p)(g (m:num)) - i m)
                                        + abs(rsum(d,p) (g n) - i n)`` THEN CONJ_TAC THENL
                 [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites [real_sub] THEN
                  GEN_REWRITE_TAC (funpow 2 RAND_CONV) empty_rewrites [GSYM ABS_NEG] THEN
                  MATCH_ACCEPT_TAC ABS_TRIANGLE,
                  GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM REAL_HALF_DOUBLE] THEN
                  MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC[]],
          DISCH_TAC THEN
          ABBREV_TAC``s = rsum(d,p)(g (m:num)) - rsum(d,p) (g n)`` THEN
          ABBREV_TAC``t= s- (i (m:num) - i n)`` THEN POP_ASSUM MP_TAC THEN
          GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) empty_rewrites [real_sub] THEN
          ONCE_REWRITE_TAC [GSYM REAL_ADD_SYM] THEN
          ONCE_REWRITE_TAC [GSYM REAL_EQ_SUB_LADD] THEN
          ONCE_REWRITE_TAC [REAL_NEG_EQ] THEN ONCE_REWRITE_TAC [REAL_NEG_SUB] THEN
          DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_sub] THEN
          MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC``abs s + abs (-t)`` THEN
          REWRITE_TAC[ABS_TRIANGLE] THEN
          GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM REAL_HALF_DOUBLE] THEN
          MATCH_MP_TAC REAL_LET_ADD2 THEN PROVE_TAC[ABS_NEG]]],
  REWRITE_TAC[SEQ_CAUCHY, convergent] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ``s:real`` THEN DISCH_TAC THEN
  REWRITE_TAC[Dint] THEN X_GEN_TAC ``e:real`` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC ``e / &3`` o REWRITE_RULE[SEQ]) THEN
  ASM_SIMP_TAC arith_ss[REAL_LT_DIV, REAL_LT, GREATER_EQ] THEN
  DISCH_THEN(X_CHOOSE_TAC ``N1:num``) THEN
  MP_TAC(SPEC ``(&3 * (b - a)) / e`` REAL_ARCH_POW2) THEN
  DISCH_THEN(X_CHOOSE_TAC ``N2:num``) THEN
  UNDISCH_TAC``!(n:num). Dint(a,b) (g (n:num)) ( i n)`` THEN
  REWRITE_TAC[Dint] THEN
  DISCH_THEN(MP_TAC o SPECL [``N1 + N2:num``, ``e / &3``]) THEN
  ASM_SIMP_TAC arith_ss[REAL_LT_DIV, REAL_LT] THEN
  HO_MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC ``g:real->real`` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [``d:num->real``, ``p:num->real``] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [``d:num->real``, ``p:num->real``]) THEN
  ASM_REWRITE_TAC[] THEN SUBGOAL_THEN``N1:num <= N1 + N2``MP_TAC THENL
   [REWRITE_TAC[LESS_EQ_ADD], ALL_TAC] THEN DISCH_TAC THEN
  SUBGOAL_THEN``abs(i ((N1:num) + N2) - s) < e/3``MP_TAC THENL
   [ASM_MESON_TAC[], ALL_TAC] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN``abs(rsum(d,p) f - rsum(d,p)
  (g ((N1:num) + N2))) <= e/ &3``MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC ``&1 / &2 pow (N1 + N2) * (b - a)`` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RSUM_DIFF_BOUND THEN ASM_REWRITE_TAC[],
          MATCH_MP_TAC REAL_LE_RDIV THEN CONJ_TAC THENL
          [REAL_ARITH_TAC,
           GEN_REWRITE_TAC LAND_CONV empty_rewrites [REAL_MUL_SYM] THEN
           ONCE_REWRITE_TAC[REAL_MUL_ASSOC] THEN REWRITE_TAC [real_div] THEN
           REWRITE_TAC [REAL_MUL_ASSOC] THEN
           ONCE_REWRITE_TAC [GSYM REAL_MUL_ASSOC] THEN
           GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites [REAL_MUL_SYM] THEN
           REWRITE_TAC [REAL_MUL_ASSOC] THEN REWRITE_TAC [GSYM real_div] THEN
           ASM_SIMP_TAC arith_ss[REAL_LE_LDIV_EQ, REAL_POW_LT, REAL_LT] THEN
           GEN_REWRITE_TAC RAND_CONV empty_rewrites [REAL_MUL_SYM] THEN
           REWRITE_TAC[REAL_MUL_RID] THEN
           ASM_SIMP_TAC arith_ss[GSYM REAL_LE_LDIV_EQ, REAL_LT_IMP_LE] THEN
           SUBGOAL_THEN``N2:num <= N1 + N2``MP_TAC THENL
            [ONCE_REWRITE_TAC[ADD_COMM] THEN REWRITE_TAC[LESS_EQ_ADD],
                 DISCH_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
                 MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC``2 pow N2`` THEN
                 ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_MONO THEN
                 ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]]],
        DISCH_TAC THEN ABBREV_TAC``sf = rsum(d,p) f`` THEN
        ABBREV_TAC``sg = rsum(d,p) (g ((N1:num) + N2))`` THEN
        SUBGOAL_THEN``abs(sf - i((N1:num) + N2)) < 2*e/3``MP_TAC THENL
         [MATCH_MP_TAC REAL_LET_TRANS THEN
          EXISTS_TAC``abs(sf - sg) + abs(sg - i((N1:num)+ N2))`` THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_TRANS THEN
            EXISTS_TAC``abs((sf - sg) + (sg - i((N1:num) + N2)))`` THEN
                REWRITE_TAC[ABS_TRIANGLE] THEN REAL_ARITH_TAC,
                REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC] THEN
                REWRITE_TAC[GSYM REAL_DOUBLE, GSYM real_div] THEN
                PROVE_TAC[REAL_LET_ADD2]],
          ONCE_REWRITE_TAC [GSYM REAL_NEG_THIRD] THEN DISCH_TAC THEN
          MATCH_MP_TAC REAL_LET_TRANS THEN
          EXISTS_TAC``abs((sf - i((N1:num) + N2)) + (i((N1:num) + N2) - s))`` THEN
          CONJ_TAC THENL
           [REAL_ARITH_TAC, MATCH_MP_TAC REAL_LET_TRANS THEN
            EXISTS_TAC``abs((sf - i((N1:num) + N2))) +
                        abs((i((N1:num) + N2) - s))`` THEN REWRITE_TAC[ABS_TRIANGLE] THEN
                MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC``(e - e / 3) + e/3`` THEN
                CONJ_TAC THENL [PROVE_TAC[REAL_LT_ADD2],REAL_ARITH_TAC]]]]],
   ASM_MESON_TAC[REAL_NOT_LE, DINT_WRONG, integrable]]);

(* ------------------------------------------------------------------------- *)
(* Hence continuous functions are integrable.                                *)
(* ------------------------------------------------------------------------- *)

val INTEGRABLE_CONST = store_thm("INTEGRABLE_CONST",
 “!a b c. integrable(a,b) (\x. c)”,
  REWRITE_TAC[integrable] THEN REPEAT GEN_TAC THEN
  EXISTS_TAC(Term`c*(b-a):real`) THEN SIMP_TAC arith_ss[DINT_CONST]);

val INTEGRABLE_ADD = store_thm("INTEGRABLE_ADD",
  ``!f g a b. a<=b /\ integrable(a,b) f /\ integrable(a,b) g ==>
    integrable(a,b)(\x. f x + g x)``,
  RW_TAC std_ss[] THEN REWRITE_TAC[integrable] THEN
  EXISTS_TAC``integral(a,b) f + integral(a,b) g`` THEN
  MATCH_MP_TAC DINT_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC INTEGRABLE_DINT THEN ASM_REWRITE_TAC[]);

val INTEGRABLE_CMUL = store_thm("INTEGRABLE_CMUL",
  ``!f a b c. a<=b /\ integrable(a,b) f ==> integrable(a,b)(\x. c* f x)``,
  RW_TAC std_ss[] THEN REWRITE_TAC[integrable] THEN
  EXISTS_TAC``c*integral(a,b)f`` THEN HO_MATCH_MP_TAC DINT_CMUL THEN
  MATCH_MP_TAC INTEGRABLE_DINT THEN ASM_REWRITE_TAC[]);

val INTEGRABLE_COMBINE = store_thm("INTEGRABLE_COMBINE",
        ``!f a b c. a <= b /\ b <= c /\ integrable(a,b) f /\ integrable(b,c) f
         ==> integrable(a,c) f``,
  REWRITE_TAC[integrable] THEN MESON_TAC[DINT_COMBINE]);

val INTEGRABLE_POINT_SPIKE = store_thm("INTEGRABLE_POINT_SPIKE",
        ``!f g a b c.
         (!x. a <= x /\ x <= b /\ ~(x = c) ==> (f x = g x)) /\ integrable(a,b) f
                        ==> integrable(a,b) g``,
  REWRITE_TAC[integrable] THEN MESON_TAC[DINT_POINT_SPIKE]);

val SUP_INTERVAL = store_thm("SUP_INTERVAL",
        ``!P a b.
        (?x. a <= x /\ x <= b /\ P x)
        ==> ?s. a <= s /\ s <= b /\
                !y. y < s <=> (?x. a <= x /\ x <= b /\ P x /\ y < x)``,
        REPEAT STRIP_TAC THEN
        MP_TAC(SPEC ``\x. a <= x /\ x <= b /\ P x`` REAL_SUP) THEN
        SUBGOAL_THEN``(?x. (\x. a <= x /\ x <= b /\ P x) x) /\
                (?z. !x. (\x. a <= x /\ x <= b /\ P x) x ==> x < z)``MP_TAC THENL
          [CONJ_TAC THENL
            [BETA_TAC THEN EXISTS_TAC``x:real`` THEN ASM_REWRITE_TAC[],
                 BETA_TAC THEN EXISTS_TAC``(b+1:real)`` THEN REPEAT STRIP_TAC THEN
                 ASM_SIMP_TAC arith_ss[REAL_LT_ADD1]],
           DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
           ABBREV_TAC ``s = sup (\x. a <= x /\ x <= b /\ P x)`` THEN
           DISCH_TAC THEN EXISTS_TAC ``s:real`` THEN
           ASM_MESON_TAC[REAL_LTE_TRANS, REAL_NOT_LE, REAL_LT_ANTISYM]]);

val CONT_UNIFORM = store_thm("CONT_UNIFORM",
  ``!f a b. a <= b /\ (!x. a <= x /\ x <= b ==> f contl x)
           ==> !e. &0 < e ==> ?d. &0 < d /\
                                  !x y. a <= x /\ x <= b /\
                                        a <= y /\ y <= b /\
                                        abs(x - y) < d
                                        ==> abs(f(x) - f(y)) < e``,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC ``\c. ?d. &0 < d /\
                       !x y. a <= x /\ x <= c /\
                             a <= y /\ y <= c /\
                             abs(x - y) < d
                             ==> abs(f(x) - f(y)) < e``
         SUP_INTERVAL) THEN
  DISCH_THEN(MP_TAC o SPECL [``a:real``, ``b:real``]) THEN
  SUBGOAL_THEN``?x.
   a <= x /\ x <= b /\
   (\c.
      ?d.
        0 < d /\
        !x y.
          a <= x /\ x <= c /\ a <= y /\ y <= c /\ abs (x - y) < d ==>
          abs (f x - f y) < e) x``ASSUME_TAC THENL
   [EXISTS_TAC ``a:real`` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    BETA_TAC THEN EXISTS_TAC ``&1`` THEN SIMP_TAC arith_ss[REAL_LT] THEN
        ASM_MESON_TAC[REAL_LE_ANTISYM, REAL_ARITH ``abs(x - x) = &0``],
        ALL_TAC] THEN
        ASM_SIMP_TAC arith_ss[] THEN
        DISCH_THEN(X_CHOOSE_THEN ``s:real`` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN ``?t. s < t /\ ?d. &0 < d /\
                                 !x y. a <= x /\ x <= t /\ a <= y /\ y <= t /\
                                       abs(x - y) < d ==> abs(f(x) - f(y)) < e``
     MP_TAC THENL
          [UNDISCH_TAC ``!x. a <= x /\ x <= b ==> f contl x`` THEN
           DISCH_THEN(MP_TAC o SPEC ``s:real``) THEN ASM_REWRITE_TAC[] THEN
           REWRITE_TAC[CONTL_LIM, LIM] THEN DISCH_THEN(MP_TAC o SPEC ``e / &2``) THEN
           ASM_SIMP_TAC arith_ss[REAL_LT_DIV, REAL_LT] THEN
           DISCH_THEN(X_CHOOSE_THEN ``d1:real`` STRIP_ASSUME_TAC) THEN
           SUBGOAL_THEN ``&0 < d1 / &2 /\ d1 / &2 < d1`` STRIP_ASSUME_TAC THENL
            [ASM_SIMP_TAC arith_ss[REAL_LT_DIV, REAL_LT, REAL_LT_LDIV_EQ,
                   REAL_ARITH ``(d < d * &2) <=> (&0 < d)``], ALL_TAC] THEN
           SUBGOAL_THEN ``!x y. abs(x - s) < d1 /\ abs(y - s) < d1
                        ==> abs(f(x) - f(y)) < e`` ASSUME_TAC THENL
                [REPEAT STRIP_TAC THEN
                 GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM REAL_HALF_DOUBLE] THEN
                 HO_MATCH_MP_TAC(REAL_ARITH
                                ``!a. abs(x - a) < e / &2 /\ abs(y - a) < e / &2
                                        ==> abs(x - y) < e / &2 + e / &2``) THEN
                 EXISTS_TAC ``(f:real->real) s`` THEN
                 SUBGOAL_THEN ``!x. abs(x - s) < d1 ==> abs(f x - f s) < e / &2``
                        (fn th => ASM_MESON_TAC[th]) THEN
             X_GEN_TAC ``u:real`` THEN REPEAT STRIP_TAC THEN
                 ASM_CASES_TAC ``u:real = s`` THENL
                  [ASM_SIMP_TAC arith_ss[REAL_SUB_REFL, ABS_N, REAL_LT_DIV, REAL_LT],
                   ALL_TAC] THEN
                 ASM_MESON_TAC[REAL_ARITH ``&0 < abs(x - s) <=> ~(x = s)``],
                 ALL_TAC] THEN
                 SUBGOAL_THEN ``s - d1 / &2 < s`` MP_TAC THENL
                  [ASM_REWRITE_TAC[REAL_ARITH ``x - y < x <=> &0 < y``],ALL_TAC] THEN
                 DISCH_THEN(fn th => FIRST_ASSUM(fn th' =>
                         MP_TAC(GEN_REWRITE_RULE I empty_rewrites [th'] th))) THEN
                 DISCH_THEN(X_CHOOSE_THEN ``r:real`` MP_TAC) THEN
                 DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
                 DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
                 DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
                 DISCH_THEN(X_CHOOSE_THEN ``d2:real`` STRIP_ASSUME_TAC) THEN
                 MP_TAC(SPECL [``d2:real``, ``d1 / &2``] REAL_DOWN2) THEN
                 ASM_REWRITE_TAC[] THEN
                 DISCH_THEN(X_CHOOSE_THEN ``d:real`` STRIP_ASSUME_TAC) THEN
                 EXISTS_TAC ``s + d / &2`` THEN
                 ASM_SIMP_TAC arith_ss[REAL_LT_DIV, REAL_LT,
                                                REAL_ARITH ``s < s + d <=> &0 < d``] THEN
                 EXISTS_TAC ``d:real`` THEN ASM_REWRITE_TAC[] THEN
                 MAP_EVERY X_GEN_TAC[``x:real``, ``y:real``] THEN STRIP_TAC THEN
                 ASM_CASES_TAC ``x <= r /\ y <= r`` THENL
                  [ASM_MESON_TAC[REAL_LT_TRANS], ALL_TAC] THEN
                 MATCH_MP_TAC(ASSUME ``!x y. abs(x - s) < d1 /\ abs(y - s) < d1 ==>
                                        abs(f x - f y) < e``) THEN
                 MATCH_MP_TAC(REAL_ARITH
                        ``!r t d d12.
                          ~(x <= r /\ y <= r) /\
                          abs(x - y) < d /\
                          s - d12 < r /\ t <= s + d /\
                          x <= t /\ y <= t /\ &2 * d12 <= e /\
                          &2 * d < e ==> abs(x - s) < e /\ abs(y - s) < e``) THEN
                 MAP_EVERY EXISTS_TAC[``r:real``,``s + d / &2``,``d:real``,``d1 / &2``] THEN
                 ASM_REWRITE_TAC[REAL_LE_LADD] THEN
                 SIMP_TAC arith_ss[REAL_DIV_LMUL, REAL_OF_NUM_EQ] THEN
                 ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
                 SIMP_TAC arith_ss[REAL_LE_LDIV_EQ, GSYM REAL_LT_RDIV_EQ, REAL_LT] THEN
                 ASM_SIMP_TAC arith_ss[REAL_ARITH ``&0 < d ==> d <= d * &2``, REAL_LE_REFL],
                 ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_THEN ``t:real`` (CONJUNCTS_THEN ASSUME_TAC)) THEN
          SUBGOAL_THEN ``b <= t`` (fn th => ASM_MESON_TAC[REAL_LE_TRANS, th]) THEN
          FIRST_X_ASSUM(X_CHOOSE_THEN ``d:real`` STRIP_ASSUME_TAC) THEN
          UNDISCH_THEN ``!x. a <= x /\ x <= b ==> f contl x`` (K ALL_TAC) THEN
          FIRST_X_ASSUM(MP_TAC o assert(is_eq o concl) o SPEC ``s:real``) THEN
          REWRITE_TAC[REAL_LT_REFL] THEN CONV_TAC CONTRAPOS_CONV THEN
          REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN EXISTS_TAC ``t:real`` THEN
          ASM_MESON_TAC[REAL_LT_IMP_LE, REAL_LE_TRANS]);

val INTEGRABLE_CONTINUOUS = store_thm("INTEGRABLE_CONTINUOUS",
 ``!f a b. (!x. a <= x /\ x <= b ==> f contl x) ==> integrable(a,b) f``,
  REPEAT STRIP_TAC THEN DISJ_CASES_TAC(REAL_ARITH ``b < a \/ a <= b``) THENL
   [ASM_MESON_TAC[integrable, DINT_WRONG], ALL_TAC] THEN
  MATCH_MP_TAC INTEGRABLE_LIMIT THEN X_GEN_TAC ``e:real`` THEN DISCH_TAC THEN
  MP_TAC(SPECL[``f:real->real``, ``a:real``, ``b:real``] CONT_UNIFORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC ``e:real``) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN ``d:real`` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  UNDISCH_TAC ``a <= b`` THEN MAP_EVERY (fn t => SPEC_TAC(t,t))
   [``b:real``, ``a:real``] THEN
  HO_MATCH_MP_TAC BOLZANO_LEMMA_ALT THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [``u:real``, ``v:real``, ``w:real``] THEN
    NTAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(fn th => DISCH_TAC THEN MP_TAC th) THEN
    MATCH_MP_TAC(TAUT_CONV
      ``(a /\ b) /\ (c /\ d ==> e) ==> (a ==> c) /\ (b ==> d) ==> e``) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[REAL_LE_TRANS], ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC ``g:real->real``)
                               (X_CHOOSE_TAC ``h:real->real``)) THEN
    EXISTS_TAC ``\x. if x <= v then g(x):real else h(x)`` THEN
    CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN COND_CASES_TAC THENL
          [ASM_MESON_TAC[REAL_LE_TOTAL],ASM_MESON_TAC[REAL_LE_TOTAL]],ALL_TAC] THEN
    MATCH_MP_TAC INTEGRABLE_COMBINE THEN EXISTS_TAC ``v:real`` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC INTEGRABLE_POINT_SPIKE THENL
     [EXISTS_TAC ``g:real->real``, EXISTS_TAC ``h:real->real``] THEN
    EXISTS_TAC ``v:real`` THEN ASM_REWRITE_TAC[] THEN SIMP_TAC arith_ss[] THEN
        GEN_TAC THEN DISCH_TAC THEN SUBGOAL_THEN``~(x<=v)``ASSUME_TAC THENL
         [ASM_MESON_TAC[REAL_ARITH ``b <= x /\ x <= c /\ ~(x = b) ==> ~(x <= b)``],
          RW_TAC std_ss[]], ALL_TAC] THEN
  X_GEN_TAC ``x:real`` THEN EXISTS_TAC ``d:real`` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [``u:real``, ``v:real``] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC ``\x:real. (f:real->real) u`` THEN
  ASM_REWRITE_TAC[INTEGRABLE_CONST] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC std_ss[REAL_LE_REFL] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC``x:real`` THEN
    ASM_REWRITE_TAC[],
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC``(x'-u):real`` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_EQ_IMP_LE THEN ONCE_REWRITE_TAC[ABS_REFL] THEN
          ASM_SIMP_TAC arith_ss[REAL_SUB_LE],
          MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC``(v-u):real`` THEN
          ASM_REWRITE_TAC[REAL_LE_SUB_CANCEL2]]]);

(* ------------------------------------------------------------------------- *)
(* Integrability on a subinterval.                                           *)
(* ------------------------------------------------------------------------- *)

val INTEGRABLE_SPLIT_SIDES = store_thm("INTEGRABLE_SPLIT_SIDES",
  ``!f a b c.
        a <= c /\ c <= b /\ integrable(a,b) f
        ==> ?i. !e. &0 < e
                    ==> ?g. gauge(\x. a <= x /\ x <= b) g /\
                            !d1 p1 d2 p2. tdiv(a,c) (d1,p1) /\
                                          fine g (d1,p1) /\
                                          tdiv(c,b) (d2,p2) /\
                                          fine g (d2,p2)
                                          ==> abs((rsum(d1,p1) f +
                                                   rsum(d2,p2) f) - i) < e``,
  REPEAT GEN_TAC THEN REWRITE_TAC[integrable, Dint] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  HO_MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ``i:real`` THEN
  HO_MATCH_MP_TAC MONO_ALL THEN X_GEN_TAC ``e:real`` THEN
  ASM_CASES_TAC ``&0 < e`` THEN ASM_REWRITE_TAC[] THEN
  HO_MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ``g:real->real`` THEN
  ASM_MESON_TAC[DIVISION_APPEND_STRONG] THEN ASM_REWRITE_TAC[]);

val INTEGRABLE_SUBINTERVAL_LEFT = store_thm("INTEGRABLE_SUBINTERVAL_LEFT",
  ``!f a b c. a <= c /\ c <= b /\ integrable(a,b) f ==> integrable(a,c) f``,
   REPEAT GEN_TAC THEN DISCH_TAC THEN
   FIRST_ASSUM(X_CHOOSE_TAC ``i:real`` o MATCH_MP INTEGRABLE_SPLIT_SIDES) THEN
   REWRITE_TAC[INTEGRABLE_CAUCHY] THEN X_GEN_TAC ``e:real`` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC ``e / &2``) THEN
   SIMP_TAC arith_ss[ASSUME ``&0 < e``, REAL_LT_DIV, REAL_LT] THEN
   HO_MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ``g:real->real`` THEN STRIP_TAC THEN
   CONJ_TAC THENL
    [UNDISCH_TAC ``gauge (\x. a <= x /\ x <= b) g`` THEN
         REWRITE_TAC[gauge] THEN ASM_MESON_TAC[REAL_LE_TRANS],ALL_TAC] THEN
         REPEAT STRIP_TAC THEN
         MP_TAC(SPECL [``c:real``, ``b:real``, ``g:real->real``]
                                DIVISION_EXISTS) THEN
         SUBGOAL_THEN``c <= b /\ gauge (\x. c <= x /\ x <= b) g``ASSUME_TAC THENL
          [ASM_REWRITE_TAC[] THEN
           UNDISCH_TAC ``gauge (\x. a <= x /\ x <= b) g`` THEN
           REWRITE_TAC[gauge] THEN ASM_MESON_TAC[REAL_LE_TRANS],ALL_TAC] THEN
           ASM_REWRITE_TAC[] THEN SIMP_TAC arith_ss[GSYM LEFT_FORALL_IMP_THM] THEN
         MAP_EVERY X_GEN_TAC [``d:num->real``, ``p:num->real``] THEN STRIP_TAC THEN
         FIRST_X_ASSUM(fn th =>
      MP_TAC(SPECL [``d1:num->real``, ``p1:num->real``] th) THEN
      MP_TAC(SPECL [``d2:num->real``, ``p2:num->real``] th)) THEN
         SIMP_TAC arith_ss[AND_IMP_INTRO, GSYM FORALL_AND_THM] THEN
         DISCH_THEN(MP_TAC o SPECL [``d:num->real``, ``p:num->real``]) THEN
         ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
         MATCH_MP_TAC REAL_LET_TRANS THEN
         EXISTS_TAC``abs ((rsum (d1,p1) f + rsum (d,p) f - i) -
                                (rsum (d2,p2) f + rsum (d,p) f - i))`` THEN
         CONJ_TAC THENL
          [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
           REWRITE_TAC[REAL_ARITH``a + b - i -(c + b - i) = a - c``],
           MATCH_MP_TAC REAL_LET_TRANS THEN
           EXISTS_TAC``abs (rsum (d1,p1) f + rsum (d,p) f - i) +
                                        abs(rsum (d2,p2) f + rsum (d,p) f - i)`` THEN
           CONJ_TAC THENL
            [REWRITE_TAC[REAL_ARITH``abs(a - b) <= abs a + abs b``],
             GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM REAL_HALF_DOUBLE] THEN
             MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC[]]]);

val INTEGRABLE_SUBINTERVAL_RIGHT = store_thm("INTEGRABLE_SUBINTERVAL_RIGHT",
  ``!f a b c. a <= c /\ c <= b /\ integrable(a,b) f ==> integrable(c,b) f``,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC ``i:real`` o MATCH_MP INTEGRABLE_SPLIT_SIDES) THEN
  REWRITE_TAC[INTEGRABLE_CAUCHY] THEN X_GEN_TAC ``e:real`` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC ``e / &2``) THEN
  SIMP_TAC arith_ss[ASSUME ``&0 < e``, REAL_LT_DIV, REAL_LT] THEN
  HO_MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ``g:real->real`` THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC ``gauge (\x. a <= x /\ x <= b) g`` THEN
         REWRITE_TAC[gauge] THEN ASM_MESON_TAC[REAL_LE_TRANS], ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
         MP_TAC(SPECL [``a:real``, ``c:real``, ``g:real->real``]
                                DIVISION_EXISTS) THEN
  SUBGOAL_THEN``a <= c /\ gauge (\x. a <= x /\ x <= c) g``ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC ``gauge (\x. a <= x /\ x <= b) g`` THEN
        REWRITE_TAC[gauge] THEN ASM_MESON_TAC[REAL_LE_TRANS], ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN SIMP_TAC arith_ss[GSYM LEFT_FORALL_IMP_THM] THEN
         MAP_EVERY X_GEN_TAC [``d:num->real``, ``p:num->real``] THEN STRIP_TAC THEN
         FIRST_X_ASSUM(MP_TAC o SPECL [``d:num->real``, ``p:num->real``]) THEN
         DISCH_THEN(fn th =>
   MP_TAC(SPECL [``d1:num->real``, ``p1:num->real``] th) THEN
   MP_TAC(SPECL [``d2:num->real``, ``p2:num->real``] th)) THEN
   ASM_REWRITE_TAC[] THEN
   REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC``abs ((rsum (d,p) f + rsum (d1,p1) f - i) -
                                (rsum (d,p) f + rsum (d2,p2) f - i))`` THEN
   CONJ_TAC THENL
    [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
         REWRITE_TAC[REAL_ARITH``a + b - i -(a + c - i) = b - c``], ALL_TAC] THEN
   MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC``abs (rsum (d,p) f + rsum (d1,p1) f - i) +
                                abs(rsum (d,p) f + rsum (d2,p2) f - i)`` THEN
   CONJ_TAC THENL
    [REWRITE_TAC[REAL_ARITH``abs(a - b) <= abs a + abs b``],
     GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM REAL_HALF_DOUBLE] THEN
     MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC[]]);

val INTEGRABLE_SUBINTERVAL = store_thm("INTEGRABLE_SUBINTERVAL",
  ``!f a b c d. a <= c /\ c <= d /\ d <= b /\ integrable(a,b) f
               ==> integrable(c,d) f``,
  MESON_TAC[INTEGRABLE_SUBINTERVAL_LEFT, INTEGRABLE_SUBINTERVAL_RIGHT,
            REAL_LE_TRANS]);

(* ------------------------------------------------------------------------- *)
(* More basic lemmas about integration.                                      *)
(* ------------------------------------------------------------------------- *)

val INTEGRAL_0 = store_thm("INTEGRAL_0",
  ``!a b. a <= b ==> (integral(a,b) (\x. 0) = 0)``,
  RW_TAC std_ss[] THEN MATCH_MP_TAC DINT_INTEGRAL THEN
  ASM_REWRITE_TAC[DINT_0]);

val INTEGRAL_CONST = store_thm("INTEGRAL_CONST",
 “!a b c. a <= b ==> (integral(a,b) (\x. c) = c * (b - a))”,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DINT_INTEGRAL THEN
  ASM_SIMP_TAC arith_ss[DINT_CONST]);

val INTEGRAL_CMUL = store_thm("INTEGRAL_CMUL",
“!f c a b. a <= b /\ integrable(a,b) f
           ==> (integral(a,b) (\x. c * f(x)) = c * integral(a,b) f)”,
        REPEAT STRIP_TAC THEN MATCH_MP_TAC DINT_INTEGRAL THEN
        ASM_SIMP_TAC arith_ss[DINT_CMUL, INTEGRABLE_DINT]);

val INTEGRAL_ADD = store_thm("INTEGRAL_ADD",
“!f g a b. a <= b /\ integrable(a,b) f /\ integrable(a,b) g
             ==> (integral(a,b) (\x. f(x) + g(x)) =
                 integral(a,b) f + integral(a,b) g)”,
        REPEAT STRIP_TAC THEN MATCH_MP_TAC DINT_INTEGRAL THEN
        ASM_SIMP_TAC arith_ss[DINT_ADD, INTEGRABLE_DINT]);

val INTEGRAL_SUB = store_thm("INTEGRAL_SUB",
 “!f g a b. a <= b /\ integrable(a,b) f /\ integrable(a,b) g
             ==> (integral(a,b) (\x. f(x) - g(x)) =
                 integral(a,b) f - integral(a,b) g)”,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DINT_INTEGRAL THEN
  ASM_SIMP_TAC arith_ss[DINT_SUB, INTEGRABLE_DINT]);

val INTEGRAL_BY_PARTS = store_thm("INTEGRAL_BY_PARTS",
  ``!f g f' g' a b.
         a <= b /\
         (!x. a <= x /\ x <= b ==> (f diffl f' x) x) /\
         (!x. a <= x /\ x <= b ==> (g diffl g' x) x) /\
         integrable(a,b) (\x. f' x * g x) /\
         integrable(a,b) (\x. f x * g' x)
         ==> (integral(a,b) (\x. f x * g' x) =
              (f b * g b - f a * g a) - integral(a,b) (\x. f' x * g x))``,
  MP_TAC INTEGRATION_BY_PARTS THEN REPEAT(HO_MATCH_MP_TAC MONO_ALL THEN GEN_TAC) THEN
  DISCH_THEN(fn th => STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJ (ASSUME ``a <= b``)) THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP DINT_INTEGRAL) THEN
  ASM_SIMP_TAC arith_ss[INTEGRAL_ADD] THEN REAL_ARITH_TAC);

val INTEGRAL_COMBINE = store_thm("INTEGRAL_COMBINE",
  ``!f a b c. a <= b /\ b <= c /\ (integrable (a,c) f) ==>
      (integral (a,c) f = (integral (a,b) f) + (integral (b,c) f))``,
  RW_TAC std_ss[integral] THEN SELECT_ELIM_TAC THEN RW_TAC std_ss[] THENL
   [FULL_SIMP_TAC std_ss[integrable] THEN EXISTS_TAC ``i:real`` THEN
    ASM_REWRITE_TAC[],
        SELECT_ELIM_TAC THEN CONJ_TAC THENL
         [REWRITE_TAC[GSYM integrable] THEN MATCH_MP_TAC INTEGRABLE_SUBINTERVAL THEN
          MAP_EVERY EXISTS_TAC[``a:real``,``c:real``] THEN
          RW_TAC std_ss[REAL_LE_REFL, integrable],
          SELECT_ELIM_TAC THEN CONJ_TAC THENL
           [REWRITE_TAC[GSYM integrable] THEN MATCH_MP_TAC INTEGRABLE_SUBINTERVAL THEN
                MAP_EVERY EXISTS_TAC[``a:real``,``c:real``] THEN
                RW_TAC std_ss[REAL_LE_REFL, integrable],
                RW_TAC std_ss[] THEN MATCH_MP_TAC DINT_UNIQ THEN
                MAP_EVERY EXISTS_TAC[``a:real``,``c:real``,``f:real->real``] THEN
                RW_TAC std_ss[] THENL
                 [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC ``b:real`` THEN
                  RW_TAC std_ss[],
                  MATCH_MP_TAC DINT_COMBINE THEN EXISTS_TAC ``b:real`` THEN
                  RW_TAC std_ss[]]]]]);

(* ------------------------------------------------------------------------- *)
(* Mean value theorem of integral.                                           *)
(* ------------------------------------------------------------------------- *)

val INTEGRAL_MVT1 = store_thm("INTEGRAL_MVT1",
  ``!f a b. (a <= b /\(!x. a<=x /\ x<=b ==> f contl x)) ==>
  (?x. a<=x /\ x<=b /\ (integral(a,b) f = f(x)*(b-a)))``,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL[``f:real->real``,``a:real``,``b:real``]CONT_ATTAINS_ALL) THEN
  REWRITE_TAC[TAUT_CONV``((a ==> b) ==> (a ==> c)) = (a ==> b ==> c)``] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC``a:real=b`` THENL
   [EXISTS_TAC``b:real`` THEN ASM_SIMP_TAC std_ss[REAL_LE_REFL] THEN
    ASM_SIMP_TAC std_ss[REAL_SUB_REFL,REAL_MUL_RZERO] THEN
        MATCH_MP_TAC DINT_INTEGRAL THEN
        ASM_SIMP_TAC std_ss[REAL_LE_REFL,INTEGRAL_NULL], ALL_TAC] THEN
  SUBGOAL_THEN``?x:real. a<=x /\ x<=b /\
                                (f x = inv(b-a)* integral(a,b) f)``ASSUME_TAC THENL
   [UNDISCH_TAC``!y. L <= y /\ y <= M ==> ?x. a <= x /\ x<=b /\ (f x = y)`` THEN
    DISCH_THEN(MP_TAC o SPEC``inv(b-a)* integral(a,b)f``) THEN
        REPEAT STRIP_TAC THEN
        SUBGOAL_THEN``(L*(b-a) <= integral(a,b) f) /\
                                (integral(a,b) f <= M*(b-a))``ASSUME_TAC THENL
        [CONJ_TAC THENL
     [SUBGOAL_THEN``L*(b-a)=integral(a,b)(\x. L)``ASSUME_TAC THENL
           [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_CONST THEN
            ASM_REWRITE_TAC[],ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_LE THEN
                ASM_SIMP_TAC std_ss[INTEGRABLE_CONTINUOUS,
                                                  INTEGRABLE_CONST,REAL_LT_IMP_LE]],
          SUBGOAL_THEN``M*(b-a) = integral(a,b)(\x. M)``ASSUME_TAC THENL
           [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_CONST THEN
            ASM_REWRITE_TAC[], ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_LE THEN
                ASM_SIMP_TAC std_ss[INTEGRABLE_CONTINUOUS,
                                                  INTEGRABLE_CONST,REAL_LT_IMP_LE]]],ALL_TAC] THEN
    SUBGOAL_THEN``L <= inv(b-a) * integral(a,b) f /\
                                inv(b-a) * integral(a,b) f <= M``MP_TAC THENL
         [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
          CONJ_TAC THENL
          [MATCH_MP_TAC REAL_LE_RDIV THEN
           ASM_SIMP_TAC std_ss[REAL_SUB_LT,REAL_LT_LE],
           MATCH_MP_TAC REAL_LE_LDIV THEN
           ASM_SIMP_TAC std_ss[REAL_SUB_LT,REAL_LT_LE]],ALL_TAC] THEN
        ASM_SIMP_TAC std_ss[],ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN``x:real``STRIP_ASSUME_TAC) THEN
  EXISTS_TAC``x:real``THEN ASM_SIMP_TAC std_ss[REAL_ARITH``a*b*c=c*a*b``] THEN
  SUBGOAL_THEN``(b:real -a)*inv(b-a)=1``ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC REAL_POS_NZ THEN
    ASM_SIMP_TAC std_ss[REAL_SUB_LT,REAL_LT_LE],ALL_TAC] THEN
  ASM_SIMP_TAC std_ss[REAL_MUL_LID]);

(* ------------------------------------------------------------------------- *)
(* connection to integrationTheory (bridging theorem added by Chun Tian)     *)
(* ------------------------------------------------------------------------- *)

(* NOTE: ‘b < a’ must be avoid, as ‘integral$integral (a,b) f’ is unspecified
  (see DINT_WRONG), while ‘integration$integral (interval [a,b]) f = 0’. (see
   HAS_INTEGRAL_NULL).

   UPDATE: ‘a = b’ must be also avoid, because ‘tagged_division_of’ allows
   degenerate divisions, which must be filtered out when constructing Dint.
 *)

(* Part 1: from old integrals to new integrals *)
Theorem Dint_imp_has_integral[local] :
    !f a b k. a < b /\ Dint(a,b) f k ==> (f has_integral k) (interval[a,b])
Proof
    RW_TAC std_ss [Dint, has_integral]
 >> Q.PAT_X_ASSUM ‘!e. 0 < e ==> P’ (MP_TAC o (Q.SPEC ‘e’)) >> rw []
 >> Q.ABBREV_TAC ‘E = \x. a <= x /\ x <= b’
 >> Q.ABBREV_TAC ‘d = \x. ball (x,if E x then 1 / 2 * g x else 1)’
 >> Q.EXISTS_TAC ‘d’ (* gauge d *)
 >> STRONG_CONJ_TAC >- rw [Abbr ‘d’, GSYM gauge_alt]
 >> DISCH_TAC
 >> rpt STRIP_TAC
 (* now, from ‘p tagged_division_of interval [a,b]’ we must find all its end
    points, sorted by interval lowerbounds, then construct an equivalent (D,t)
    such that ‘tdiv (a,b) (D,t)’ and ‘fine g (D,t)’. This is not easy.
  *)
 >> Q.PAT_X_ASSUM ‘p tagged_division_of i’
      (STRIP_ASSUME_TAC o (REWRITE_RULE [TAGGED_DIVISION_OF]))
 (* preparing for iterateTheory.TOPOLOGICAL_SORT' *)
 >> Q.ABBREV_TAC ‘R = \(x1,k1) (x2,k2). (x1,k1) IN p /\ (x2,k2) IN p /\
                                        0 < content k1 /\ 0 < content k2 /\
                        interval_lowerbound k1 <= interval_lowerbound k2’
 >> Know ‘transitive R /\ antisymmetric R’
 >- (RW_TAC std_ss [transitive_def, antisymmetric_def, Abbr ‘R’]
     >- (Cases_on ‘x’ >> Cases_on ‘y’ >> Cases_on ‘z’ >> fs [] \\
         METIS_TAC [REAL_LE_TRANS]) \\
  (* antisymmetric requires some assumptions *)
     Cases_on ‘x’ >> Cases_on ‘y’ >> fs [] \\
     rename1 ‘x1 = x2 /\ k1 = k2’ \\
     Q.PAT_ASSUM ‘!x k. (x,k) IN p ==> P’ (MP_TAC o (Q.SPECL [‘x1’, ‘k1’])) \\
     RW_TAC std_ss [] >> rename1 ‘interval [a1,b1] SUBSET interval [a,b]’ \\
     Q.PAT_ASSUM ‘!x k. (x,k) IN p ==> P’ (MP_TAC o (Q.SPECL [‘x2’, ‘k2’])) \\
     RW_TAC std_ss [] >> rename1 ‘interval [a2,b2] SUBSET interval [a,b]’ \\
    ‘interval [a1,b1] <> {} /\ interval [a2,b2] <> {}’ by METIS_TAC [MEMBER_NOT_EMPTY] \\
    ‘a1 <= b1 /\ a2 <= b2’ by PROVE_TAC [INTERVAL_NE_EMPTY] \\
     FULL_SIMP_TAC std_ss [INTERVAL_LOWERBOUND, CONTENT_POS_LT_EQ] \\
    ‘a1 = a2’ by PROVE_TAC [REAL_LE_ANTISYM] \\
     Q.PAT_ASSUM ‘!x1 k1 x2 k2. _ ==> interior k1 INTER interior k2 = {}’
       (MP_TAC o (Q.SPECL [‘x1’, ‘interval [a1,b1]’, ‘x2’, ‘interval [a2,b2]’])) \\
     RW_TAC std_ss [INTERIOR_CLOSED_INTERVAL, EQ_INTERVAL, GSYM DISJOINT_DEF] \\
     CCONTR_TAC \\
     Q.PAT_X_ASSUM ‘_ ==> DISJOINT (interval (a1,b1)) (interval (a1,b2))’ MP_TAC \\
     RW_TAC std_ss [DISJOINT_ALT, IN_INTERVAL] \\
    ‘a1 < min b1 b2’ by PROVE_TAC [REAL_LT_MIN] \\
    ‘?z. a1 < z /\ z < min b1 b2’ by METIS_TAC [REAL_MEAN] \\
     Q.EXISTS_TAC ‘z’ >> fs [REAL_LT_MIN])
 >> STRIP_TAC
 (* applying iterateTheory.TOPOLOGICAL_SORT' *)
 >> Q.ABBREV_TAC ‘L = {(x,k) | (x,k) IN p /\ 0 < content k}’
 >> Know ‘FINITE L’
 >- (MATCH_MP_TAC SUBSET_FINITE_I >> Q.EXISTS_TAC ‘p’ \\
     rw [Abbr ‘L’, SUBSET_DEF] >> art [])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘N = CARD L’
 >> ‘L HAS_SIZE N’ by PROVE_TAC [HAS_SIZE]
 >> drule_all TOPOLOGICAL_SORT' >> STRIP_TAC
 >> rename1 ‘L = IMAGE h (count N)’ (* this asserts ‘h’ *)
 (* h-properties *)
 >> Know ‘!i. i < N ==> h i IN p /\ 0 < content (SND (h i))’
 >- (Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘L = IMAGE h (count N)’ MP_TAC \\
     simp [Once EXTENSION, Abbr ‘L’] \\
     DISCH_THEN (MP_TAC o (Q.SPEC ‘h (i :num)’)) \\
     METIS_TAC [SND])
 >> DISCH_TAC
 >> Know ‘!x s. (x,s) IN L ==> ?n. n < N /\ (x,s) = h n’
 >- (Q.PAT_X_ASSUM ‘L = IMAGE h (count N)’ MP_TAC \\
     rw [Once EXTENSION, Abbr ‘L’] \\
     rename1 ‘(x,s) = h i’ >> Q.EXISTS_TAC ‘i’ >> art [])
 >> DISCH_TAC
 (* h-properties *)
 >> Know ‘!i j. i < N /\ j < N /\ i < j ==>
                interval_lowerbound (SND (h i)) < interval_lowerbound (SND (h j))’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!j k. j < N /\ k < N /\ j < k ==> ~R (h k) (h j)’
       (MP_TAC o (Q.SPECL [‘i’, ‘j’])) \\
     Cases_on ‘h i’ >> Cases_on ‘h j’ >> rw [Abbr ‘R’] (* 5 subgoals, same tactics *) \\
     METIS_TAC [SND, real_lt])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘!j k. j < N /\ k < N /\ j < k ==> ~R (h k) (h j)’ K_TAC
 (* clean up everything about R (not needed anymore) *)
 >> Q.PAT_X_ASSUM ‘transitive R’    K_TAC
 >> Q.PAT_X_ASSUM ‘antisymmetric R’ K_TAC
 >> Q.UNABBREV_TAC ‘R’
 (* the set of all tags, degerated divisions must be among them *)
 >> Q.ABBREV_TAC ‘Z = {x | ?k. (x,k) IN p}’ (* i.e. the set of all tags *)
 >> Know ‘FINITE Z’
 >- (MATCH_MP_TAC SUBSET_FINITE_I >> Q.EXISTS_TAC ‘IMAGE FST p’ \\
     rw [IMAGE_FINITE, SUBSET_DEF, Abbr ‘Z’] >> rename1 ‘(x1,k1) IN p’ \\
     Q.EXISTS_TAC ‘(x1,k1)’ >> rw [])
 >> DISCH_TAC
 (* eliminate a special impossible case (N = 0) *)
 >> Know ‘N <> 0’
 >- (Q.PAT_X_ASSUM ‘L = IMAGE h (count N)’ K_TAC (* not needed here *) \\
     CCONTR_TAC >> fs [] \\
     Q.PAT_X_ASSUM ‘BIGUNION _ = interval [a,b]’ MP_TAC \\
     rw [Once EXTENSION, IN_INTERVAL, IN_BIGUNION, Abbr ‘E’] \\
     Q.ABBREV_TAC ‘y = CHOICE (interval[a,b] DIFF Z)’ \\
     Know ‘y IN interval[a,b] DIFF Z’
     >- (Q.UNABBREV_TAC ‘y’ >> MATCH_MP_TAC CHOICE_DEF \\
         MATCH_MP_TAC INFINITE_DIFF_FINITE >> art [] \\
        ‘interval(a,b) <> {}’ by PROVE_TAC [INTERVAL_NE_EMPTY] \\
         PROVE_TAC [finite_countable, UNCOUNTABLE_INTERVAL]) >> DISCH_TAC \\
    ‘y NOTIN Z’ by (Q.PAT_X_ASSUM ‘y IN interval[a,b] DIFF Z’ MP_TAC >> rw []) \\
     Know ‘a <= y /\ y <= b’
     >- (Q.PAT_X_ASSUM ‘y IN interval[a,b] DIFF Z’ MP_TAC \\
         rw [IN_DIFF, IN_INTERVAL]) >> STRIP_TAC \\
     CCONTR_TAC >> fs [] \\
     Q.PAT_X_ASSUM ‘!x. _ <=> a <= x /\ x <= b’ (MP_TAC o (Q.SPEC ‘y’)) \\
     RW_TAC std_ss [] \\
     CCONTR_TAC >> fs [] >> rename1 ‘(x,s) IN p’ \\
    ‘x IN Z’ by (rw [Abbr ‘Z’] >> Q.EXISTS_TAC ‘s’ >> art []) \\
     Q.PAT_X_ASSUM ‘!x k. (x,k) IN p ==> _’ (MP_TAC o (Q.SPECL [‘x’, ‘s’])) \\
     RW_TAC std_ss [] \\
     CCONTR_TAC >> fs [] \\
     rename1 ‘s = interval[a0,b0]’ \\
    ‘interval [a0,b0] <> {}’ by PROVE_TAC [MEMBER_NOT_EMPTY] \\
    ‘a0 <= b0’ by PROVE_TAC [INTERVAL_NE_EMPTY] \\
    ‘b0 = a0 \/ a0 < b0’ by PROVE_TAC [REAL_LE_LT]
     >- (gs [INTERVAL_SING, IN_SING]) \\
     Q.PAT_X_ASSUM ‘!x s. (x,s) NOTIN L’
       (MP_TAC o (Q.SPECL [‘x’, ‘interval [a0,b0]’])) \\
     rw [Abbr ‘L’, CONTENT_CLOSED_INTERVAL, REAL_SUB_LT])
 >> DISCH_TAC
 (* now construct tdiv (the old form) *)
 >> Q.ABBREV_TAC ‘D = \n. if n < N then interval_lowerbound (SND (h n)) else b’
 >> Q.ABBREV_TAC ‘t = \n. if n < N then FST (h n) else b’
 (* stage work *)
 >> Know ‘tdiv (a,b) (D,t)’
 >- (Q.PAT_X_ASSUM ‘L = IMAGE h (count N)’ K_TAC (* not needed here *) \\
     RW_TAC real_ss [tdiv, division, Abbr ‘D’, Abbr ‘t’] >| (* 4 subgoals *)
     [ (* goal 1 (of 4): interval_lowerbound (SND (h 0)) = a *)
       Q.PAT_X_ASSUM ‘BIGUNION _ = interval [a,b]’ MP_TAC \\
       rw [Once EXTENSION, IN_INTERVAL, IN_BIGUNION, Abbr ‘E’] \\
       Q.PAT_ASSUM ‘!x k. (x,k) IN p ==> x IN k /\ _’
         (MP_TAC o (Q.SPECL [‘FST ((h :num -> real # (real set)) 0)’,
                             ‘SND ((h :num -> real # (real set)) 0)’])) >> rw [] \\
       rename1 ‘SND (h 0) = interval [a0,b0]’ \\
       Know ‘interval [a0,b0] <> {}’
       >- (rw [GSYM MEMBER_NOT_EMPTY] \\
           Q.EXISTS_TAC ‘FST (h 0)’ \\
           Know ‘(FST (h 0),SND (h 0)) IN p’ >- rw [] \\
           METIS_TAC []) >> DISCH_TAC \\
      ‘a0 <= b0’ by PROVE_TAC [INTERVAL_NE_EMPTY] \\
       FULL_SIMP_TAC bool_ss [INTERVAL_LOWERBOUND_NONEMPTY, SUBSET_INTERVAL] \\
       CCONTR_TAC >> ‘a0 < a \/ a < a0’ by PROVE_TAC [REAL_LT_TOTAL] (* 2 subgoals *)
       >- (Q.PAT_X_ASSUM ‘a0 <> a’ K_TAC \\
           Q.PAT_X_ASSUM ‘!x. _ <=> a <= x /\ x <= b’ (MP_TAC o (Q.SPEC ‘a0’)) \\
           Suff ‘?s. a0 IN s /\ ?x. (x,s) IN p’ >- (Rewr >> rw [GSYM real_lt]) \\
           Q.EXISTS_TAC ‘SND (h 0)’ \\
           ONCE_REWRITE_TAC [CONJ_COMM] \\
           CONJ_TAC >- (Q.EXISTS_TAC ‘FST (h 0)’ >> rw []) \\
           Q.PAT_X_ASSUM ‘SND (h 0) = interval _’ (ONCE_REWRITE_TAC o wrap) \\
           rw [IN_INTERVAL]) \\
    (* stage work *)
      ‘a0 <= b’ by PROVE_TAC [REAL_LE_TRANS] \\
       Q.ABBREV_TAC ‘y = CHOICE (interval(a,a0) DIFF Z)’ \\
       Know ‘y IN interval(a,a0) DIFF Z’
       >- (Q.UNABBREV_TAC ‘y’ >> MATCH_MP_TAC CHOICE_DEF \\
           MATCH_MP_TAC INFINITE_DIFF_FINITE >> art [] \\
          ‘interval(a,a0) <> {}’ by PROVE_TAC [INTERVAL_NE_EMPTY] \\
           PROVE_TAC [finite_countable, UNCOUNTABLE_INTERVAL]) >> DISCH_TAC \\
       Know ‘a < y /\ y < b’
       >- (POP_ASSUM MP_TAC >> rw [IN_DIFF, IN_INTERVAL] \\
           MATCH_MP_TAC REAL_LTE_TRANS \\
           Q.EXISTS_TAC ‘a0’ >> art []) >> STRIP_TAC \\
       Q.PAT_X_ASSUM ‘!x. _ <=> a <= x /\ x <= b’ (MP_TAC o (Q.SPEC ‘y’)) \\
       Know ‘a <= y /\ y <= b’ >- PROVE_TAC [REAL_LT_IMP_LE] >> Rewr \\
       CCONTR_TAC >> FULL_SIMP_TAC bool_ss [] >> rename1 ‘(x,s) IN p’ \\
      ‘x IN Z’ by (rw [Abbr ‘Z’] >> Q.EXISTS_TAC ‘s’ >> art []) \\
    (* now we show that (x,s) IN L. But first of all, ‘s’ cannot be degenerate,
       since otherwise we will have x = y, but this is impossible. *)
       Know ‘(x,s) IN L’
       >- (rw [Abbr ‘L’] (* now ‘0 < content s’ *) \\
           Q.PAT_X_ASSUM ‘!x k. (x,k) IN p ==> _’ (MP_TAC o (Q.SPECL [‘x’, ‘s’])) \\
           RW_TAC std_ss [] >> rename1 ‘(x,interval[a1,b1]) IN p’ \\
          ‘interval [a1,b1] <> {}’ by METIS_TAC [MEMBER_NOT_EMPTY] \\
          ‘a1 <= b1’ by PROVE_TAC [INTERVAL_NE_EMPTY] \\
           Suff ‘content (interval[a1,b1]) <> 0’
           >- (rw [REAL_LT_LE, CONTENT_POS_LE]) \\
           CCONTR_TAC >> FULL_SIMP_TAC bool_ss [CONTENT_EQ_0] \\
          ‘b1 = a1’ by PROVE_TAC [REAL_LE_ANTISYM] \\
           fs [INTERVAL_SING, IN_SING]) >> DISCH_TAC \\
      ‘?m. m < N /\ (x,s) = h m’ by METIS_TAC [] \\
    (* ordering: (a, y, [a0,b0], b) *)
      ‘m = 0 \/ 0 < m’ by RW_TAC arith_ss []
       >- (Know ‘s = SND (h m)’
           >- (Q.PAT_X_ASSUM ‘(x,s) = h m’ (ONCE_REWRITE_TAC o wrap o SYM) >> rw []) \\
           DISCH_TAC \\
           Know ‘y IN interval [a0,b0]’ >- METIS_TAC [] \\
           fs [IN_INTERVAL, GSYM real_lt]) \\
       Q.PAT_X_ASSUM ‘!x k. (x,k) IN p ==> x IN k /\ _’ (MP_TAC o (Q.SPECL [‘x’,‘s’])) \\
       RW_TAC std_ss [] \\
       CCONTR_TAC >> FULL_SIMP_TAC bool_ss [] >> rename1 ‘s = interval[a1,b1]’ \\
      ‘interval [a1,b1] <> {}’ by METIS_TAC [MEMBER_NOT_EMPTY] \\
      ‘a1 <= b1’ by PROVE_TAC [INTERVAL_NE_EMPTY] \\
       Know ‘interval_lowerbound (SND (h 0)) < interval_lowerbound (SND (h m))’ >- rw [] \\
       Know ‘SND (h m) = interval[a1,b1]’
       >- (Q.PAT_X_ASSUM ‘(x,s) = h m’ (ONCE_REWRITE_TAC o wrap o SYM) >> rw []) >> Rewr \\
       Q.PAT_X_ASSUM ‘SND (h 0) = interval [a0,b0]’ (REWRITE_TAC o wrap) \\
       rw [INTERVAL_LOWERBOUND_NONEMPTY, real_lt] >> fs [IN_INTERVAL] \\
       MATCH_MP_TAC REAL_LT_IMP_LE >> MATCH_MP_TAC REAL_LET_TRANS \\
       Q.EXISTS_TAC ‘y’ >> art [],
       (* goal 2 (of 4) *)
       Q.EXISTS_TAC ‘N’ >> rw [] (* now: interval_lowerbound (SND (h n)) < b *) \\
      ‘h n IN p /\ 0 < content (SND (h n))’ by PROVE_TAC [] \\
       Q.PAT_ASSUM ‘!x k. (x,k) IN p ==> _’
         (MP_TAC o (Q.SPECL [‘FST ((h :num -> real # (real set)) n)’,
                             ‘SND ((h :num -> real # (real set)) n)’])) >> rw [] \\
       rename1 ‘SND (h n) = interval [a0,b0]’ \\
       Know ‘interval [a0,b0] <> {}’
       >- (rw [GSYM MEMBER_NOT_EMPTY] \\
           Q.EXISTS_TAC ‘FST (h n)’ \\
           Know ‘(FST (h n),SND (h n)) IN p’ >- rw [] \\
           METIS_TAC []) >> DISCH_TAC \\
      ‘a0 <= b0’ by PROVE_TAC [INTERVAL_NE_EMPTY] \\
       Q.PAT_X_ASSUM ‘SND (h n) = interval[a0,b0]’
         (fn th => FULL_SIMP_TAC std_ss [th, CONTENT_CLOSED_INTERVAL, REAL_SUB_LT,
                                         INTERVAL_LOWERBOUND_NONEMPTY]) \\
       Q.PAT_X_ASSUM ‘interval [a0,b0] SUBSET interval [a,b]’ MP_TAC \\
       RW_TAC std_ss [SUBSET_INTERVAL] \\
       MATCH_MP_TAC REAL_LTE_TRANS >> Q.EXISTS_TAC ‘b0’ >> art [],
       (* goal 3 (of 4) *)
       Cases_on ‘n < N’ >> rw [] (* interval_lowerbound (SND (h n)) <= FST (h n) *) \\
      ‘h n IN p’ by PROVE_TAC [] \\
       Q.PAT_ASSUM ‘!x k. (x,k) IN p ==> _’
         (MP_TAC o (Q.SPECL [‘FST ((h :num -> real # (real set)) n)’,
                             ‘SND ((h :num -> real # (real set)) n)’])) >> rw [] \\
       rename1 ‘SND (h n) = interval [a0,b0]’ \\
       Know ‘interval [a0,b0] <> {}’
       >- (rw [GSYM MEMBER_NOT_EMPTY] \\
           Q.EXISTS_TAC ‘FST (h n)’ \\
           Know ‘(FST (h n),SND (h n)) IN p’ >- rw [] \\
           METIS_TAC []) >> DISCH_TAC \\
      ‘a0 <= b0’ by PROVE_TAC [INTERVAL_NE_EMPTY] \\
      ‘FST (h n) IN SND (h n)’ by rw [] \\
       Q.PAT_X_ASSUM ‘SND (h n) = interval[a0,b0]’
         (fn th => FULL_SIMP_TAC std_ss [th, INTERVAL_LOWERBOUND_NONEMPTY, IN_INTERVAL]),
       (* goal 4 (of 4) *)
       Cases_on ‘n < N’ >> reverse (rw []) >| (* 2 subgoals *)
       [ (* goal 4.1 (of 2): FST (h n) <= b *)
        ‘h n IN p’ by PROVE_TAC [] \\
         Q.PAT_ASSUM ‘!x k. (x,k) IN p ==> _’
           (MP_TAC o (Q.SPECL [‘FST ((h :num -> real # (real set)) n)’,
                               ‘SND ((h :num -> real # (real set)) n)’])) \\
         rw [] >> rename1 ‘SND (h n) = interval [a0,b0]’ \\
         Know ‘interval [a0,b0] <> {}’
         >- (rw [GSYM MEMBER_NOT_EMPTY] \\
             Q.EXISTS_TAC ‘FST (h n)’ \\
             Know ‘(FST (h n),SND (h n)) IN p’ >- rw [] \\
             METIS_TAC []) >> DISCH_TAC \\
        ‘a0 <= b0’ by PROVE_TAC [INTERVAL_NE_EMPTY] \\
        ‘FST (h n) IN SND (h n)’ by rw [] \\
         Q.PAT_X_ASSUM ‘SND (h n) = interval[a0,b0]’
           (fn th => FULL_SIMP_TAC std_ss [th, INTERVAL_LOWERBOUND_NONEMPTY,
                                           SUBSET_INTERVAL, IN_INTERVAL]) \\
         MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC ‘b0’ >> art [],
         (* goal 4.2 (of 2): FST (h n) <= interval_lowerbound (SND (h (SUC n))) *)
         MATCH_MP_TAC REAL_LE_TRANS \\
         Q.EXISTS_TAC ‘interval_upperbound (SND (h n))’ \\
         CONJ_TAC
         >- (‘h n IN p’ by PROVE_TAC [] \\
             Q.PAT_ASSUM ‘!x k. (x,k) IN p ==> _’
              (MP_TAC o (Q.SPECL [‘FST ((h :num -> real # (real set)) n)’,
                                  ‘SND ((h :num -> real # (real set)) n)’])) \\
             rw [] >> rename1 ‘SND (h n) = interval [a0,b0]’ \\
             Know ‘interval [a0,b0] <> {}’
             >- (rw [GSYM MEMBER_NOT_EMPTY] \\
                 Q.EXISTS_TAC ‘FST (h n)’ \\
                 Know ‘(FST (h n),SND (h n)) IN p’ >- rw [] \\
                 METIS_TAC []) >> DISCH_TAC \\
            ‘a0 <= b0’ by PROVE_TAC [INTERVAL_NE_EMPTY] \\
            ‘FST (h n) IN SND (h n)’ by rw [] \\
             Q.PAT_X_ASSUM ‘SND (h n) = interval[a0,b0]’
               (fn th => FULL_SIMP_TAC std_ss [th, INTERVAL_UPPERBOUND_NONEMPTY,
                                               IN_INTERVAL])) \\
         CCONTR_TAC >> FULL_SIMP_TAC bool_ss [GSYM real_lt] \\
        ‘interval_lowerbound (SND (h n)) < interval_lowerbound (SND (h (SUC n)))’ by rw [] \\
      (* stage work *)
        ‘h n IN p /\ h (SUC n) IN p /\ 0 < content (SND (h (SUC n)))’ by PROVE_TAC [] \\
         Q.PAT_X_ASSUM ‘!x1 k1 x2 k2. (x1,k1) IN p /\ (x2,k2) IN p /\ _ ==> P’
           (MP_TAC o (Q.SPECL [‘FST ((h :num -> real # (real set)) n)’,
                               ‘SND ((h :num -> real # (real set)) n)’,
                               ‘FST ((h :num -> real # (real set)) (SUC n))’,
                               ‘SND ((h :num -> real # (real set)) (SUC n))’])) \\
         simp [GSYM DISJOINT_DEF] \\
         Know ‘SND (h n) <> SND (h (SUC n))’ >- (CCONTR_TAC >> fs []) >> Rewr \\
         Q.PAT_ASSUM ‘!x k. (x,k) IN p ==> _’
           (MP_TAC o (Q.SPECL [‘FST ((h :num -> real # (real set)) n)’,
                               ‘SND ((h :num -> real # (real set)) n)’])) >> rw [] \\
         rename1 ‘SND (h n) = interval [a0,b0]’ \\
         Know ‘interval [a0,b0] <> {}’
         >- (rw [GSYM MEMBER_NOT_EMPTY] \\
             Q.EXISTS_TAC ‘FST (h n)’ \\
             Know ‘(FST (h n),SND (h n)) IN p’ >- rw [] \\
             METIS_TAC []) >> DISCH_TAC \\
        ‘a0 <= b0’ by PROVE_TAC [INTERVAL_NE_EMPTY] \\
         Q.PAT_X_ASSUM ‘SND (h n) = interval[a0,b0]’
           (fn th => FULL_SIMP_TAC std_ss [th, INTERVAL_UPPERBOUND_NONEMPTY,
                                               INTERVAL_LOWERBOUND_NONEMPTY]) \\
         Q.PAT_ASSUM ‘!x k. (x,k) IN p ==> _’
           (MP_TAC o (Q.SPECL [‘FST ((h :num -> real # (real set)) (SUC n))’,
                               ‘SND ((h :num -> real # (real set)) (SUC n))’])) \\
         rw [] >> rename1 ‘SND (h (SUC n)) = interval [a1,b1]’ \\
         Know ‘interval [a1,b1] <> {}’
         >- (rw [GSYM MEMBER_NOT_EMPTY] \\
             Q.EXISTS_TAC ‘FST (h (SUC n))’ \\
             Know ‘(FST (h (SUC n)),SND (h (SUC n))) IN p’ >- rw [] \\
             METIS_TAC []) >> DISCH_TAC \\
        ‘a1 <= b1’ by PROVE_TAC [INTERVAL_NE_EMPTY] \\
         Q.PAT_X_ASSUM ‘SND (h (SUC n)) = interval[a1,b1]’
           (fn th => FULL_SIMP_TAC std_ss [th, INTERVAL_LOWERBOUND_NONEMPTY,
                                           CONTENT_CLOSED_INTERVAL, REAL_SUB_LT]) \\
         rw [DISJOINT_ALT, INTERIOR_CLOSED_INTERVAL, IN_INTERVAL] \\
      (* ordering: a0 < a1 < b0,b1 *)
         Know ‘?z. max a0 a1 < z /\ z < min b0 b1’
         >- (MATCH_MP_TAC REAL_MEAN >> rw [REAL_MAX_LT, REAL_LT_MIN] \\ (* 2 subgoals *)
             MATCH_MP_TAC REAL_LT_TRANS >> Q.EXISTS_TAC ‘a1’ >> art []) \\
         RW_TAC std_ss [REAL_MAX_LT, REAL_LT_MIN] \\
         Q.EXISTS_TAC ‘z’ >> art [] ] ])
 >> DISCH_TAC
 (* advanced h-properties *)
 >> Know ‘!n. n < N /\ SUC n < N ==>
              interval_lowerbound (SND (h (SUC n))) = interval_upperbound (SND (h n))’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘L = IMAGE h (count N)’ K_TAC (* not needed here *) \\
    ‘interval_lowerbound (SND (h n)) < interval_lowerbound (SND (h (SUC n)))’ by rw [] \\
    ‘h n IN p /\ h (SUC n) IN p /\
     0 < content (SND (h n)) /\ 0 < content (SND (h (SUC n)))’ by PROVE_TAC [] \\
     Q.PAT_ASSUM ‘!x k. (x,k) IN p ==> x IN k /\ _’
       (MP_TAC o (Q.SPECL [‘FST ((h :num -> real # (real set)) n)’,
                           ‘SND ((h :num -> real # (real set)) n)’])) \\
     simp [] >> STRIP_TAC >> rename1 ‘SND (h n) = interval [a0,b0]’ \\
     Know ‘interval [a0,b0] <> {}’
     >- (rw [GSYM MEMBER_NOT_EMPTY] \\
         Q.EXISTS_TAC ‘FST (h n)’ \\
         Know ‘(FST (h n),SND (h n)) IN p’ >- rw [] \\
         METIS_TAC []) >> DISCH_TAC \\
    ‘a0 <= b0’ by PROVE_TAC [INTERVAL_NE_EMPTY] \\
     Q.PAT_ASSUM ‘!x k. (x,k) IN p ==> x IN k /\ _’
       (MP_TAC o (Q.SPECL [‘FST ((h :num -> real # (real set)) (SUC n))’,
                           ‘SND ((h :num -> real # (real set)) (SUC n))’])) \\
     simp [] >> STRIP_TAC >> rename1 ‘SND (h (SUC n)) = interval [a1,b1]’ \\
     Know ‘interval [a1,b1] <> {}’
     >- (rw [GSYM MEMBER_NOT_EMPTY] \\
         Q.EXISTS_TAC ‘FST (h (SUC n))’ \\
         Know ‘(FST (h (SUC n)),SND (h (SUC n))) IN p’ >- rw [] \\
         METIS_TAC []) >> DISCH_TAC \\
    ‘a1 <= b1’ by PROVE_TAC [INTERVAL_NE_EMPTY] \\
  (* move two assumptions to the bottom to use fs[] *)
     Q.PAT_X_ASSUM ‘SND (h n) = interval [a0,b0]’ ASSUME_TAC \\
     Q.PAT_X_ASSUM ‘SND (h (SUC n)) = interval [a1,b1]’ ASSUME_TAC \\
     FULL_SIMP_TAC bool_ss [INTERVAL_UPPERBOUND_NONEMPTY,
                            INTERVAL_LOWERBOUND_NONEMPTY,
                            INTERIOR_CLOSED_INTERVAL, SUBSET_INTERVAL,
                            IN_INTERVAL, CONTENT_CLOSED_INTERVAL, REAL_SUB_LT] \\
     Q.PAT_X_ASSUM ‘a0 <= b0’ K_TAC \\
     Q.PAT_X_ASSUM ‘a1 <= b1’ K_TAC \\
     CCONTR_TAC (* ordering: a0 <= b0 .. a1 <= b1 *) \\
    ‘a1 < b0 \/ b0 < a1’ by PROVE_TAC [REAL_LT_TOTAL] (* 2 subgoals, first easier *)
     >- (Q.PAT_X_ASSUM ‘a1 <> b0’ K_TAC \\
        ‘a1 < min b0 b1’ by rw [REAL_LT_MIN] (* a0 <= a1 < b0|b1 *) \\
        ‘?z. a1 < z /\ z < min b0 b1’ by METIS_TAC [REAL_MEAN] \\
        ‘a0 < z’ by PROVE_TAC [REAL_LT_TRANS] \\
         Q.PAT_ASSUM ‘!x1 k1 x2 k2. (x1,k1) IN p /\ (x2,k2) IN p /\ _ ==> P’
           (MP_TAC o (Q.SPECL [‘FST ((h :num -> real # (real set)) n)’,
                               ‘SND ((h :num -> real # (real set)) n)’,
                               ‘FST ((h :num -> real # (real set)) (SUC n))’,
                               ‘SND ((h :num -> real # (real set)) (SUC n))’])) \\
         simp [GSYM DISJOINT_DEF, EQ_INTERVAL, REAL_LT_IMP_NE] \\
         rw [DISJOINT_ALT, INTERIOR_CLOSED_INTERVAL, IN_INTERVAL] \\
         Q.EXISTS_TAC ‘z’ >> fs [REAL_LT_MIN]) \\
  (* ordering: a0 .. b0 < a1 < b1 *)
     Q.PAT_X_ASSUM ‘a1 <> b0’ K_TAC \\
  (* choose a good point *)
     Q.ABBREV_TAC ‘y = CHOICE (interval(b0,a1) DIFF Z)’ \\
     Know ‘y IN interval(b0,a1) DIFF Z’
     >- (Q.UNABBREV_TAC ‘y’ >> MATCH_MP_TAC CHOICE_DEF \\
         MATCH_MP_TAC INFINITE_DIFF_FINITE >> art [] \\
        ‘interval(b0,a1) <> {}’ by PROVE_TAC [INTERVAL_NE_EMPTY] \\
         PROVE_TAC [finite_countable, UNCOUNTABLE_INTERVAL]) >> DISCH_TAC \\
    ‘y NOTIN Z’ by (Q.PAT_X_ASSUM ‘y IN interval(b0,a1) DIFF Z’ MP_TAC >> rw []) \\
     Know ‘b0 < y /\ y < a1’
     >- (Q.PAT_X_ASSUM ‘y IN interval(b0,a1) DIFF Z’ MP_TAC \\
         rw [IN_DIFF, IN_INTERVAL]) >> STRIP_TAC \\
  (* now find the "impossible" division covering y *)
     Q.PAT_X_ASSUM ‘BIGUNION _ = interval [a,b]’ MP_TAC \\
     simp [Once EXTENSION, IN_INTERVAL, IN_BIGUNION, Abbr ‘E’] \\
     CCONTR_TAC >> FULL_SIMP_TAC bool_ss [] \\
     POP_ASSUM (MP_TAC o (Q.SPEC ‘y’)) \\
     Know ‘a <= y /\ y <= b’
     >- (METIS_TAC [REAL_LE_TRANS, REAL_LET_TRANS, REAL_LT_IMP_LE]) >> Rewr \\
     CCONTR_TAC >> FULL_SIMP_TAC bool_ss [] >> rename1 ‘(x,s) IN p’ \\
    ‘x IN Z’ by (rw [Abbr ‘Z’] >> Q.EXISTS_TAC ‘s’ >> art []) \\
     Know ‘(x,s) IN L’
     >- (simp [Abbr ‘L’] (* now ‘0 < content s’ *) \\
         Q.PAT_X_ASSUM ‘!x k. (x,k) IN p ==> x IN k /\ _’ (MP_TAC o (Q.SPECL [‘x’, ‘s’])) \\
         simp [] >> STRIP_TAC >> rename1 ‘s = interval[a2,b2]’ \\
        ‘interval [a2,b2] <> {}’ by METIS_TAC [MEMBER_NOT_EMPTY] \\
        ‘a2 <= b2’ by PROVE_TAC [INTERVAL_NE_EMPTY] \\
         Suff ‘content (interval[a2,b2]) <> 0’
         >- (rw [REAL_LT_LE, CONTENT_POS_LE]) \\
         CCONTR_TAC >> FULL_SIMP_TAC bool_ss [CONTENT_EQ_0] \\
        ‘b2 = a2’ by PROVE_TAC [REAL_LE_ANTISYM] \\
         fs [INTERVAL_SING, IN_SING]) >> DISCH_TAC \\
     Know ‘0 < content s’
     >- (POP_ASSUM MP_TAC >> simp [Abbr ‘L’]) >> DISCH_TAC \\
    ‘?m. m < N /\ (x,s) = h m’ by METIS_TAC [] (* this ‘m’ is between ‘n’ and ‘SUC n’ *) \\
     Q.PAT_ASSUM ‘!x k. (x,k) IN p ==> x IN k /\ _’ (MP_TAC o (Q.SPECL [‘x’, ‘s’])) \\
     simp [] >> CCONTR_TAC >> FULL_SIMP_TAC bool_ss [] \\
     rename1 ‘s = interval [a2,b2]’ \\
    ‘interval [a2,b2] <> {}’ by PROVE_TAC [MEMBER_NOT_EMPTY] \\
    ‘a2 <= b2’ by PROVE_TAC [INTERVAL_NE_EMPTY] \\
     Q.PAT_X_ASSUM ‘s = interval [a2,b2]’
       (fn th => FULL_SIMP_TAC bool_ss [th, SUBSET_INTERVAL, IN_INTERVAL,
                                            CONTENT_CLOSED_INTERVAL, REAL_SUB_LT]) \\
     Q.PAT_X_ASSUM ‘a2 <= b2’ K_TAC \\
     Know ‘SND (h m) = interval[a2,b2]’
     >- (Q.PAT_X_ASSUM ‘(x,interval[a2,b2]) = h m’
           (ONCE_REWRITE_TAC o wrap o SYM) >> rw []) >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘(x,interval[a2,b2]) = h m’ K_TAC \\
  (* ordering: a0 < b0 .. a2 < y < b2 .. a1 < b1 *)
     Suff ‘b0 <= a2 /\ b2 <= a1’
     >- (STRIP_TAC \\
        ‘a0 < a2 /\ a2 < a1’ by PROVE_TAC [REAL_LET_TRANS, REAL_LTE_TRANS] \\
         Know ‘n <= m’
         >- (SPOSE_NOT_THEN (ASSUME_TAC o (REWRITE_RULE [NOT_LESS_EQUAL])) \\
             Q.PAT_X_ASSUM ‘!i j. i < N /\ j < N /\ i < j ==> P’
               (MP_TAC o (Q.SPECL [‘m’, ‘n’])) \\
             simp [INTERVAL_LOWERBOUND_NONEMPTY] \\
             METIS_TAC [REAL_LT_ANTISYM]) >> DISCH_TAC \\
         Know ‘m <= SUC n’
         >- (SPOSE_NOT_THEN (ASSUME_TAC o (REWRITE_RULE [NOT_LESS_EQUAL])) \\
             Q.PAT_X_ASSUM ‘!i j. i < N /\ j < N /\ i < j ==> P’
               (MP_TAC o (Q.SPECL [‘SUC n’, ‘m’])) \\
             simp [INTERVAL_LOWERBOUND_NONEMPTY] \\
             METIS_TAC [REAL_LT_ANTISYM]) >> DISCH_TAC \\
         Know ‘m = n \/ m = SUC n’
         >- (MATCH_MP_TAC
              (ARITH_PROVE “n <= m /\ m <= SUC n ==> m = n \/ m = SUC n”) >> art []) \\
         STRIP_TAC >> gs [EQ_INTERVAL]) \\
     CONJ_TAC \\
     SPOSE_NOT_THEN (ASSUME_TAC o (REWRITE_RULE [GSYM real_lt])) >| (* 2 subgoals *)
     [ (* goal 1.1 (of 2): a2 < b0 |- F, order: a0|a2 < b0|b2 *)
       Know ‘max a0 a2 < min b0 b2’
       >- (simp [REAL_LT_MIN, REAL_MAX_LT] \\
           MATCH_MP_TAC REAL_LTE_TRANS >> Q.EXISTS_TAC ‘y’ >> art [] \\
           MATCH_MP_TAC REAL_LT_TRANS >> Q.EXISTS_TAC ‘b0’ >> art []) >> DISCH_TAC \\
      ‘?z. max a0 a2 < z /\ z < min b0 b2’ by METIS_TAC [REAL_MEAN] \\
       Q.PAT_ASSUM ‘!x1 k1 x2 k2. (x1,k1) IN p /\ (x2,k2) IN p /\ _ ==> P’
         (MP_TAC o (Q.SPECL [‘FST ((h :num -> real # (real set)) n)’,
                             ‘SND ((h :num -> real # (real set)) n)’,
                             ‘FST ((h :num -> real # (real set)) m)’,
                             ‘SND ((h :num -> real # (real set)) m)’])) \\
       simp [GSYM DISJOINT_DEF, EQ_INTERVAL] \\
       Know ‘b0 <> b2’ >- (CCONTR_TAC >> METIS_TAC [REAL_LET_ANTISYM]) >> Rewr \\
       rw [DISJOINT_ALT, INTERIOR_CLOSED_INTERVAL, IN_INTERVAL] \\
       Q.EXISTS_TAC ‘z’ >> fs [REAL_LT_MIN, REAL_MAX_LT],
       (* goal 1.2 (of 2): a1 < b2 |- F, order: a2|a1 < b2|b1 *)
       Know ‘max a2 a1 < min b2 b1’
       >- (simp [REAL_LT_MIN, REAL_MAX_LT] \\
           MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC ‘y’ >> art [] \\
           MATCH_MP_TAC REAL_LT_TRANS >> Q.EXISTS_TAC ‘a1’ >> art []) >> DISCH_TAC \\
      ‘?z. max a2 a1 < z /\ z < min b2 b1’ by METIS_TAC [REAL_MEAN] \\
       Q.PAT_ASSUM ‘!x1 k1 x2 k2. (x1,k1) IN p /\ (x2,k2) IN p /\ _ ==> P’
         (MP_TAC o (Q.SPECL [‘FST ((h :num -> real # (real set)) m)’,
                             ‘SND ((h :num -> real # (real set)) m)’,
                             ‘FST ((h :num -> real # (real set)) (SUC n))’,
                             ‘SND ((h :num -> real # (real set)) (SUC n))’])) \\
       simp [GSYM DISJOINT_DEF, EQ_INTERVAL] \\
       Know ‘a2 <> a1’ >- (CCONTR_TAC >> METIS_TAC [REAL_LET_ANTISYM]) >> Rewr \\
       rw [DISJOINT_ALT, INTERIOR_CLOSED_INTERVAL, IN_INTERVAL] \\
       Q.EXISTS_TAC ‘z’ >> fs [REAL_LT_MIN, REAL_MAX_LT] ])
 >> DISCH_TAC
 (* advanced h-properties *)
 >> Know ‘!n. n < N /\ ~(SUC n < N) ==> interval_upperbound (SND (h n)) = b’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘L = IMAGE h (count N)’ K_TAC (* not needed here *) \\
     Q.PAT_X_ASSUM ‘tdiv (a,b) (D,t)’ K_TAC \\
     qunabbrevl_tac [‘D’, ‘t’] \\
     Q.PAT_X_ASSUM ‘BIGUNION _ = interval [a,b]’ MP_TAC \\
     rw [Once EXTENSION, IN_INTERVAL, IN_BIGUNION, Abbr ‘E’] \\
    ‘h n IN p /\ 0 < content (SND (h n))’ by PROVE_TAC [] \\
     Q.PAT_ASSUM ‘!x k. (x,k) IN p ==> x IN k /\ _’
       (MP_TAC o (Q.SPECL [‘FST ((h :num -> real # (real set)) n)’,
                           ‘SND ((h :num -> real # (real set)) n)’])) >> rw [] \\
     rename1 ‘SND (h n) = interval [a0,b0]’ \\
     Know ‘interval [a0,b0] <> {}’
     >- (rw [GSYM MEMBER_NOT_EMPTY] >> Q.EXISTS_TAC ‘FST (h n)’ \\
         Know ‘(FST (h n),SND (h n)) IN p’ >- rw [] \\
         METIS_TAC []) >> DISCH_TAC \\
    ‘a0 <= b0’ by PROVE_TAC [INTERVAL_NE_EMPTY] \\
     FULL_SIMP_TAC bool_ss [INTERVAL_UPPERBOUND_NONEMPTY, SUBSET_INTERVAL,
                            CONTENT_CLOSED_INTERVAL, REAL_SUB_LT] (* b0 = b *) \\
     CCONTR_TAC >> ‘b < b0 \/ b0 < b’ by PROVE_TAC [REAL_LT_TOTAL] (* 2 subgoals *)
     >- (Q.PAT_X_ASSUM ‘b0 <> b’ K_TAC \\
         Q.PAT_X_ASSUM ‘!x. _ <=> a <= x /\ x <= b’ (MP_TAC o (Q.SPEC ‘b0’)) \\
         Suff ‘?s. b0 IN s /\ ?x. (x,s) IN p’ >- (Rewr >> rw [GSYM real_lt]) \\
         Q.EXISTS_TAC ‘SND (h n)’ \\
         ONCE_REWRITE_TAC [CONJ_COMM] \\
         CONJ_TAC >- (Q.EXISTS_TAC ‘FST (h n)’ >> rw []) \\
         Q.PAT_X_ASSUM ‘SND (h n) = interval _’ (ONCE_REWRITE_TAC o wrap) \\
         rw [IN_INTERVAL]) \\
     Q.PAT_X_ASSUM ‘b0 <> b’ K_TAC \\
  (* stage work *)
    ‘a <= b0’ by PROVE_TAC [REAL_LE_TRANS] \\
     Q.ABBREV_TAC ‘y = CHOICE (interval(b0,b) DIFF Z)’ \\
     Know ‘y IN interval(b0,b) DIFF Z’
     >- (Q.UNABBREV_TAC ‘y’ >> MATCH_MP_TAC CHOICE_DEF \\
         MATCH_MP_TAC INFINITE_DIFF_FINITE >> art [] \\
        ‘interval(b0,b) <> {}’ by PROVE_TAC [INTERVAL_NE_EMPTY] \\
         PROVE_TAC [finite_countable, UNCOUNTABLE_INTERVAL]) >> DISCH_TAC \\
     Know ‘b0 < y /\ y < b’
     >- (POP_ASSUM MP_TAC >> rw [IN_DIFF, IN_INTERVAL]) >> STRIP_TAC \\
    ‘a < y’ by PROVE_TAC [REAL_LET_TRANS] \\
     Q.PAT_X_ASSUM ‘!x. _ <=> a <= x /\ x <= b’ (MP_TAC o (Q.SPEC ‘y’)) \\
     Know ‘a <= y /\ y <= b’ >- PROVE_TAC [REAL_LT_IMP_LE] >> Rewr \\
     CCONTR_TAC >> FULL_SIMP_TAC bool_ss [] >> rename1 ‘(x,s) IN p’ \\
    ‘x IN Z’ by (rw [Abbr ‘Z’] >> Q.EXISTS_TAC ‘s’ >> art []) \\
  (* now we show that (x,s) IN L. But first of all, ‘s’ cannot be degenerate,
     since otherwise we will have x = y, but this is impossible. *)
     Know ‘(x,s) IN L’
     >- (rw [Abbr ‘L’] (* now ‘0 < content s’ *) \\
         Q.PAT_X_ASSUM ‘!x k. (x,k) IN p ==> x IN k /\ _’ (MP_TAC o (Q.SPECL [‘x’, ‘s’])) \\
         RW_TAC std_ss [] >> rename1 ‘(x,interval[a1,b1]) IN p’ \\
        ‘interval [a1,b1] <> {}’ by METIS_TAC [MEMBER_NOT_EMPTY] \\
        ‘a1 <= b1’ by PROVE_TAC [INTERVAL_NE_EMPTY] \\
         Suff ‘content (interval[a1,b1]) <> 0’
         >- (rw [REAL_LT_LE, CONTENT_POS_LE]) \\
         CCONTR_TAC >> FULL_SIMP_TAC bool_ss [CONTENT_EQ_0] \\
        ‘b1 = a1’ by PROVE_TAC [REAL_LE_ANTISYM] \\
         fs [INTERVAL_SING, IN_SING]) >> DISCH_TAC \\
    ‘?m. m < N /\ (x,s) = h m’ by METIS_TAC [] \\
  (* ordering: (a, y, [a0,b0], b) *)
    ‘m = n \/ m < n’ by rw []
     >- (Know ‘s = SND (h m)’
         >- (Q.PAT_X_ASSUM ‘(x,s) = h m’ (ONCE_REWRITE_TAC o wrap o SYM) >> rw []) \\
         DISCH_TAC \\
         Know ‘y IN interval [a0,b0]’ >- METIS_TAC [] \\
         fs [IN_INTERVAL, GSYM real_lt]) \\
     Q.PAT_X_ASSUM ‘!x k. (x,k) IN p ==> x IN k /\ _’ (MP_TAC o (Q.SPECL [‘x’,‘s’])) \\
     RW_TAC std_ss [] \\
     CCONTR_TAC >> FULL_SIMP_TAC bool_ss [] >> rename1 ‘s = interval[a1,b1]’ \\
    ‘interval [a1,b1] <> {}’ by METIS_TAC [MEMBER_NOT_EMPTY] \\
    ‘a1 <= b1’ by PROVE_TAC [INTERVAL_NE_EMPTY] \\
  (* stage work *)
     Know ‘interval_lowerbound (SND (h m)) < interval_lowerbound (SND (h n))’ >- rw [] \\
     Know ‘SND (h m) = interval[a1,b1]’
     >- (Q.PAT_X_ASSUM ‘(x,s) = h m’ (ONCE_REWRITE_TAC o wrap o SYM) >> rw []) \\
     DISCH_TAC >> art [] >> Q.PAT_X_ASSUM ‘(x,s) = h m’ K_TAC \\
     rw [INTERVAL_LOWERBOUND_NONEMPTY, real_lt] \\
     FULL_SIMP_TAC bool_ss [SUBSET_INTERVAL, IN_INTERVAL] \\
     SPOSE_NOT_THEN (ASSUME_TAC o (REWRITE_RULE [GSYM real_lt])) (* a1 < a0 *) \\
    ‘b0 < b1’ by PROVE_TAC [REAL_LTE_TRANS] \\
  (* ordering: (a1, (a0, b0), b1) *)
     Q.PAT_ASSUM ‘!x1 k1 x2 k2. (x1,k1) IN p /\ (x2,k2) IN p /\ _ ==> P’
       (MP_TAC o (Q.SPECL [‘FST ((h :num -> real # (real set)) m)’,
                           ‘SND ((h :num -> real # (real set)) m)’,
                           ‘FST ((h :num -> real # (real set)) n)’,
                           ‘SND ((h :num -> real # (real set)) n)’])) \\
     simp [GSYM DISJOINT_DEF, EQ_INTERVAL] \\
     Know ‘a1 <> a0’ >- (CCONTR_TAC >> METIS_TAC [REAL_LT_IMP_NE]) >> Rewr \\
     rw [DISJOINT_ALT, INTERIOR_CLOSED_INTERVAL, IN_INTERVAL] \\
    ‘?z. a0 < z /\ z < b0’ by METIS_TAC [REAL_MEAN] \\
     Q.EXISTS_TAC ‘z’ >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC REAL_LT_TRANS >> Q.EXISTS_TAC ‘a0’ >> art [],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC REAL_LT_TRANS >> Q.EXISTS_TAC ‘b0’ >> art [] ])
 >> DISCH_TAC
 (* stage work *)
 >> Know ‘dsize D = N /\ fine g (D,t)’
 >- (Q.PAT_X_ASSUM ‘tdiv (a,b) (D,t)’     MP_TAC \\
     Q.PAT_X_ASSUM ‘d FINE p’             MP_TAC \\
     Q.PAT_X_ASSUM ‘L = IMAGE h (count N)’ K_TAC (* not needed here *) \\
     SIMP_TAC std_ss [tdiv, division, fine, FINE] >> NTAC 2 STRIP_TAC \\
     rename1 ‘!n. n >= M ==> D n = b’ \\
     Know ‘M = N’
     >- (CCONTR_TAC >> ‘N < M \/ M < N’ by fs []
         >- (Q.PAT_X_ASSUM ‘!n. n < M ==> D n < D (SUC n)’ (MP_TAC o (Q.SPEC ‘N’)) \\
            ‘D N = b /\ D (SUC N) = b’ by rw [Abbr ‘D’] >> rw []) \\
        ‘h M IN p /\ 0 < content (SND (h M))’ by PROVE_TAC [] \\
         Q.PAT_ASSUM ‘!x k. (x,k) IN p ==> x IN k /\ _’
           (MP_TAC o (Q.SPECL [‘FST ((h :num -> real # (real set)) M)’,
                               ‘SND ((h :num -> real # (real set)) M)’])) \\
         rw [] >> CCONTR_TAC >> fs [] \\
         rename1 ‘SND (h M) = interval [a0,b0]’ \\
         Know ‘interval [a0,b0] <> {}’
         >- (rw [GSYM MEMBER_NOT_EMPTY] \\
             Q.EXISTS_TAC ‘FST (h M)’ \\
             Know ‘(FST (h M),SND (h M)) IN p’ >- rw [] \\
             METIS_TAC []) >> DISCH_TAC \\
        ‘a0 <= b0’ by PROVE_TAC [INTERVAL_NE_EMPTY] \\
         Know ‘interval_lowerbound (SND (h M)) = D M’
         >- (Q.UNABBREV_TAC ‘D’ >> BETA_TAC >> art []) \\
        ‘D M = b’ by rw [Abbr ‘D’] >> POP_ASSUM (REWRITE_TAC o wrap) \\
         Q.PAT_X_ASSUM ‘SND (h M) = interval[a0,b0]’
           (fn th => FULL_SIMP_TAC std_ss [th, CONTENT_CLOSED_INTERVAL, SUBSET_INTERVAL,
                                           INTERVAL_LOWERBOUND_NONEMPTY, REAL_SUB_LT]) \\
         CCONTR_TAC >> METIS_TAC [REAL_LET_ANTISYM]) \\
     DISCH_THEN (FULL_SIMP_TAC bool_ss o wrap) \\
     STRONG_CONJ_TAC (* dsize D = N *)
     >- (REWRITE_TAC [dsize] >> SELECT_ELIM_TAC \\
         CONJ_TAC >- (Q.EXISTS_TAC ‘N’ >> rw []) \\
         Q.X_GEN_TAC ‘M’ >> rpt STRIP_TAC \\
         CCONTR_TAC >> ‘N < M \/ M < N’ by fs []
         >- (‘D N = b /\ D (SUC N) = b’ by rw [Abbr ‘D’] \\
             Q.PAT_X_ASSUM ‘!n. n < M ==> D n < D (SUC n)’ (MP_TAC o (Q.SPEC ‘N’)) \\
             rw []) \\
        ‘h M IN p /\ 0 < content (SND (h M))’ by PROVE_TAC [] \\
         Q.PAT_ASSUM ‘!x k. (x,k) IN p ==> x IN k /\ _’
           (MP_TAC o (Q.SPECL [‘FST ((h :num -> real # (real set)) M)’,
                               ‘SND ((h :num -> real # (real set)) M)’])) \\
         rw [] >> CCONTR_TAC >> fs [] \\
         rename1 ‘SND (h M) = interval [a0,b0]’ \\
         Know ‘interval [a0,b0] <> {}’
         >- (rw [GSYM MEMBER_NOT_EMPTY] \\
             Q.EXISTS_TAC ‘FST (h M)’ \\
             Know ‘(FST (h M),SND (h M)) IN p’ >- rw [] \\
             METIS_TAC []) >> DISCH_TAC \\
        ‘a0 <= b0’ by PROVE_TAC [INTERVAL_NE_EMPTY] \\
         Know ‘interval_lowerbound (SND (h M)) = D M’
         >- (Q.UNABBREV_TAC ‘D’ >> BETA_TAC >> art []) \\
         Know ‘D M = b’ (* here the difference *)
         >- (FIRST_X_ASSUM MATCH_MP_TAC \\
             Q.EXISTS_TAC ‘N’ >> rw []) >> DISCH_THEN (REWRITE_TAC o wrap) \\
         Q.PAT_X_ASSUM ‘SND (h M) = interval[a0,b0]’
           (fn th => FULL_SIMP_TAC std_ss [th, CONTENT_CLOSED_INTERVAL, SUBSET_INTERVAL,
                                           INTERVAL_LOWERBOUND_NONEMPTY, REAL_SUB_LT]) \\
         CCONTR_TAC >> METIS_TAC [REAL_LET_ANTISYM]) \\
     DISCH_THEN (FULL_SIMP_TAC bool_ss o wrap) \\
  (* stage work: !n. n < N ==> D (SUC n) - D n < g (t n) *)
     rpt STRIP_TAC \\
    ‘D n = interval_lowerbound (SND (h n))’ by rw [Abbr ‘D’] >> POP_ORW \\
     Know ‘D (SUC n) = interval_upperbound (SND (h n))’
     >- (Cases_on ‘SUC n < N’ >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
          ‘D (SUC n) = interval_lowerbound (SND (h (SUC n)))’ by rw [Abbr ‘D’] >> POP_ORW \\
           FIRST_X_ASSUM MATCH_MP_TAC >> art [],
           (* goal 2 (of 2) *)
          ‘D (SUC n) = b’ by rw [Abbr ‘D’] >> POP_ORW \\
           ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
           FIRST_X_ASSUM MATCH_MP_TAC >> art [] ]) >> Rewr' \\
  (* stage work *)
    ‘h n IN p’ by PROVE_TAC [] \\
     Q.PAT_X_ASSUM ‘!x k. (x,k) IN p ==> x IN k /\ _’
      (MP_TAC o (Q.SPECL [‘FST ((h :num -> real # (real set)) n)’,
                          ‘SND ((h :num -> real # (real set)) n)’])) \\
     Q.PAT_X_ASSUM ‘!x k. (x,k) IN p ==> k SUBSET (d x)’
      (MP_TAC o (Q.SPECL [‘FST ((h :num -> real # (real set)) n)’,
                          ‘SND ((h :num -> real # (real set)) n)’])) \\
     simp [Abbr ‘t’] >> rpt STRIP_TAC \\
     rename1 ‘SND (h n) = interval [a0,b0]’ \\
    ‘interval [a0,b0] <> {}’ by METIS_TAC [MEMBER_NOT_EMPTY] \\
    ‘a0 <= b0’ by PROVE_TAC [INTERVAL_NE_EMPTY] \\
     Q.ABBREV_TAC ‘x = FST (h n)’ \\
     Q.PAT_X_ASSUM ‘SND (h n) = interval [a0,b0]’
       (fn th => FULL_SIMP_TAC std_ss [th, SUBSET_INTERVAL, IN_INTERVAL,
                                       INTERVAL_UPPERBOUND_NONEMPTY,
                                       INTERVAL_LOWERBOUND_NONEMPTY]) \\
    ‘a <= x /\ x <= b’ by PROVE_TAC [REAL_LE_TRANS] \\
     Q.PAT_X_ASSUM ‘interval[a0,b0] SUBSET (d x)’ MP_TAC \\
  (* final stage using ‘d’ *)
     rw [Abbr ‘d’, Abbr ‘E’, BALL, SUBSET_INTERVAL] \\
    ‘-a0 < -(x - 1 / 2 * g x)’ by PROVE_TAC [REAL_LT_NEG] \\
     Know ‘b0 + -a0 < (x + 1 / 2 * g x) + -(x - 1 / 2 * g x)’
     >- (MATCH_MP_TAC REAL_LT_ADD2 >> art []) \\
     simp [GSYM real_sub, REAL_ARITH “a + b - (a - b) = 2 * b”])
 >> STRIP_TAC
 (* stage work *)
 >> Q.PAT_X_ASSUM ‘!D p. tdiv (a,b) (D,p) /\ fine g (D,p) ==> P’ drule_all
 (* convert all sums to SIGMA (REAL_SUM_IMAGE) *)
 >> simp [rsum, GSYM REAL_SUM_IMAGE_sum, GSYM REAL_SUM_IMAGE_COUNT]
 >> Suff ‘SIGMA (\n. f (t n) * (D (SUC n) - D n)) (count N) =
          SIGMA (\(x,k). f x * content k) p’ >- Rewr
 (* SIGMA ... (count N) = SIGMA ... p, but first we need to turn ‘p’ to ‘L’ *)
 >> Know ‘SIGMA (\(x,k). f x * content k) p = SIGMA (\(x,k). f x * content k) L’
 >- (Q.PAT_X_ASSUM ‘L = IMAGE h (count N)’ K_TAC (* not useful here *) \\
     Q.ABBREV_TAC ‘V = {(x,k) | (x,k) IN p /\ content k = 0}’ \\
     Know ‘FINITE V’
     >- (MATCH_MP_TAC SUBSET_FINITE_I >> Q.EXISTS_TAC ‘p’ \\
         rw [Abbr ‘V’, SUBSET_DEF] >> art []) >> DISCH_TAC \\
     Know ‘p = L UNION V’
     >- (rw [Once EXTENSION, Abbr ‘L’, Abbr ‘V’] >> Cases_on ‘x’ \\
         EQ_TAC >> STRIP_TAC >> fs [] >> rename1 ‘(x,k) IN p’ \\
         Q.PAT_X_ASSUM ‘!x k. (x,k) IN p ==> x IN k /\ _’ (MP_TAC o (Q.SPECL [‘x’, ‘k’])) \\
         simp [] >> STRIP_TAC >> rename1 ‘k = interval[a0,b0]’ \\
        ‘interval [a0,b0] <> {}’ by METIS_TAC [MEMBER_NOT_EMPTY] \\
        ‘a0 <= b0’ by PROVE_TAC [INTERVAL_NE_EMPTY] \\
        ‘0 <= content k’ by METIS_TAC [CONTENT_POS_LE] \\
         fs [REAL_LE_LT]) >> Rewr' \\
     Know ‘DISJOINT L V’
     >- (rw [Abbr ‘L’, Abbr ‘V’, DISJOINT_ALT] >> rename1 ‘(x,k) IN p’ \\
         CCONTR_TAC >> fs []) >> DISCH_TAC \\
     Know ‘SIGMA (\(x,k). f x * content k) (L UNION V) =
           SIGMA (\(x,k). f x * content k) L +
           SIGMA (\(x,k). f x * content k) V’
     >- (MATCH_MP_TAC REAL_SUM_IMAGE_DISJOINT_UNION >> art []) >> Rewr' \\
     Suff ‘SIGMA (\(x,k). f x * content k) V = 0’ >- rw [] \\
     rw [REAL_SUM_IMAGE_sum] >> MATCH_MP_TAC SUM_EQ_0' \\
     rw [Abbr ‘V’] >> rename1 ‘(x,k) IN p’ >> rw [])
 >> Rewr'
 (* finally this is used *)
 >> Q.PAT_X_ASSUM ‘L = IMAGE h (count N)’ (ONCE_REWRITE_TAC o wrap)
 >> Know ‘SIGMA (\(x,k). f x * content k) (IMAGE h (count N)) =
          SIGMA ((\(x,k). f x * content k) o h) (count N)’
 >- (irule REAL_SUM_IMAGE_IMAGE >> simp [INJ_DEF] \\
     qx_genl_tac [‘i’, ‘j’] >> rpt STRIP_TAC \\
    ‘h i IN p /\ h j IN p’ by PROVE_TAC [] \\
     Q.PAT_ASSUM ‘!x k. (x,k) IN p ==> x IN k /\ _’
      (MP_TAC o (Q.SPECL [‘FST ((h :num -> real # (real set)) i)’,
                          ‘SND ((h :num -> real # (real set)) i)’])) \\
     simp [] >> STRIP_TAC >> rename1 ‘SND (h j) = interval[a0,b0]’ \\
     Know ‘interval [a0,b0] <> {}’
     >- (rw [GSYM MEMBER_NOT_EMPTY] \\
         Q.EXISTS_TAC ‘FST (h j)’ \\
         Know ‘(FST (h j),SND (h j)) IN p’ >- rw [] \\
         METIS_TAC []) >> DISCH_TAC \\
    ‘a0 <= b0’ by PROVE_TAC [INTERVAL_NE_EMPTY] \\
     CCONTR_TAC >> ‘i < j \/ j < i’ by rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
      ‘interval_lowerbound (SND (h i)) < interval_lowerbound (SND (h j))’ by PROVE_TAC [] \\
       METIS_TAC [INTERVAL_LOWERBOUND_NONEMPTY, REAL_LT_REFL],
       (* goal 2 (of 2) *)
      ‘interval_lowerbound (SND (h j)) < interval_lowerbound (SND (h i))’ by PROVE_TAC [] \\
       METIS_TAC [INTERVAL_LOWERBOUND_NONEMPTY, REAL_LT_REFL] ])
 >> Rewr'
 >> MATCH_MP_TAC REAL_SUM_IMAGE_EQ >> simp [Abbr ‘t’]
 >> Q.X_GEN_TAC ‘n’ >> STRIP_TAC
 >> ‘h n IN p’ by PROVE_TAC []
 >> Q.PAT_ASSUM ‘!x k. (x,k) IN p ==> x IN k /\ _’
      (MP_TAC o (Q.SPECL [‘FST ((h :num -> real # (real set)) n)’,
                          ‘SND ((h :num -> real # (real set)) n)’]))
 >> simp [] >> STRIP_TAC
 >> rename1 ‘SND (h n) = interval[a0,b0]’
 >> Know ‘interval [a0,b0] <> {}’
 >- (rw [GSYM MEMBER_NOT_EMPTY] \\
     Q.EXISTS_TAC ‘FST (h n)’ \\
     Know ‘(FST (h n),SND (h n)) IN p’ >- rw [] \\
     METIS_TAC [])
 >> DISCH_TAC
 >> ‘a0 <= b0’ by PROVE_TAC [INTERVAL_NE_EMPTY]
 >> Q.ABBREV_TAC ‘x = FST (h n)’
 >> Know ‘h n = (x,interval[a0,b0])’
 >- (rw [Abbr ‘x’] \\
     Q.PAT_X_ASSUM ‘SND (h n) = interval [a0,b0]’
      (ONCE_REWRITE_TAC o wrap o SYM) >> simp [])
 >> Rewr'
 >> ASM_SIMP_TAC std_ss [CONTENT_CLOSED_INTERVAL]
 >> Suff ‘D (SUC n) - D n = b0 - a0’ >- rw []
 >> Cases_on ‘SUC n < N’
 >- rw [Abbr ‘D’, INTERVAL_UPPERBOUND_NONEMPTY, INTERVAL_LOWERBOUND_NONEMPTY]
 (* ~(SUC n < N) *)
 >> rw [Abbr ‘D’, INTERVAL_LOWERBOUND_NONEMPTY]
 >> Suff ‘b0 = b’ >- rw []
 >> Know ‘interval_upperbound (SND (h n)) = b’
 >- (FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> Q.PAT_X_ASSUM ‘SND (h n) = interval [a0,b0]’ (ONCE_REWRITE_TAC o wrap)
 >> simp [INTERVAL_UPPERBOUND_NONEMPTY]
QED

Theorem lemma1[local] :
    !xs. FST xs IN SND xs /\ open (SND xs) ==> ?e. 0 < e /\ cball (FST xs,e) SUBSET (SND xs)
Proof
    rw [OPEN_CONTAINS_CBALL]
QED

(* h is a cball generator of open sets *)
Theorem lemma2[local] :
    ?h. !x s. x IN s /\ open s ==> 0 < h(x,s) /\ cball (x,h(x,s)) SUBSET s
Proof
    STRIP_ASSUME_TAC (SIMP_RULE std_ss [EXT_SKOLEM_THM'] lemma1)
 >> Q.EXISTS_TAC ‘f’
 >> rpt STRIP_TAC
 >> Q.PAT_X_ASSUM ‘!xs. P’ (MP_TAC o (Q.SPEC ‘(x,s)’))
 >> rw []
QED

(* Part 2: from new integrals to old integrals *)
Theorem has_integral_imp_Dint[local] :
    !f a b k. a < b /\ (f has_integral k) (interval[a,b]) ==> Dint(a,b) f k
Proof
    RW_TAC std_ss [Dint, has_integral]
 >> Q.PAT_X_ASSUM ‘!e. 0 < e ==> P’ (MP_TAC o (Q.SPEC ‘e’)) >> rw []
 >> Q.ABBREV_TAC ‘E = \x. a <= x /\ x <= b’
 (* Unlike the case of ‘Dint_imp_has_integral’, the most difficult part here
    is the construction of old gauges from new guages. *)
 >> STRIP_ASSUME_TAC lemma2 (* this asserts ‘h’ *)
 >> Q.ABBREV_TAC ‘cb = \x. cball (x,h(x,d x))’
 >> Q.ABBREV_TAC ‘g = \x. 1 / 2 * (interval_upperbound (cb x) - interval_lowerbound (cb x))’
 >> Q.EXISTS_TAC ‘g’
 >> STRONG_CONJ_TAC (* gauge E g *)
 >- (FULL_SIMP_TAC std_ss [gauge, gauge_def] \\
     rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!x. x IN d x /\ open (d x)’ (MP_TAC o (Q.SPEC ‘x’)) >> rw [] \\
     rw [Abbr ‘g’, Abbr ‘cb’, CBALL_INTERVAL, REAL_SUB_LT] \\
     Q.ABBREV_TAC ‘r = h (x,d x)’ \\
    ‘0 < r’ by rw [Abbr ‘r’] \\
     Know ‘x - r < x + r’
     >- (MATCH_MP_TAC REAL_LT_TRANS \\
         Q.EXISTS_TAC ‘x’ >> rw [REAL_LT_SUB_RADD]) >> DISCH_TAC \\
    ‘x - r <= x + r’ by rw [REAL_LT_IMP_LE] \\
     rw [INTERVAL_LOWERBOUND, INTERVAL_UPPERBOUND])
 >> rpt STRIP_TAC
 (* stage work *)
 >> rename1 ‘tdiv (a,b) (D,t)’
 >> Q.ABBREV_TAC ‘p = {(x,k) | ?n. n < dsize D /\ x = t n /\ k = interval[D n,D (SUC n)]}’
 >> Know ‘FINITE p’
 >- (Know ‘p = IMAGE (\n. (t n,interval[D n,D (SUC n)])) (count (dsize D))’
     >- (rw [Abbr ‘p’, Once EXTENSION, IN_IMAGE] >> Cases_on ‘x’ \\
         EQ_TAC >> rw [] \\ (* 2 subgoals, same tactics *)
         Q.EXISTS_TAC ‘n’ >> rw []) >> Rewr' \\
     MATCH_MP_TAC IMAGE_FINITE >> rw [FINITE_COUNT])
 >> DISCH_TAC
 >> Know ‘p tagged_division_of interval [a,b]’
 >- (rw [tagged_division_of, tagged_partial_division_of] >| (* 6 subgoals *)
     [ (* goal 1 (of 6): x IN s *)
       rename1 ‘(x,s) IN p’ >> POP_ASSUM MP_TAC \\
       rw [Abbr ‘p’] >> simp [IN_INTERVAL] \\
       Q.PAT_X_ASSUM ‘tdiv (a,b) (D,t)’ MP_TAC >> simp [tdiv],
       (* goal 2 (of 6): s SUBSET interval [a,b] *)
       rename1 ‘(x,s) IN p’ >> POP_ASSUM MP_TAC \\
       rw [Abbr ‘p’] >> simp [SUBSET_INTERVAL] >> DISCH_TAC \\
       Q.PAT_X_ASSUM ‘tdiv (a,b) (D,t)’ MP_TAC >> simp [tdiv] >> STRIP_TAC \\
       METIS_TAC [DIVISION_BOUNDS],
       (* goal 3 (of 6): ?a b. s = interval [a,b] *)
       rename1 ‘(x,s) IN p’ >> POP_ASSUM MP_TAC \\
       rw [Abbr ‘p’] >> qexistsl_tac [‘D n’, ‘D (SUC n)’] >> rw [],
       (* goal 4 (of 6): interior k1 INTER interior k2 = {} *)
       Q.PAT_X_ASSUM ‘(x1,k1) IN p’ MP_TAC \\
       Q.PAT_X_ASSUM ‘(x2,k2) IN p’ MP_TAC \\
       rw [Abbr ‘p’] >> rename1 ‘t m <> t n’ \\
       Q.PAT_X_ASSUM ‘tdiv (a,b) (D,t)’ MP_TAC >> simp [tdiv] >> STRIP_TAC \\
       Know ‘D m < D (SUC m) /\ D n < D (SUC n)’
       >- (CONJ_TAC \\ (* 2 subgoals, same tactics *)
           MATCH_MP_TAC DIVISION_LT_GEN \\
           qexistsl_tac [‘a’, ‘b’] >> rw []) >> STRIP_TAC \\
       rw [INTERIOR_CLOSED_INTERVAL, GSYM DISJOINT_DEF] \\
       rw [DISJOINT_ALT, IN_INTERVAL] \\
       CCONTR_TAC >> FULL_SIMP_TAC bool_ss [] \\
      ‘m <> n’ by (CCONTR_TAC >> fs []) \\
      ‘m < n \/ n < m’ by rw [] >| (* 2 subgoals *)
       [ (* goal 4.1 (of 2) *)
        ‘SUC m <= n’ by rw [] \\
        ‘D (SUC m) <= D n’ by METIS_TAC [DIVISION_MONO_LE] \\
         METIS_TAC [REAL_LET_TRANS, REAL_LT_ANTISYM],
         (* goal 4.2 (of 2) *)
        ‘SUC n <= m’ by rw [] \\
        ‘D (SUC n) <= D m’ by METIS_TAC [DIVISION_MONO_LE] \\
         METIS_TAC [REAL_LET_TRANS, REAL_LT_ANTISYM] ],
       (* goal 5 (of 6): interior k1 INTER interior k2 = {} *)
       Q.PAT_X_ASSUM ‘(x1,k1) IN p’ MP_TAC \\
       Q.PAT_X_ASSUM ‘(x2,k2) IN p’ MP_TAC \\
       rw [Abbr ‘p’] >> rename1 ‘m < dsize D’ \\
       Q.PAT_X_ASSUM ‘tdiv (a,b) (D,t)’ MP_TAC >> simp [tdiv] >> STRIP_TAC \\
       simp [INTERIOR_CLOSED_INTERVAL, GSYM DISJOINT_DEF] \\
       rw [DISJOINT_ALT, IN_INTERVAL] \\
       CCONTR_TAC >> FULL_SIMP_TAC bool_ss [] \\
      ‘m <> n’ by (CCONTR_TAC >> fs []) \\
      ‘m < n \/ n < m’ by rw [] >| (* 2 subgoals *)
       [ (* goal 5.1 (of 2) *)
        ‘SUC m <= n’ by rw [] \\
        ‘D (SUC m) <= D n’ by METIS_TAC [DIVISION_MONO_LE] \\
         METIS_TAC [REAL_LET_TRANS, REAL_LT_ANTISYM],
         (* goal 5.2 (of 2) *)
        ‘SUC n <= m’ by rw [] \\
        ‘D (SUC n) <= D m’ by METIS_TAC [DIVISION_MONO_LE] \\
         METIS_TAC [REAL_LET_TRANS, REAL_LT_ANTISYM] ],
       (* goal 6 (of 6): BIGUNION {k | (?x. (x,k) IN p)} = interval [a,b] *)
       Q.PAT_X_ASSUM ‘tdiv (a,b) (D,t)’ MP_TAC >> simp [tdiv] >> STRIP_TAC \\
       rw [Abbr ‘p’, Abbr ‘E’, Once EXTENSION, IN_BIGUNION, IN_INTERVAL] \\
       EQ_TAC >> simp [] (* 2 subgoals, first easier *)
       >- (STRIP_TAC \\
           POP_ASSUM (fn th => FULL_SIMP_TAC std_ss [th, IN_INTERVAL]) \\
          ‘a <= D n /\ D (SUC n) <= b’ by METIS_TAC [DIVISION_BOUNDS] \\
           METIS_TAC [REAL_LE_TRANS]) \\
       STRIP_TAC \\
       MP_TAC (Q.SPECL [‘D’, ‘a’, ‘b’, ‘x’] DIVISION_INTERMEDIATE') \\
       RW_TAC std_ss [] \\
       Q.EXISTS_TAC ‘interval [D n,D (SUC n)]’ \\
       CONJ_TAC >- rw [IN_INTERVAL] \\
       Q.EXISTS_TAC ‘n’ >> rw [] ])
 >> DISCH_TAC
 >> Know ‘d FINE p’
 >- (rw [FINE] >> rename1 ‘(x,s) IN p’ \\
     Q.PAT_X_ASSUM ‘p tagged_division_of interval [a,b]’ K_TAC \\
     POP_ASSUM MP_TAC >> rw [Abbr ‘p’] \\
     FULL_SIMP_TAC std_ss [fine, tdiv, gauge_def] \\
     Q.PAT_X_ASSUM ‘!n. D n <= t n /\ t n <= D (SUC n)’ (STRIP_ASSUME_TAC o (Q.SPEC ‘n’)) \\
     Q.PAT_X_ASSUM ‘gauge E g’ K_TAC \\
     Q.PAT_X_ASSUM ‘!n. n < dsize D ==> P’ drule >> rw [Abbr ‘g’] \\
     Q.ABBREV_TAC ‘x = t n’ \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘cb x’ \\
     reverse CONJ_TAC >- rw [Abbr ‘cb’] \\
     Q.ABBREV_TAC ‘r = h(x,d x)’ \\
    ‘0 < r’ by rw [Abbr ‘r’] \\
     Know ‘x - r < x + r’
     >- (MATCH_MP_TAC REAL_LT_TRANS \\
         Q.EXISTS_TAC ‘x’ >> rw [REAL_LT_SUB_RADD]) >> DISCH_TAC \\
    ‘x - r <= x + r’ by rw [REAL_LT_IMP_LE] \\
     fs [Abbr ‘cb’, CBALL_INTERVAL, INTERVAL_UPPERBOUND, INTERVAL_LOWERBOUND] \\
    ‘D n <= D (SUC n)’ by PROVE_TAC [REAL_LE_TRANS] \\
     simp [SUBSET_INTERVAL] \\
     fs [REAL_ARITH “x + r - (x - r) = 2 * r”] \\
    ‘D (SUC n) - D n <= r’ by rw [REAL_LT_IMP_LE] \\
     reverse CONJ_TAC
     >- (‘D (SUC n) = D n + (D (SUC n) - D n)’ by REAL_ARITH_TAC >> POP_ORW \\
         MATCH_MP_TAC REAL_LE_ADD2 >> art []) \\
     rw [REAL_LE_SUB_RADD] \\
     MATCH_MP_TAC REAL_LE_TRANS \\
     Q.EXISTS_TAC ‘D (SUC n)’ >> rw [Once REAL_ADD_COMM] \\
     fs [REAL_LE_SUB_RADD])
 >> DISCH_TAC
 (* stage work *)
 >> Q.PAT_X_ASSUM ‘!p. p tagged_division_of interval [a,b] /\ d FINE p ==> P’ drule_all
 >> simp [rsum, GSYM REAL_SUM_IMAGE_COUNT, GSYM REAL_SUM_IMAGE_sum]
 >> Q.ABBREV_TAC ‘N = dsize D’
 >> Suff ‘SIGMA (\n. f (t n) * (D (SUC n) - D n)) (count N) =
          SIGMA (\(x,k). f x * content k) p’ >- Rewr
 >> Know ‘p = IMAGE (\n. (t n,interval[D n,D (SUC n)])) (count N)’
 >- (rw [Abbr ‘p’, Once EXTENSION, IN_IMAGE] >> Cases_on ‘x’ \\
     EQ_TAC >> rw [] \\ (* 2 subgoals, same tactics *)
     Q.EXISTS_TAC ‘n’ >> rw []) >> Rewr'
 >> Q.ABBREV_TAC ‘H = \n. (t n,interval [D n,D (SUC n)])’
 >> Know ‘SIGMA (\(x,k). f x * content k) (IMAGE H (count N)) =
          SIGMA ((\(x,k). f x * content k) o H) (count N)’
 >- (irule REAL_SUM_IMAGE_IMAGE >> simp [INJ_DEF] \\
     qx_genl_tac [‘i’, ‘j’] >> rpt STRIP_TAC \\
     fs [Abbr ‘H’, EQ_INTERVAL, GSYM INTERVAL_EQ_EMPTY, tdiv]
     >- (Suff ‘D i < D (SUC i)’ >- PROVE_TAC [REAL_LT_ANTISYM] \\
         MATCH_MP_TAC DIVISION_LT_GEN \\
         qexistsl_tac [‘a’, ‘b’] >> rw []) \\
     CCONTR_TAC >> ‘i < j \/ j < i’ by rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Suff ‘D (SUC i) < D (SUC j)’ >- PROVE_TAC [REAL_LT_IMP_NE] \\
       MATCH_MP_TAC DIVISION_LT_GEN \\
       qexistsl_tac [‘a’, ‘b’] >> rw [],
       (* goal 2 (of 2) *)
       Suff ‘D (SUC j) < D (SUC i)’ >- PROVE_TAC [REAL_LT_IMP_NE] \\
       MATCH_MP_TAC DIVISION_LT_GEN \\
       qexistsl_tac [‘a’, ‘b’] >> rw [] ])
 >> Rewr'
 >> MATCH_MP_TAC REAL_SUM_IMAGE_EQ >> rw [Abbr ‘H’]
 >> DISJ2_TAC >> rename1 ‘n < N’
 >> Suff ‘D n <= D (SUC n)’ >- rw [CONTENT_CLOSED_INTERVAL]
 >> MATCH_MP_TAC DIVISION_MONO_LE_SUC
 >> qexistsl_tac [‘a’, ‘b’] >> fs [tdiv]
QED

Theorem Dint_has_integral :
    !f a b k. a <= b ==> (Dint(a,b) f k <=> (f has_integral k) (interval[a,b]))
Proof
    rpt STRIP_TAC
 (* special case: a = b *)
 >> ‘b = a \/ a < b’ by PROVE_TAC [REAL_LE_LT]
 >- (POP_ASSUM (fs o wrap) >> KILL_TAC \\
     Cases_on ‘k = 0’ >- (rw [INTEGRAL_NULL, HAS_INTEGRAL_REFL]) \\
     Know ‘Dint (a,a) f k <=> F’
     >- (rw [] >> CCONTR_TAC >> fs [] \\
         ASSUME_TAC (Q.SPECL [‘f’, ‘a’] INTEGRAL_NULL) \\
         METIS_TAC [DINT_UNIQ, REAL_LE_REFL]) >> Rewr' \\
     Know ‘(f has_integral k) (interval [a,a]) <=> F’
     >- (rw [] >> CCONTR_TAC >> fs [] \\
         ASSUME_TAC (Q.SPECL [‘f’, ‘a’] HAS_INTEGRAL_REFL) \\
         METIS_TAC [HAS_INTEGRAL_UNIQUE]) >> Rewr)
 (* now ‘a < b’ *)
 >> METIS_TAC [Dint_imp_has_integral, has_integral_imp_Dint]
QED

(* Below are easy corollaries of Dint_has_integral *)
Theorem integrable_eq_integrable_on :
    !f a b. a <= b ==> (integrable(a,b) f <=> f integrable_on (interval[a,b]))
Proof
    rw [integrable, integrable_on, Dint_has_integral]
QED

Theorem integral_old_to_new :
    !f a b. a <= b /\ integrable(a,b) f ==>
            integral(a,b) f = integration$integral (interval[a,b]) f
Proof
    rpt STRIP_TAC
 >> ‘f integrable_on (interval[a,b])’ by PROVE_TAC [integrable_eq_integrable_on]
 >> rw [integral, integral_def]
 >> SELECT_ELIM_TAC
 >> STRONG_CONJ_TAC
 >- (fs [integrable] >> Q.EXISTS_TAC ‘i’ >> art [])
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘k’ ASSUME_TAC)
 >> rpt STRIP_TAC
 >> ‘x = k’ by METIS_TAC [DINT_UNIQ]
 >> POP_ASSUM (fs o wrap)
 >> SELECT_ELIM_TAC
 >> CONJ_TAC
 >- (fs [integrable_on] >> Q.EXISTS_TAC ‘y’ >> art [])
 >> rpt STRIP_TAC
 >> MATCH_MP_TAC HAS_INTEGRAL_UNIQUE
 >> qexistsl_tac [‘f’, ‘interval[a,b]’] >> art []
 >> rw [GSYM Dint_has_integral]
QED

Theorem integral_new_to_old :
    !f a b. a <= b /\ f integrable_on (interval[a,b]) ==>
            integration$integral (interval[a,b]) f = integral(a,b) f
Proof
    rpt STRIP_TAC
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> MATCH_MP_TAC integral_old_to_new >> art []
 >> rw [integrable_eq_integrable_on]
QED

val _ = export_theory();

(* References:

 [1] Bartle, R.G.: A Modern Theory of Integration. American Mathematical Soc. (2001).
 [2] Shi, Z., Gu, W., Li, X., Guan, Y., Ye, S., Zhang, J., Wei, H.:
     The Gauge Integral Theory in HOL4. J. Appl. Math. 2013, (2013).
 *)
