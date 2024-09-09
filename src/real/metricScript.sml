(*===========================================================================*)
(* Metric spaces, including metric on real line                              *)
(* ========================================================================= *)
(* Formalization of general topological and metric spaces in HOL Light       *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2017                       *)
(*                (c) Copyright, Marco Maggesi 2014-2017                     *)
(*             (c) Copyright, Andrea Gabrielli  2016-2017                    *)
(* ========================================================================= *)

open HolKernel Parse bossLib boolLib;

open arithmeticTheory numTheory boolSimps simpLib mesonLib metisLib jrhUtils
     pairTheory pairLib quotientTheory pred_setTheory pred_setLib RealArith;

open realTheory cardinalTheory topologyTheory hurdUtils;

val _ = new_theory "metric";

fun METIS ths tm = prove(tm,METIS_TAC ths);

(* ------------------------------------------------------------------------- *)
(* Handy lemmas switching between versions of limit arguments.               *)
(* (originally from hol-light's misc.ml, line 747-772)                       *)
(* ------------------------------------------------------------------------- *)

Theorem FORALL_POS_MONO :
   !P. (!d e:real. d < e /\ P d ==> P e) /\ (!n. ~(n = 0) ==> P(inv(&n)))
       ==> !e. &0 < e ==> P e
Proof
  MESON_TAC[REAL_ARCH_INV, REAL_LT_TRANS]
QED

Theorem FORALL_SUC :
   (!n. n <> 0 ==> P n) <=> !n. P (SUC n)
Proof
   MESON_TAC[num_CASES, NOT_SUC]
QED

Theorem FORALL_POS_MONO_1 :
   !P. (!d e. d < e /\ P d ==> P e) /\ (!n. P(inv(&n + &1)))
       ==> !e. &0 < e ==> P e
Proof
    GEN_TAC >> REWRITE_TAC [REAL_OF_NUM_SUC]
 >> STRIP_TAC
 >> MATCH_MP_TAC FORALL_POS_MONO
 >> ASM_REWRITE_TAC []
 >> ASM_SIMP_TAC std_ss [FORALL_SUC]
QED

Theorem FORALL_POS_MONO_EQ :
   !P. (!d e. d < e /\ P d ==> P e)
       ==> ((!e. &0 < e ==> P e) <=> (!n. ~(n = 0) ==> P(inv(&n))))
Proof
  MESON_TAC[REAL_ARCH_INV, REAL_LT_INV_EQ, REAL_LT_TRANS, LE_1,
            REAL_OF_NUM_LT]
QED

Theorem FORALL_POS_MONO_1_EQ :
   !P. (!d e. d < e /\ P d ==> P e)
       ==> ((!e. &0 < e ==> P e) <=> (!n. P(inv(&n + &1))))
Proof
  GEN_TAC THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP FORALL_POS_MONO_EQ) THEN
  SIMP_TAC std_ss [REAL_OF_NUM_SUC, GSYM FORALL_SUC]
QED

(*---------------------------------------------------------------------------*)
(* Characterize an (alpha)metric                                             *)
(*---------------------------------------------------------------------------*)

Definition ismet :
   ismet (m :'a # 'a -> real) =
     ((!x y. (m(x,y) = &0) <=> (x = y)) /\
      (!x y z. m(y,z) <= m(x,y) + m(x,z)))
End

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
  ONCE_REWRITE_TAC[TAUT_CONV “~a ==> b <=> b \/ a”] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN
  REWRITE_TAC[GSYM REAL_LE_LT, METRIC_POS]);

(*---------------------------------------------------------------------------*)
(* Get a bounded metric (<1) from any metric                                 *)
(*---------------------------------------------------------------------------*)

val bmetric_tm = “(dist m)(x,y) / (1 + (dist m)(x,y))”;

Definition bounded_metric_def :
    bounded_metric (m :'a metric) = metric (\(x,y). ^bmetric_tm)
End

Theorem bounded_metric_alt[local] :
    !m x y. ^bmetric_tm = 1 - inv (1 + dist m (x,y))
Proof
    rw [FUN_EQ_THM]
 >> Q.ABBREV_TAC ‘z = 1 + dist m (x,y)’
 >> Know ‘0 < z’
 >- (MATCH_MP_TAC REAL_LTE_TRANS \\
     Q.EXISTS_TAC ‘1’ >> rw [Abbr ‘z’, METRIC_POS])
 >> DISCH_TAC
 >> ‘z <> 0’ by PROVE_TAC [REAL_LT_IMP_NE]
 >> Know ‘dist m (x,y) = z - 1’
 >- (Q.UNABBREV_TAC ‘z’ >> REAL_ARITH_TAC)
 >> Rewr'
 >> rw [real_div, REAL_SUB_RDISTRIB, REAL_MUL_RINV]
QED

Theorem bounded_metric_ismet :
    !m. ismet (\(x,y). ^bmetric_tm)
Proof
    rw [ismet]
 >- (fs [REAL_DIV_ZERO] \\
     EQ_TAC >> rw [METRIC_ZERO] \\
     Suff ‘0 < 1 + dist m (x,y)’ >- PROVE_TAC [REAL_LT_IMP_NE] \\
     MATCH_MP_TAC REAL_LTE_TRANS \\
     Q.EXISTS_TAC ‘1’ >> rw [METRIC_POS])
 >> Know ‘!a b. 0 < 1 + dist m (a,b)’
 >- (rpt GEN_TAC \\
     MATCH_MP_TAC REAL_LTE_TRANS \\
     Q.EXISTS_TAC ‘1’ >> rw [METRIC_POS])
 >> DISCH_TAC
 >> REWRITE_TAC [bounded_metric_alt]
 >> ‘1 - inv (1 + dist m (x,y)) + (1 - inv (1 + dist m (x,z))) =
     1 - (inv (1 + dist m (x,y)) + inv (1 + dist m (x,z)) - 1)’ by REAL_ARITH_TAC
 >> POP_ORW
 >> RW_TAC std_ss [REAL_LE_SUB_CANCEL1, REAL_LE_SUB_RADD]
 (* applying METRIC_TRIANGLE *)
 >> MATCH_MP_TAC REAL_LE_TRANS
 >> Q.EXISTS_TAC ‘inv (1 + dist m (x,y) + dist m (x,z)) + 1’
 >> reverse CONJ_TAC
 >- (REWRITE_TAC [REAL_LE_RADD] \\
     MATCH_MP_TAC REAL_LE_INV2 \\
     rw [REAL_LE_LADD, GSYM REAL_ADD_ASSOC] \\
     METIS_TAC [METRIC_SYM, METRIC_TRIANGLE])
 >> Q.ABBREV_TAC ‘a = dist m (x,y)’
 >> Q.ABBREV_TAC ‘b = dist m (x,z)’
 >> ‘1 + a <> 0 /\ 1 + b <> 0’ by METIS_TAC [REAL_LT_IMP_NE]
 (* LHS simplification *)
 >> Know ‘inv (1 + a) = (1 + b) * inv ((1 + a) * (1 + b))’
 >- (rw [REAL_INV_MUL, REAL_MUL_ASSOC] \\
    ‘(1 + b) * inv (1 + a) * inv (1 + b) =
     (1 + b) * inv (1 + b) * inv (1 + a)’ by REAL_ARITH_TAC >> POP_ORW \\
     rw [REAL_MUL_RINV]) >> Rewr'
 >> Know ‘inv (1 + b) = (1 + a) * inv ((1 + a) * (1 + b))’
 >- (rw [REAL_INV_MUL, REAL_MUL_ASSOC, REAL_MUL_RINV])
 >> Rewr'
 >> rw [GSYM REAL_ADD_RDISTRIB, REAL_ARITH “1 + b + (1 + a) = 2 + a + (b :real)”]
 >> Know ‘0 < 1 + a + b’
 >- (MATCH_MP_TAC REAL_LTE_TRANS \\
     Q.EXISTS_TAC ‘1’ >> rw [Abbr ‘a’, Abbr ‘b’, GSYM REAL_ADD_ASSOC] \\
     MATCH_MP_TAC REAL_LE_ADD >> rw [METRIC_POS])
 >> DISCH_TAC
 >> Know ‘inv (1 + a + b) + 1 = (1 + (1 + a + b)) * inv (1 + a + b)’
 >- (REWRITE_TAC [Once REAL_ADD_RDISTRIB, REAL_MUL_LID] \\
    ‘1 + a + b <> 0’ by PROVE_TAC [REAL_LT_IMP_NE] \\
     rw [REAL_MUL_RINV])
 >> Rewr'
 >> REWRITE_TAC [REAL_ARITH “1 + (1 + a + b) = 2 + a + (b :real)”]
 >> Know ‘0 < 2 + a + b’
 >- (MATCH_MP_TAC REAL_LTE_TRANS \\
     Q.EXISTS_TAC ‘2’ >> rw [Abbr ‘a’, Abbr ‘b’, GSYM REAL_ADD_ASSOC] \\
     MATCH_MP_TAC REAL_LE_ADD >> rw [METRIC_POS])
 >> DISCH_TAC
 >> ASM_SIMP_TAC std_ss [REAL_LE_LMUL]
 >> MATCH_MP_TAC REAL_LE_INV2
 >> rw [REAL_ADD_LDISTRIB, REAL_ADD_RDISTRIB, REAL_ADD_ASSOC]
 >> REWRITE_TAC [REAL_ARITH “1 + b + a + a * b = 1 + a + b + a * (b :real)”]
 >> rw [REAL_LE_ADDR, Abbr ‘a’, Abbr ‘b’]
 >> MATCH_MP_TAC REAL_LE_MUL >> rw [METRIC_POS]
QED

Theorem bounded_metric_thm :
    !m x y. dist (bounded_metric m) (x,y) = ^bmetric_tm
Proof
    rw [bounded_metric_def]
 >> ‘dist (metric (\(x,y). ^bmetric_tm)) = (\(x,y). ^bmetric_tm)’
       by (rw [GSYM metric_tybij, bounded_metric_ismet])
 >> rw []
QED

Theorem bounded_metric_lt_1 :
    !(m :'a metric) x y. dist (bounded_metric m) (x,y) < 1
Proof
    rw [bounded_metric_thm]
 >> Know ‘0 < 1 + dist m (q,r)’
 >- (MATCH_MP_TAC REAL_LTE_TRANS \\
     Q.EXISTS_TAC ‘1’ >> rw [METRIC_POS])
 >> DISCH_TAC
 >> ‘1 + dist m (q,r) <> 0’ by rw [REAL_LT_IMP_NE]
 >> MATCH_MP_TAC REAL_LT_1
 >> rw [METRIC_POS]
QED

(*---------------------------------------------------------------------------*)
(* Now define metric topology and prove equivalent definition of "open"      *)
(*---------------------------------------------------------------------------*)

Definition mtop :
    mtop (m :'a metric) =
    topology (\S'. !x. S' x ==> ?e. &0 < e /\ !y. (dist m)(x,y) < e ==> S' y)
End

(* for HOL Light compatibility *)
Overload mtopology[inferior] = “mtop”
Overload mdist[inferior] = “dist”

(* NOTE: HOL4's ‘mspace’ definition is different with HOL-Light *)
Definition mspace :
    mspace m = topspace (mtop m)
End

(* |- !m. topspace (mtop m) = mspace m *)
Theorem TOPSPACE_MTOPOLOGY = GEN_ALL (GSYM mspace)

Theorem mtop_istopology :
    !m:('a)metric.
      istopology (\S'. !x. S' x ==>
                           ?e. &0 < e /\
                               (!y. (dist m)(x,y) < e ==> S' y))
Proof
  GEN_TAC THEN
  SIMP_TAC bool_ss [istopology, EMPTY_DEF, UNIV_DEF, BIGUNION_applied,
                    INTER_applied, SUBSET_applied, IN_DEF] THEN
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
      >> PROVE_TAC [] ] ]
QED

val MTOP_OPEN = store_thm("MTOP_OPEN",
  “!S' (m:('a)metric). open_in(mtop m) S' =
      (!x. S' x ==> ?e. &0 < e /\ (!y. (dist m(x,y)) < e ==> S' y))”,
  GEN_TAC THEN REWRITE_TAC[mtop] THEN
  REWRITE_TAC[REWRITE_RULE[topology_tybij] mtop_istopology] THEN
  BETA_TAC THEN REWRITE_TAC[]);

(*---------------------------------------------------------------------------*)
(* Define open ball in metric space + prove basic properties                 *)
(*---------------------------------------------------------------------------*)

Definition ball :
    B(m)(x,e) = \y. (dist m)(x,y) < e
End

(* for HOL Light compatibility *)
Overload mball[inferior] = “B”;

Theorem BALL_OPEN:
  !m:('a)metric. !x e. &0 < e ==> open_in(mtop(m))(B(m)(x,e))
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[MTOP_OPEN] THEN
  X_GEN_TAC “z:'a” THEN REWRITE_TAC[ball] THEN BETA_TAC THEN
  DISCH_THEN(ASSUME_TAC o ONCE_REWRITE_RULE[GSYM REAL_SUB_LT]) THEN
  EXISTS_TAC “e - dist(m:('a)metric)(x,z)” THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC “y:'a” THEN REWRITE_TAC[REAL_LT_SUB_LADD] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC “dist(m)(x:'a,z) + dist(m)(z,y)” THEN
  ASM_REWRITE_TAC[METRIC_TRIANGLE]
QED

(* This is not good ... *)
Theorem TOPSPACE_MTOP[simp]:
  topspace (mtop m) = UNIV
Proof
  simp[topspace, EXTENSION] >> csimp[IN_DEF] >> qx_gen_tac ‘x’ >>
  qexists_tac ‘B(m)(x,1)’ >> simp[BALL_OPEN] >>
  simp[ball, METRIC_SAME]
QED

val BALL_NEIGH = store_thm("BALL_NEIGH",
  “!m:('a)metric. !x e. &0 < e ==> neigh(mtop(m))(B(m)(x,e),x)”,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[neigh] THEN EXISTS_TAC “B(m)(x:'a,e)” THEN
  REWRITE_TAC[SUBSET_REFL, TOPSPACE_MTOP, SUBSET_UNIV] THEN CONJ_TAC THENL
   [MATCH_MP_TAC BALL_OPEN,
    REWRITE_TAC[ball] THEN BETA_TAC THEN REWRITE_TAC[METRIC_SAME]] THEN
  POP_ASSUM ACCEPT_TAC);

(*---------------------------------------------------------------------------*)
(* HOL-Light compatibile theorems                                            *)
(*---------------------------------------------------------------------------*)

Theorem MDIST_REFL :
   !m x:'a. x IN mspace m ==> mdist m (x,x) = &0
Proof
   rw [mspace, METRIC_SAME]
QED

Theorem mtopology :
   !m. mtopology (m:'a metric) =
       topology {u | u SUBSET mspace m /\
                     !x:'a. x IN u ==> ?r. &0 < r /\ mball m (x,r) SUBSET u}
Proof
    rw [mtop, mspace, ball]
 >> AP_TERM_TAC
 >> rw [Once EXTENSION, IN_APP, SUBSET_DEF]
QED

Theorem mball :
   !m x r. mball m (x:'a,r) =
          {y | x IN mspace m /\ y IN mspace m /\ mdist m (x,y) < r}
Proof
   rw [mspace, ball, Once EXTENSION]
QED

Theorem IS_TOPOLOGY_METRIC_TOPOLOGY :
    !m. istopology {u | u SUBSET mspace m /\
                        !x:'a. x IN u ==> ?r. &0 < r /\ mball m (x,r) SUBSET u}
Proof
    GEN_TAC
 >> Q_TAC SUFF_TAC
     ‘{u | u SUBSET mspace m /\
           !x:'a. x IN u ==> ?r. &0 < r /\ mball m (x,r) SUBSET u} =
     (\S'. !x. S' x ==> ?e. 0 < e /\ !y. dist m (x,y) < e ==> S' y)’
 >- (DISCH_THEN (ONCE_REWRITE_TAC o wrap) \\
     REWRITE_TAC [mtop_istopology])
 >> rw [mspace, ball, SUBSET_DEF, IN_APP, Once EXTENSION]
QED

Theorem OPEN_IN_MTOPOLOGY :
   !(m:'a metric) u.
     open_in (mtopology m) u <=>
     u SUBSET mspace m /\
     (!x. x IN u ==> ?r. &0 < r /\ mball m (x,r) SUBSET u)
Proof
    rw [MTOP_OPEN, mspace, ball, SUBSET_DEF, IN_APP]
QED

Theorem IN_MBALL :
   !m x y:'a r.
     y IN mball m (x,r) <=>
     x IN mspace m /\ y IN mspace m /\ mdist m (x,y) < r
Proof
    rw [mball]
QED

(*---------------------------------------------------------------------------*)
(* Characterize limit point in a metric topology                             *)
(*---------------------------------------------------------------------------*)

Theorem MTOP_LIMPT:
  !m:('a)metric x S'.
    limpt(mtop m) x S' <=>
    !e. &0 < e ==> ?y. ~(x = y) /\ S' y /\ (dist m)(x,y) < e
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[limpt] THEN EQ_TAC THENL
   [STRIP_TAC THEN
    Q.X_GEN_TAC ‘e’ THEN STRIP_TAC THEN
    FIRST_X_ASSUM (Q.SPEC_THEN ‘B(m)(x,e)’ MP_TAC) THEN
    FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP BALL_NEIGH th]) THEN
    REWRITE_TAC[ball] THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC,
    STRIP_TAC THEN CONJ_TAC THEN1 ASM_REWRITE_TAC[TOPSPACE_MTOP,IN_UNIV] THEN
    GEN_TAC THEN REWRITE_TAC[neigh] THEN
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
    FIRST_ASSUM ACCEPT_TAC
   ]
QED

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

Definition mr1 :
    mr1 = metric(\(x,y). abs(y - x))
End

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

Theorem MR1_LIMPT:
  !x. limpt(mtop mr1) x univ(:real)
Proof
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
  ASM_REWRITE_TAC[REAL_LT_HALF1]
QED

(* ------------------------------------------------------------------------- *)
(* Metric function for R^1.                                                  *)
(* ------------------------------------------------------------------------- *)

(* new definition based on metricTheory *)
Definition dist_def :
    real_dist = dist mr1
End

(* old definition (now becomes a theorem) *)
Theorem dist :
    !x y. real_dist(x:real,y:real) = abs(x - y)
Proof
    RW_TAC std_ss [dist_def, MR1_DEF]
 >> REAL_ARITH_TAC
QED

Overload dist = “real_dist”;

val DIST_REFL = store_thm ("DIST_REFL",
 ``!x. dist(x,x) = &0``,
  SIMP_TAC std_ss [dist] THEN REAL_ARITH_TAC);

val DIST_SYM = store_thm ("DIST_SYM",
 ``!x y. dist(x,y) = dist(y,x)``,
  SIMP_TAC std_ss [dist] THEN REAL_ARITH_TAC);

val DIST_TRIANGLE = store_thm ("DIST_TRIANGLE",
 ``!x:real y z. dist(x,z) <= dist(x,y) + dist(y,z)``,
  SIMP_TAC std_ss [dist] THEN REAL_ARITH_TAC);

val DIST_TRIANGLE_ALT = store_thm ("DIST_TRIANGLE_ALT",
 ``!x y z. dist(y,z) <= dist(x,y) + dist(x,z)``,
  SIMP_TAC std_ss [dist] THEN REAL_ARITH_TAC);

val DIST_EQ_0 = store_thm ("DIST_EQ_0",
 ``!x y. (dist(x,y) = 0:real) <=> (x = y)``,
  SIMP_TAC std_ss [dist] THEN REAL_ARITH_TAC);

val DIST_POS_LT = store_thm ("DIST_POS_LT",
 ``!x y. ~(x = y) ==> &0 < dist(x,y)``,
  SIMP_TAC std_ss [dist] THEN REAL_ARITH_TAC);

val DIST_NZ = store_thm ("DIST_NZ",
 ``!x y. ~(x = y) <=> &0 < dist(x,y)``,
  SIMP_TAC std_ss [dist] THEN REAL_ARITH_TAC);

val DIST_TRIANGLE_LE = store_thm ("DIST_TRIANGLE_LE",
 ``!x y z e. dist(x,z) + dist(y,z) <= e ==> dist(x,y) <= e``,
  SIMP_TAC std_ss [dist] THEN REAL_ARITH_TAC);

val DIST_TRIANGLE_LT = store_thm ("DIST_TRIANGLE_LT",
 ``!x y z e. dist(x,z) + dist(y,z) < e ==> dist(x,y) < e``,
  SIMP_TAC std_ss [dist] THEN REAL_ARITH_TAC);

val DIST_TRIANGLE_HALF_L = store_thm ("DIST_TRIANGLE_HALF_L",
 ``!x1 x2 y. dist(x1,y) < e / &2 /\ dist(x2,y) < e / &2 ==> dist(x1,x2) < e``,
  REPEAT STRIP_TAC THEN KNOW_TAC `` dist (x1,y) + dist (x2,y) < e`` THENL
  [METIS_TAC [REAL_LT_ADD2, REAL_HALF_DOUBLE],
   DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC ``dist (x1,y) + dist (x2,y)`` THEN
   METIS_TAC [DIST_TRIANGLE, DIST_SYM]]);

val DIST_TRIANGLE_HALF_R = store_thm ("DIST_TRIANGLE_HALF_R",
 ``!x1 x2 y. dist(y,x1) < e / &2 /\ dist(y,x2) < e / &2 ==> dist(x1,x2) < e``,
  REPEAT STRIP_TAC THEN KNOW_TAC `` dist (y, x1) + dist (y, x2) < e`` THENL
  [METIS_TAC [REAL_LT_ADD2, REAL_HALF_DOUBLE],
   DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC ``dist (y, x1) + dist (y, x2)`` THEN
   METIS_TAC [DIST_TRIANGLE, DIST_SYM]]);

val DIST_TRIANGLE_ADD = store_thm ("DIST_TRIANGLE_ADD",
 ``!x x' y y'. dist(x + y,x' + y') <= dist(x,x') + dist(y,y')``,
  SIMP_TAC std_ss [dist] THEN REAL_ARITH_TAC);

val DIST_MUL = store_thm ("DIST_MUL",
 ``!x y c. dist(c * x,c * y) = abs(c) * dist(x,y)``,
  REWRITE_TAC[dist, GSYM ABS_MUL] THEN REAL_ARITH_TAC);

val DIST_TRIANGLE_ADD_HALF = store_thm ("DIST_TRIANGLE_ADD_HALF",
 ``!x x' y y':real.
    dist(x,x') < e / &2 /\ dist(y,y') < e / &2 ==> dist(x + y,x' + y') < e``,
  REPEAT STRIP_TAC THEN KNOW_TAC `` dist (x, x') + dist (y, y') < e`` THENL
  [METIS_TAC [REAL_LT_ADD2, REAL_HALF_DOUBLE],
   DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC ``dist (x, x') + dist (y, y')`` THEN
   METIS_TAC [DIST_TRIANGLE_ADD, DIST_SYM]]);

val DIST_LE_0 = store_thm ("DIST_LE_0",
 ``!x y. dist(x,y) <= &0 <=> (x = y)``,
  SIMP_TAC std_ss [dist] THEN REAL_ARITH_TAC);

val DIST_POS_LE = store_thm ("DIST_POS_LE",
 ``!x y. &0 <= dist(x,y)``,
  METIS_TAC [DIST_EQ_0, DIST_NZ, REAL_LE_LT]);

val DIST_EQ = store_thm ("DIST_EQ",
 ``!w x y z. (dist(w,x) = dist(y,z)) <=> (dist(w,x) pow 2 = dist(y,z) pow 2)``,
  REPEAT GEN_TAC THEN EQ_TAC THENL [RW_TAC std_ss [],
  DISCH_TAC THEN MATCH_MP_TAC POW_EQ THEN EXISTS_TAC ``1:num`` THEN
  RW_TAC arith_ss [DIST_POS_LE]]);

val DIST_0 = store_thm ("DIST_0",
 ``!x. (dist(x,0) = abs(x)) /\ (dist(0,x) = abs(x))``,
  RW_TAC arith_ss [dist, REAL_SUB_RZERO, REAL_SUB_LZERO, ABS_NEG]);

val REAL_CHOOSE_DIST = store_thm ("REAL_CHOOSE_DIST",
 ``!x e. &0 <= e ==> (?y. dist (x,y) = e)``,
  REPEAT STRIP_TAC THEN EXISTS_TAC ``x - e:real`` THEN
  ASM_REWRITE_TAC [dist, REAL_SUB_SUB2, ABS_REFL]);

(* ------------------------------------------------------------------------- *)
(* F_sigma and G_delta sets in a topological space (ported from HOL Light)   *)
(* ------------------------------------------------------------------------- *)

(* The countable intersection class (general version)

   The leading letter G is from the German word "Gebiet" meaning "region".
   The greek letter "delta" stands for a countable intersection (in German,
   "Durchschnitt"). See [1, p.310] (bibitem is at the bottom of this file.)

   NOTE: the part ‘relative_to topspace top’ is necessary when ‘topspace top’
   is not UNIV, because "a countable intersection of something" includes "a
   countable intersection of nothing", and ‘BIGINTER {} = UNIV’, which may
   go beyond the scope of ‘topspace top’. -- Chun Tian, 28 nov 2021
 *)
Definition gdelta_in :
    gdelta_in (top:'a topology) =
        (COUNTABLE INTERSECTION_OF open_in top) relative_to topspace top
End

(* The countable union class (general version)

   The leading letter F is from the French word "ferme" meaning "closed".
   The greek letter "sigma" stands for a countable union or sum (in German,
   "Summe").
 *)
Definition fsigma_in :
    fsigma_in (top:'a topology) = COUNTABLE UNION_OF closed_in top
End

Theorem FSIGMA_IN_ASCENDING :
   !top s:'a->bool.
        fsigma_in top s <=>
        ?c. (!n. closed_in top (c n)) /\
            (!n. c n SUBSET c(n + 1)) /\
            UNIONS {c n | n IN univ(:num)} = s
Proof
  REWRITE_TAC[fsigma_in] THEN
  SIMP_TAC std_ss [COUNTABLE_UNION_OF_ASCENDING, CLOSED_IN_EMPTY, CLOSED_IN_UNION] THEN
  REWRITE_TAC[ADD1]
QED

Theorem GDELTA_IN_ALT :
   !top s:'a->bool.
        gdelta_in top s <=>
        s SUBSET topspace top /\ (COUNTABLE INTERSECTION_OF open_in top) s
Proof
  SIMP_TAC std_ss [COUNTABLE_INTERSECTION_OF_RELATIVE_TO_ALT, gdelta_in,
                   OPEN_IN_TOPSPACE] THEN
  REWRITE_TAC[Once CONJ_ACI]
QED

Theorem FSIGMA_IN_SUBSET :
   !top s:'a->bool. fsigma_in top s ==> s SUBSET topspace top
Proof
  GEN_TAC THEN SIMP_TAC std_ss [fsigma_in, FORALL_UNION_OF, UNIONS_SUBSET] THEN
  SIMP_TAC std_ss [CLOSED_IN_SUBSET]
QED

Theorem GDELTA_IN_SUBSET :
   !top s:'a->bool. gdelta_in top s ==> s SUBSET topspace top
Proof
  SIMP_TAC std_ss [GDELTA_IN_ALT]
QED

Theorem CLOSED_IMP_FSIGMA_IN :
   !top s:'a->bool. closed_in top s ==> fsigma_in top s
Proof
  SIMP_TAC std_ss [fsigma_in, COUNTABLE_UNION_OF_INC]
QED

Theorem OPEN_IMP_GDELTA_IN :
   !top s:'a->bool. open_in top s ==> gdelta_in top s
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[gdelta_in] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (SET_RULE ``s SUBSET u ==> s = u INTER s``) o
    MATCH_MP OPEN_IN_SUBSET) THEN
  MATCH_MP_TAC RELATIVE_TO_INC THEN
  ASM_SIMP_TAC std_ss [COUNTABLE_INTERSECTION_OF_INC]
QED

Theorem FSIGMA_IN_EMPTY :
   !top:'a topology. fsigma_in top {}
Proof
  SIMP_TAC std_ss [CLOSED_IMP_FSIGMA_IN, CLOSED_IN_EMPTY]
QED

Theorem GDELTA_IN_EMPTY :
   !top:'a topology. gdelta_in top {}
Proof
  SIMP_TAC std_ss [OPEN_IMP_GDELTA_IN, OPEN_IN_EMPTY]
QED

Theorem FSIGMA_IN_TOPSPACE :
   !top:'a topology. fsigma_in top (topspace top)
Proof
  SIMP_TAC std_ss [CLOSED_IMP_FSIGMA_IN, CLOSED_IN_TOPSPACE]
QED

Theorem GDELTA_IN_TOPSPACE :
   !top:'a topology. gdelta_in top (topspace top)
Proof
  SIMP_TAC std_ss [OPEN_IMP_GDELTA_IN, OPEN_IN_TOPSPACE]
QED

Theorem FSIGMA_IN_UNIONS :
   !top t:('a->bool)->bool.
        COUNTABLE t /\ (!s. s IN t ==> fsigma_in top s)
        ==> fsigma_in top (UNIONS t)
Proof
  REWRITE_TAC[fsigma_in, COUNTABLE_UNION_OF_UNIONS]
QED

Theorem FSIGMA_IN_UNION :
   !top s t:'a->bool.
        fsigma_in top s /\ fsigma_in top t ==> fsigma_in top (s UNION t)
Proof
  REWRITE_TAC[fsigma_in, COUNTABLE_UNION_OF_UNION]
QED

Theorem FSIGMA_IN_INTER :
   !top s t:'a->bool.
        fsigma_in top s /\ fsigma_in top t ==> fsigma_in top (s INTER t)
Proof
  GEN_TAC THEN REWRITE_TAC[fsigma_in] THEN
  MATCH_MP_TAC COUNTABLE_UNION_OF_INTER THEN
  REWRITE_TAC[CLOSED_IN_INTER]
QED

Theorem GDELTA_IN_INTERS :
   !top t:('a->bool)->bool.
        COUNTABLE t /\ ~(t = {}) /\ (!s. s IN t ==> gdelta_in top s)
        ==> gdelta_in top (INTERS t)
Proof
  REWRITE_TAC[GDELTA_IN_ALT] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC std_ss [INTERS_SUBSET] THEN
  ASM_SIMP_TAC std_ss [COUNTABLE_INTERSECTION_OF_INTERS]
QED

Theorem GDELTA_IN_INTER :
   !top s t:'a->bool.
        gdelta_in top s /\ gdelta_in top t ==> gdelta_in top (s INTER t)
Proof
  SIMP_TAC std_ss [GSYM INTERS_2, GDELTA_IN_INTERS, COUNTABLE_INSERT, COUNTABLE_EMPTY,
           NOT_INSERT_EMPTY, FORALL_IN_INSERT, NOT_IN_EMPTY]
QED

Theorem GDELTA_IN_UNION :
   !top s t:'a->bool.
        gdelta_in top s /\ gdelta_in top t ==> gdelta_in top (s UNION t)
Proof
  SIMP_TAC std_ss [GDELTA_IN_ALT, UNION_SUBSET] THEN
  MESON_TAC[COUNTABLE_INTERSECTION_OF_UNION, OPEN_IN_UNION]
QED

Theorem FSIGMA_IN_DIFF :
   !top s t:'a->bool.
        fsigma_in top s /\ gdelta_in top t ==> fsigma_in top (s DIFF t)
Proof
  GEN_TAC THEN SUBGOAL_THEN
   ``!s:'a->bool. gdelta_in top s ==> fsigma_in top (topspace top DIFF s)``
  ASSUME_TAC THENL
  [ (* goal 1 (of 2) *)
    SIMP_TAC std_ss [fsigma_in, gdelta_in, FORALL_RELATIVE_TO] THEN
    SIMP_TAC std_ss [FORALL_INTERSECTION_OF, DIFF_INTERS, SET_RULE
     ``s DIFF (s INTER t) = s DIFF t``] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC COUNTABLE_UNION_OF_UNIONS THEN
    ASM_SIMP_TAC std_ss [SIMPLE_IMAGE, COUNTABLE_IMAGE, FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC std_ss [COUNTABLE_UNION_OF_INC, CLOSED_IN_DIFF,
                 CLOSED_IN_TOPSPACE],
    (* goal 2 (of 2) *)
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ``s DIFF t:'a->bool = s INTER (topspace top DIFF t)``
     (fn th => SUBST1_TAC th THEN ASM_SIMP_TAC std_ss [FSIGMA_IN_INTER]) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP FSIGMA_IN_SUBSET) THEN ASM_SET_TAC[] ]
QED

Theorem GDELTA_IN_DIFF :
   !top s t:'a->bool.
        gdelta_in top s /\ fsigma_in top t ==> gdelta_in top (s DIFF t)
Proof
  GEN_TAC THEN SUBGOAL_THEN
   ``!s:'a->bool. fsigma_in top s ==> gdelta_in top (topspace top DIFF s)``
  ASSUME_TAC THENL
  [ (* goal 1 (of 2) *)
    SIMP_TAC std_ss [fsigma_in, gdelta_in, FORALL_UNION_OF, DIFF_UNIONS] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RELATIVE_TO_INC THEN
    MATCH_MP_TAC COUNTABLE_INTERSECTION_OF_INTERS THEN
    ASM_SIMP_TAC std_ss [SIMPLE_IMAGE, COUNTABLE_IMAGE, FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC std_ss [COUNTABLE_INTERSECTION_OF_INC, OPEN_IN_DIFF,
                 OPEN_IN_TOPSPACE],
    (* goal 2 (of 2) *)
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ``s DIFF t:'a->bool = s INTER (topspace top DIFF t)``
     (fn th => SUBST1_TAC th THEN ASM_SIMP_TAC std_ss [GDELTA_IN_INTER]) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP GDELTA_IN_SUBSET) THEN ASM_SET_TAC[] ]
QED

Theorem GDELTA_IN_FSIGMA_IN :
   !top s:'a->bool.
       gdelta_in top s <=>
       s SUBSET topspace top /\ fsigma_in top (topspace top DIFF s)
Proof
  REPEAT GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC std_ss [GDELTA_IN_SUBSET, FSIGMA_IN_DIFF, FSIGMA_IN_TOPSPACE] THEN
  STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o MATCH_MP (SET_RULE
   ``s SUBSET u ==> s = u DIFF (u DIFF s)``)) THEN
  ASM_SIMP_TAC std_ss [GDELTA_IN_DIFF, GDELTA_IN_TOPSPACE]
QED

Theorem FSIGMA_IN_GDELTA_IN :
   !top s:'a->bool.
        fsigma_in top s <=>
        s SUBSET topspace top /\ gdelta_in top (topspace top DIFF s)
Proof
  REPEAT GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC std_ss [FSIGMA_IN_SUBSET, GDELTA_IN_DIFF, GDELTA_IN_TOPSPACE] THEN
  STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o MATCH_MP (SET_RULE
   ``s SUBSET u ==> s = u DIFF (u DIFF s)``)) THEN
  ASM_SIMP_TAC std_ss [FSIGMA_IN_DIFF, FSIGMA_IN_TOPSPACE]
QED

Theorem GDELTA_IN_DESCENDING :
   !top s:'a->bool.
        gdelta_in top s <=>
        ?c. (!n. open_in top (c n)) /\
            (!n. c(n + 1) SUBSET c n) /\
            INTERS {c n | n IN univ(:num)} = s
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[GDELTA_IN_FSIGMA_IN] THEN
  REWRITE_TAC[FSIGMA_IN_ASCENDING] THEN EQ_TAC THENL
  [ (* goal 1 (of 2) *)
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (Q.X_CHOOSE_THEN `c:num->'a->bool` STRIP_ASSUME_TAC)),
    (* goal 2 (of 2) *)
    DISCH_THEN(Q.X_CHOOSE_THEN `c:num->'a->bool` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THENL
    [ FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC INTERS_SUBSET THEN
      ASM_SIMP_TAC std_ss [OPEN_IN_SUBSET, FORALL_IN_GSPEC] THEN SET_TAC[],
      ALL_TAC ] ] THEN
  Q.EXISTS_TAC `\n. topspace top DIFF (c:num->'a->bool) n` THEN
  ASM_SIMP_TAC std_ss [OPEN_IN_DIFF, CLOSED_IN_DIFF, OPEN_IN_TOPSPACE,
    CLOSED_IN_TOPSPACE, SET_RULE ``s SUBSET t ==> u DIFF t SUBSET u DIFF s``]
  THENL
  [ (* goal 1 (of 2) *)
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
     ``u = t DIFF s ==> s SUBSET t ==> s = t DIFF u``)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[DIFF_UNIONS],
    (* goal 2 (of 2) *)
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[DIFF_INTERS] ] THEN
  SIMP_TAC std_ss [SET_RULE ``{g y | y IN {f x | x IN s}} = {g(f x) | x IN s}``] THEN
  SIMP_TAC std_ss [SET_RULE ``s = t INTER s <=> s SUBSET t``] THEN
  MATCH_MP_TAC INTERS_SUBSET THEN
  ASM_SIMP_TAC std_ss [OPEN_IN_SUBSET, FORALL_IN_GSPEC] THEN SET_TAC[]
QED

Theorem FSIGMA_IN_RELATIVE_TO :
   !top s:'a->bool.
        (fsigma_in top relative_to s) = fsigma_in (subtopology top s)
Proof
  REWRITE_TAC[fsigma_in, COUNTABLE_UNION_OF_RELATIVE_TO] THEN
  REWRITE_TAC[CLOSED_IN_RELATIVE_TO]
QED

Theorem FSIGMA_IN_RELATIVE_TO_TOPSPACE :
   !top:'a topology. fsigma_in top relative_to (topspace top) = fsigma_in top
Proof
   rw [FSIGMA_IN_RELATIVE_TO, SUBTOPOLOGY_TOPSPACE]
QED

Theorem FSIGMA_IN_SUBTOPOLOGY :
   !top u s:'a->bool.
         fsigma_in (subtopology top u) s <=>
         ?t. fsigma_in top t /\ s = t INTER u
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM FSIGMA_IN_RELATIVE_TO] THEN
  REWRITE_TAC[relative_to] THEN MESON_TAC[INTER_COMM]
QED

Theorem GDELTA_IN_RELATIVE_TO :
   !top s:'a->bool.
        (gdelta_in top relative_to s) = gdelta_in (subtopology top s)
Proof
  REWRITE_TAC[gdelta_in, RELATIVE_TO_RELATIVE_TO] THEN
  ONCE_REWRITE_TAC[COUNTABLE_INTERSECTION_OF_RELATIVE_TO] THEN
  REWRITE_TAC[OPEN_IN_RELATIVE_TO] THEN
  REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY, TOPSPACE_SUBTOPOLOGY] THEN
  SIMP_TAC std_ss [SET_RULE ``s INTER (u INTER s) = u INTER s``]
QED

Theorem GDELTA_IN_SUBTOPOLOGY :
   !top u s:'a->bool.
         gdelta_in (subtopology top u) s <=>
         ?t. gdelta_in top t /\ s = t INTER u
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM GDELTA_IN_RELATIVE_TO] THEN
  REWRITE_TAC[relative_to] THEN MESON_TAC[INTER_COMM]
QED

Theorem FSIGMA_IN_FSIGMA_SUBTOPOLOGY :
   !top s t:'a->bool.
        fsigma_in top s
        ==> (fsigma_in (subtopology top s) t <=>
             fsigma_in top t /\ t SUBSET s)
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[FSIGMA_IN_SUBTOPOLOGY] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC std_ss [INTER_SUBSET, FSIGMA_IN_INTER] THEN
  Q.EXISTS_TAC `t:'a->bool` THEN ASM_REWRITE_TAC[] THEN ASM_SET_TAC[]
QED

Theorem GDELTA_IN_GDELTA_SUBTOPOLOGY :
   !top s t:'a->bool.
        gdelta_in top s
        ==> (gdelta_in (subtopology top s) t <=>
             gdelta_in top t /\ t SUBSET s)
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[GDELTA_IN_SUBTOPOLOGY] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC std_ss [INTER_SUBSET, GDELTA_IN_INTER] THEN
  Q.EXISTS_TAC `t:'a->bool` THEN ASM_REWRITE_TAC[] THEN ASM_SET_TAC[]
QED

(* ------------------------------------------------------------------------- *)
(* Metrizable spaces (ported from HOL Light)                                 *)
(* ------------------------------------------------------------------------- *)

Definition metrizable_space :
    metrizable_space top = ?m. top = mtopology m
End

Theorem METRIZABLE_SPACE_MTOPOLOGY :
   !m. metrizable_space (mtopology m)
Proof
  REWRITE_TAC[metrizable_space] THEN MESON_TAC[]
QED

Theorem FORALL_METRIC_TOPOLOGY :
   !P. (!m:'a metric. P (mtopology m) (mspace m)) <=>
       !top. metrizable_space top ==> P top (topspace top)
Proof
  SIMP_TAC std_ss [metrizable_space, LEFT_IMP_EXISTS_THM, Once TOPSPACE_MTOPOLOGY]
QED

Theorem FORALL_METRIZABLE_SPACE :
   !P. (!top. metrizable_space top ==> P top (topspace top)) <=>
       (!m:'a metric. P (mtopology m) (mspace m))
Proof
  REWRITE_TAC[FORALL_METRIC_TOPOLOGY]
QED

Theorem EXISTS_METRIZABLE_SPACE :
   !P. (?top. metrizable_space top /\ P top (topspace top)) <=>
       (?m:'a metric. P (mtopology m) (mspace m))
Proof
  SIMP_TAC pure_ss [MESON[] ``(?(x :'a metric). P x) <=> ~(!x. ~P x)``] THEN
  SIMP_TAC pure_ss [FORALL_METRIC_TOPOLOGY] THEN MESON_TAC[]
QED

(* key result *)
Theorem CLOSED_IMP_GDELTA_IN :
   !top s:'a->bool.
        metrizable_space top /\ closed_in top s ==> gdelta_in top s
Proof
  SIMP_TAC std_ss [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_METRIZABLE_SPACE] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC ``s:'a->bool = {}`` THEN ASM_REWRITE_TAC[GDELTA_IN_EMPTY] THEN
  SUBGOAL_THEN
   ``s:'a->bool =
    INTERS
     {{x | x IN mspace m /\
           ?y. y IN s /\ mdist m (x,y) < inv(&n + &1)} | n IN univ(:num)}``
  SUBST1_TAC THENL
  [ (* goal 1 (of 2) *)
    GEN_REWRITE_TAC I empty_rewrites [EXTENSION] THEN Q.X_GEN_TAC `x:'a` THEN
    RW_TAC std_ss [INTERS_GSPEC, IN_UNIV, GSPECIFICATION] THEN EQ_TAC THENL
    [ (* goal 1.1 (of 2) *)
      DISCH_TAC THEN Q.X_GEN_TAC `n:num` THEN
      SUBGOAL_THEN ``(x:'a) IN mspace m`` ASSUME_TAC THENL
      [ ASM_MESON_TAC[CLOSED_IN_SUBSET, SUBSET_DEF, TOPSPACE_MTOPOLOGY],
        ASM_REWRITE_TAC[] THEN Q.EXISTS_TAC `x:'a` THEN
        ASM_SIMP_TAC std_ss [MDIST_REFL, REAL_LT_INV_EQ] THEN rw [] ],
      (* goal 1.2 (of 2) *)
      ASM_CASES_TAC ``(x:'a) IN mspace m`` THEN ASM_REWRITE_TAC[] THEN
      Q.ABBREV_TAC ‘P = \e. ?y. y IN s /\ dist m (x,y) < e’ \\
      ASM_SIMP_TAC std_ss [] \\
      Q_TAC KNOW_TAC ‘(!n. P (inv (&n + 1))) <=> (!e. 0 < e ==> P e)’
      >- (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
          MATCH_MP_TAC FORALL_POS_MONO_1_EQ \\
          rw [Abbr ‘P’] >> Q.EXISTS_TAC ‘y’ >> METIS_TAC [REAL_LT_TRANS]) \\
      DISCH_THEN (ONCE_REWRITE_TAC o wrap) \\
      rw [Abbr ‘P’] \\
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I empty_rewrites [closed_in]) THEN
      REWRITE_TAC[OPEN_IN_MTOPOLOGY, NOT_FORALL_THM, NOT_IMP] THEN
      DISCH_THEN(MP_TAC o SPEC ``x:'a`` o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[IN_DIFF, TOPSPACE_MTOPOLOGY, SUBSET_DEF, IN_MBALL] THEN
      ASM_MESON_TAC[CLOSED_IN_SUBSET, SUBSET_DEF, TOPSPACE_MTOPOLOGY] ],
    (* goal 2 (of 2) *)
    MATCH_MP_TAC GDELTA_IN_INTERS THEN
    SIMP_TAC std_ss [SIMPLE_IMAGE, COUNTABLE_IMAGE, NUM_COUNTABLE] THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY, FORALL_IN_IMAGE, UNIV_NOT_EMPTY, IN_UNIV] THEN
    Q.X_GEN_TAC `n:num` THEN MATCH_MP_TAC OPEN_IMP_GDELTA_IN THEN
    SIMP_TAC std_ss [OPEN_IN_MTOPOLOGY, SUBSET_RESTRICT] THEN
    Q.X_GEN_TAC `x:'a` \\
    RW_TAC std_ss [GSPECIFICATION] \\
    Q.EXISTS_TAC `inv(&n + &1) - mdist m (x:'a,y)` THEN
    ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_MBALL, REAL_SUB_LT, GSPECIFICATION] THEN
    Q.X_GEN_TAC `z:'a` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    Q.EXISTS_TAC `y:'a` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC [METRIC_SYM] \\
    MATCH_MP_TAC REAL_LET_TRANS \\
    Q.EXISTS_TAC ‘dist m (y,x) + dist m (x,z)’ >> REWRITE_TAC [METRIC_TRIANGLE] \\
    ‘y IN mspace m’ (* not really used (in HOL4) *)
       by ASM_MESON_TAC[CLOSED_IN_SUBSET, SUBSET_DEF, TOPSPACE_MTOPOLOGY] \\
    METIS_TAC [REAL_LT_SUB_LADD, METRIC_SYM, REAL_ADD_COMM] ]
QED

Theorem OPEN_IMP_FSIGMA_IN :
   !top s:'a->bool.
        metrizable_space top /\ open_in top s ==> fsigma_in top s
Proof
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC std_ss [FSIGMA_IN_GDELTA_IN, OPEN_IN_SUBSET] THEN
  MATCH_MP_TAC CLOSED_IMP_GDELTA_IN THEN
  ASM_SIMP_TAC std_ss [CLOSED_IN_DIFF, CLOSED_IN_TOPSPACE]
QED

(*---------------------------------------------------------------------------*)
(* Euclidean metric on 2-D real plane (univ(:real) CROSS univ(:real))        *)
(*---------------------------------------------------------------------------*)

val mr2_tm =
   “(\((x1,x2),(y1,y2)). sqrt ((x1 - y1) pow 2 + (x2 - y2) pow 2) :real)”;

Theorem MR2_lemma1[local] :
    !x1 x2 z1 z2. ^mr2_tm ((x1,x2),(z1,z2)) = ^mr2_tm ((x1-z1,x2-z2),(0,0))
Proof
    rw []
QED

Theorem MR2_lemma2[local] :
    !x1 x2 y1 y2. ^mr2_tm ((x1+y1,x2+y2),(0,0)) <=
                  ^mr2_tm ((x1,x2),(0,0)) + ^mr2_tm ((y1,y2),(0,0))
Proof
    rw []
 >> CCONTR_TAC >> fs [real_lte]
 >> Know ‘(sqrt (x1 pow 2 + x2 pow 2) + sqrt (y1 pow 2 + y2 pow 2)) pow 2 <
          (sqrt ((x1 + y1) pow 2 + (x2 + y2) pow 2)) pow 2’
 >- (MATCH_MP_TAC REAL_POW_LT2 >> rw [] \\
     MATCH_MP_TAC REAL_LE_ADD \\
     CONJ_TAC \\ (* 2 subgoals, same tactics *)
     MATCH_MP_TAC SQRT_POS_LE >> MATCH_MP_TAC REAL_LE_ADD >> rw [REAL_LE_POW2])
 >> KILL_TAC
 >> REWRITE_TAC [GSYM real_lte]
 >> Know ‘sqrt ((x1 + y1) pow 2 + (x2 + y2) pow 2) pow 2 =
          (x1 + y1) pow 2 + (x2 + y2) pow 2’
 >- (MATCH_MP_TAC SQRT_POW_2 \\
     MATCH_MP_TAC REAL_LE_ADD >> rw [REAL_LE_POW2])
 >> Rewr'
 >> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [ADD_POW_2]
 >> Know ‘sqrt (x1 pow 2 + x2 pow 2) pow 2 = x1 pow 2 + x2 pow 2’
 >- (MATCH_MP_TAC SQRT_POW_2 \\
     MATCH_MP_TAC REAL_LE_ADD >> rw [REAL_LE_POW2])
 >> Rewr'
 >> Know ‘sqrt (y1 pow 2 + y2 pow 2) pow 2 = y1 pow 2 + y2 pow 2’
 >- (MATCH_MP_TAC SQRT_POW_2 \\
     MATCH_MP_TAC REAL_LE_ADD >> rw [REAL_LE_POW2])
 >> Rewr'
 >> REWRITE_TAC [ADD_POW_2]
 >> Suff ‘x1 * y1 + x2 * y2 <= sqrt (x1 pow 2 + x2 pow 2) * sqrt (y1 pow 2 + y2 pow 2)’
 >- REAL_ARITH_TAC
 >> Know ‘sqrt (x1 pow 2 + x2 pow 2) * sqrt (y1 pow 2 + y2 pow 2) =
          sqrt ((x1 pow 2 + x2 pow 2) * (y1 pow 2 + y2 pow 2))’
 >- (MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC SQRT_MUL \\
     CONJ_TAC \\ (* 2 subgoals, same tactics *)
     MATCH_MP_TAC REAL_LE_ADD >> rw [REAL_LE_POW2])
 >> Rewr'
 >> CCONTR_TAC >> fs [real_lte]
 >> Know ‘(sqrt ((x1 pow 2 + x2 pow 2) * (y1 pow 2 + y2 pow 2))) pow 2 <
          (x1 * y1 + x2 * y2) pow 2’
 >- (MATCH_MP_TAC REAL_POW_LT2 >> rw [] \\
     MATCH_MP_TAC SQRT_POS_LE \\
     MATCH_MP_TAC REAL_LE_MUL \\
     CONJ_TAC >> MATCH_MP_TAC REAL_LE_ADD >> rw [REAL_LE_POW2])
 >> KILL_TAC
 >> REWRITE_TAC [GSYM real_lte]
 >> Know ‘sqrt ((x1 pow 2 + x2 pow 2) * (y1 pow 2 + y2 pow 2)) pow 2 =
          (x1 pow 2 + x2 pow 2) * (y1 pow 2 + y2 pow 2)’
 >- (MATCH_MP_TAC SQRT_POW_2 \\
     MATCH_MP_TAC REAL_LE_MUL \\
     CONJ_TAC >> MATCH_MP_TAC REAL_LE_ADD >> rw [REAL_LE_POW2])
 >> Rewr'
 >> rw [ADD_POW_2, POW_MUL, REAL_ADD_LDISTRIB, REAL_ADD_RDISTRIB]
 >> Suff ‘2 * (x1 * x2 * y1 * y2) <= x1 pow 2 * y2 pow 2 + x2 pow 2 * y1 pow 2’
 >- REAL_ARITH_TAC
 >> Know ‘0 <= (x1 * y2 - x2 * y1) pow 2’ >- rw [REAL_LE_POW2]
 >> ONCE_REWRITE_TAC [POW_2]
 >> REAL_ARITH_TAC
QED

Theorem MR2_lemma3[local] :
    !x1 x2 y1 y2. ^mr2_tm ((x1,x2),(y1,y2)) = ^mr2_tm ((y1,y2),(x1,x2))
Proof
    rw []
 >> Know ‘(x1 - y1) pow 2 = (y1 - x1) pow 2’
 >- (REWRITE_TAC [POW_2] >> REAL_ARITH_TAC)
 >> Rewr'
 >> Know ‘(x2 - y2) pow 2 = (y2 - x2) pow 2’
 >- (REWRITE_TAC [POW_2] >> REAL_ARITH_TAC)
 >> Rewr
QED

Theorem ISMET_R2 :
    ismet ^mr2_tm
Proof
    Q.ABBREV_TAC ‘d = ^mr2_tm’
 >> RW_TAC std_ss [ismet] (* 2 subgoals *)
 >- (Q.UNABBREV_TAC ‘d’ \\
     Cases_on ‘x’ >> Cases_on ‘y’ >> simp [] \\
     reverse EQ_TAC >- rw [SQRT_0, pow_rat] \\
     STRIP_TAC >> rename1 ‘x1 = x2 /\ y1 = y2’ >>
     Cases_on ‘x1 = x2’ >> gvs[pow_rat] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       CCONTR_TAC >>
       Suff ‘0 < (y1 - y2) pow 2’
       >- (METIS_TAC [SQRT_POS_LT, REAL_LT_IMP_NE]) \\
       simp[],
       (* goal 2 (of 2) *)
       Suff ‘0 < (x1 - x2) pow 2 + (y1 - y2) pow 2’
       >- (METIS_TAC [SQRT_POS_LT, REAL_LT_IMP_NE]) \\
       irule REAL_LTE_TRANS >> qexists_tac ‘(x1 - x2) pow 2’ >> simp[]
     ])
 >> Cases_on ‘x’  >> Cases_on ‘y’ >> Cases_on ‘z’
 >> rename1 ‘d ((x1,x2),(z1,z2)) <= d ((y1,y2),(x1,x2)) + d ((y1,y2),(z1,z2))’
 >> Know ‘d ((x1,x2),z1,z2) = d ((x1-z1,x2-z2),(0,0))’
 >- METIS_TAC [MR2_lemma1]
 >> Rewr'
 >> ‘x1 - z1 = x1 - y1 + (y1 - z1)’ by REAL_ARITH_TAC >> POP_ORW
 >> ‘x2 - z2 = x2 - y2 + (y2 - z2)’ by REAL_ARITH_TAC >> POP_ORW
 >> Know ‘d ((y1,y2),(x1,x2)) = d ((x1,x2),(y1,y2))’
 >- METIS_TAC [MR2_lemma3]
 >> Rewr'
 >> Know ‘d ((x1 - y1 + (y1 - z1),x2 - y2 + (y2 - z2)),(0,0)) <=
          d ((x1 - y1,x2 - y2),(0,0)) + d ((y1 - z1,y2 - z2),(0,0))’
 >- METIS_TAC [MR2_lemma2]
 >> Suff ‘d ((x1 - y1,x2 - y2),0,0) + d ((y1 - z1,y2 - z2),0,0) =
          d ((x1,x2),y1,y2) + d ((y1,y2),z1,z2)’ >- rw []
 >> METIS_TAC [MR2_lemma1]
QED

Definition mr2 :
    mr2 = metric ^mr2_tm
End

Theorem MR2_DEF :
    !x1 x2 y1 y2. (dist mr2) ((x1,x2),(y1,y2)) =
                  sqrt ((x1 - y1) pow 2 + (x2 - y2) pow 2)
Proof
    rw [mr2, REWRITE_RULE [metric_tybij] ISMET_R2]
QED

Theorem MR2_MIRROR :
    !x1 x2 y1 y2. (dist mr2) ((-x1,-x2),(-y1,-y2)) = (dist mr2) ((x1,x2),(y1,y2))
Proof
    rw [MR2_DEF, REAL_ARITH “-x - -y = -(x - y)”]
QED

val _ = remove_ovl_mapping "B" {Name = "B", Thy = "metric"};

val _ = export_theory();
