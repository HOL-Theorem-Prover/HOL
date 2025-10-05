(*===========================================================================*)
(* Metric spaces, including metric on real line                              *)
(* ========================================================================= *)
(* Formalization of general topological and metric spaces in HOL Light       *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2017                       *)
(*                (c) Copyright, Marco Maggesi 2014-2017                     *)
(*             (c) Copyright, Andrea Gabrielli  2016-2017                    *)
(* ========================================================================= *)
Theory metric
Ancestors
  arithmetic num pair quotient pred_set real real_sigma cardinal
  topology
Libs
  boolSimps simpLib mesonLib metisLib jrhUtils pairLib
  pred_setLib RealArith tautLib realSimps hurdUtils


fun METIS ths tm = prove(tm,METIS_TAC ths);
val ASM_REAL_ARITH_TAC = REAL_ASM_ARITH_TAC;

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

Theorem METRIC_ISMET:
   !m:('a)metric. ismet (dist m)
Proof
  GEN_TAC THEN REWRITE_TAC[metric_tybij]
QED

Theorem METRIC_ZERO:
   !m:('a)metric. !x y. ((dist m)(x,y) = &0) = (x = y)
Proof
  REPEAT GEN_TAC THEN ASSUME_TAC(SPEC “m:('a)metric” METRIC_ISMET) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ismet]) THEN ASM_REWRITE_TAC[]
QED

Theorem METRIC_SAME:
   !m:('a)metric. !x. (dist m)(x,x) = &0
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[METRIC_ZERO]
QED

Theorem METRIC_POS:
   !m:('a)metric. !x y. &0 <= (dist m)(x,y)
Proof
  REPEAT GEN_TAC THEN ASSUME_TAC(SPEC “m:('a)metric” METRIC_ISMET) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ismet]) THEN
  FIRST_ASSUM(MP_TAC o
             SPECL [“x:'a”, “y:'a”, “y:'a”] o CONJUNCT2) THEN
  REWRITE_TAC[REWRITE_RULE[]
             (SPECL [“m:('a)metric”, “y:'a”, “y:'a”]
                    METRIC_ZERO)]
  THEN CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[REAL_NOT_LE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_ADD2 o W CONJ) THEN
  REWRITE_TAC[REAL_ADD_LID]
QED

Theorem METRIC_SYM:
   !m:('a)metric. !x y. (dist m)(x,y) = (dist m)(y,x)
Proof
  REPEAT GEN_TAC THEN ASSUME_TAC(SPEC “m:('a)metric” METRIC_ISMET) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ismet]) THEN FIRST_ASSUM
   (MP_TAC o GENL [“y:'a”, “z:'a”] o SPECL [“z:'a”, “y:'a”, “z:'a”] o CONJUNCT2)
  THEN REWRITE_TAC[METRIC_SAME, REAL_ADD_RID] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[GSYM REAL_LE_ANTISYM]
QED

Theorem METRIC_TRIANGLE:
   !m:('a)metric. !x y z. (dist m)(x,z) <= (dist m)(x,y) + (dist m)(y,z)
Proof
  REPEAT GEN_TAC THEN ASSUME_TAC(SPEC “m:('a)metric” METRIC_ISMET) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ismet]) THEN
  GEN_REWR_TAC (RAND_CONV o LAND_CONV)  [METRIC_SYM] THEN
  ASM_REWRITE_TAC[]
QED

Theorem METRIC_NZ:
   !m:('a)metric. !x y. ~(x = y) ==> &0 < (dist m)(x,y)
Proof
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [“m:('a)metric”, “x:'a”, “y:'a”] METRIC_ZERO)) THEN
  ONCE_REWRITE_TAC[TAUT ‘~a ==> b <=> b \/ a’] THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN
  REWRITE_TAC[GSYM REAL_LE_LT, METRIC_POS]
QED

(*---------------------------------------------------------------------------*)
(* Get a bounded metric (<1) from any metric                                 *)
(*---------------------------------------------------------------------------*)

val bmetric_tm = “(dist m)(x,y) / (1 + (dist m)(x,y))”;

Definition bounded_metric_def :
    bounded_metric (m :'a metric) = metric (\(x,y). ^bmetric_tm)
End

(* NOTE: This lemma is useful when showing the metric is monotone w.r.t. x or y *)
Theorem bounded_metric_alt :
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
 >> rw [real_div, REAL_SUB_LDISTRIB, REAL_MUL_RINV]
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

Theorem MTOP_OPEN:
   !S' (m:('a)metric). open_in(mtop m) S' =
      (!x. S' x ==> ?e. &0 < e /\ (!y. (dist m(x,y)) < e ==> S' y))
Proof
  GEN_TAC THEN REWRITE_TAC[mtop] THEN
  REWRITE_TAC[REWRITE_RULE[topology_tybij] mtop_istopology] THEN
  BETA_TAC THEN REWRITE_TAC[]
QED

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

(* NOTE: In HOL-Light, a metric m is a pair whose FST (‘mspace m’) is equal to
        ‘topspace (mtop m)’. But in HOL4, this ‘mspace m’ is always UNIV.

   However, HOL4 users can construct a subtopology generated by ‘mtop m’ but is
   restricted to ‘sp = mspace m’ from HOL-Light, i.e. ‘subtopology (mtop m) sp’.

   Adding this theorem into [simp] is not a good idea.
 *)
Theorem TOPSPACE_MTOP :
  topspace (mtop m) = UNIV
Proof
  simp[topspace, EXTENSION] >> csimp[IN_DEF] >> qx_gen_tac ‘x’ >>
  qexists_tac ‘B(m)(x,1)’ >> simp[BALL_OPEN] >>
  simp[ball, METRIC_SAME]
QED

Theorem MSPACE :
    !m. mspace m = UNIV
Proof
    REWRITE_TAC [mspace, TOPSPACE_MTOP]
QED

Theorem BALL_NEIGH:
   !m:('a)metric. !x e. &0 < e ==> neigh(mtop(m))(B(m)(x,e),x)
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[neigh] THEN EXISTS_TAC “B(m)(x:'a,e)” THEN
  REWRITE_TAC[SUBSET_REFL, TOPSPACE_MTOP, SUBSET_UNIV] THEN CONJ_TAC THENL
   [MATCH_MP_TAC BALL_OPEN,
    REWRITE_TAC[ball] THEN BETA_TAC THEN REWRITE_TAC[METRIC_SAME]] THEN
  POP_ASSUM ACCEPT_TAC
QED

(*---------------------------------------------------------------------------*)
(* HOL-Light compatibile theorems (MDIST_)                                   *)
(*---------------------------------------------------------------------------*)

Theorem MDIST_REFL     = METRIC_SAME
Theorem MDIST_SYM      = METRIC_SYM
Theorem MDIST_TRIANGLE = METRIC_TRIANGLE

Theorem MDIST_TRIANGLE_SUB :
    !m x y z. mdist m (x,y) - mdist m (y,z) <= mdist m (x,z)
Proof
    RW_TAC std_ss [REAL_LE_SUB_RADD]
 >> ‘dist m (y,z) = dist m (z,y)’ by rw [METRIC_SYM] >> POP_ORW
 >> rw [MDIST_TRIANGLE]
QED

Theorem MDIST_POS_LE = METRIC_POS
Theorem MDIST_EQ_0   = METRIC_ZERO

Theorem mtopology :
   !m. mtopology (m:'a metric) =
       topology {u | u SUBSET mspace m /\
                     !x:'a. x IN u ==> ?r. &0 < r /\ mball m (x,r) SUBSET u}
Proof
    rw [mtop, MSPACE, ball]
 >> AP_TERM_TAC
 >> rw [Once EXTENSION, IN_APP, SUBSET_DEF]
QED

Theorem mball :
   !m x r. mball m (x:'a,r) =
          {y | x IN mspace m /\ y IN mspace m /\ mdist m (x,y) < r}
Proof
   rw [MSPACE, ball, Once EXTENSION]
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
 >> rw [MSPACE, ball, SUBSET_DEF, IN_APP, Once EXTENSION]
QED

Theorem OPEN_IN_MTOPOLOGY :
   !(m:'a metric) u.
     open_in (mtopology m) u <=>
     u SUBSET mspace m /\
     (!x. x IN u ==> ?r. &0 < r /\ mball m (x,r) SUBSET u)
Proof
    rw [MTOP_OPEN, MSPACE, ball, SUBSET_DEF, IN_APP]
QED

Theorem IN_MBALL :
   !m x (y:'a) r.
     y IN mball m (x,r) <=>
     x IN mspace m /\ y IN mspace m /\ mdist m (x,y) < r
Proof
    rw [mball]
QED

Theorem CENTRE_IN_MBALL :
   !m (x:'a) r. &0 < r /\ x IN mspace m ==> x IN mball m (x,r)
Proof
  SIMP_TAC std_ss[IN_MBALL, MDIST_REFL, real_gt]
QED

Theorem CENTRE_IN_MBALL_EQ :
   !m (x:'a) r. x IN mball m (x,r) <=> x IN mspace m /\ &0 < r
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_MBALL] THEN
  ASM_CASES_TAC “(x:'a) IN mspace m” THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC std_ss[MDIST_REFL]
QED

Theorem MBALL_SUBSET_MSPACE :
   !m (x:'a) r. mball m (x,r) SUBSET mspace m
Proof
  SIMP_TAC std_ss[SUBSET_DEF, IN_MBALL]
QED

Theorem MBALL_EMPTY :
   !m (x:'a) r. r <= &0 ==> mball m (x,r) = {}
Proof
  REWRITE_TAC [IN_MBALL, Once EXTENSION, NOT_IN_EMPTY] THEN
  MESON_TAC[MDIST_POS_LE, REAL_ARITH “!x. ~(r <= &0 /\ &0 <= x /\ x < r)”]
QED

Theorem OPEN_IN_MBALL :
    !m (x:'a) r. open_in (mtopology m) (mball m (x,r))
Proof
  REPEAT GEN_TAC THEN ASM_CASES_TAC “&0 < (r:real)” THENL
  [ALL_TAC, ASM_SIMP_TAC std_ss[MBALL_EMPTY, GSYM REAL_NOT_LT, OPEN_IN_EMPTY]] THEN
  REWRITE_TAC[OPEN_IN_MTOPOLOGY, MBALL_SUBSET_MSPACE, IN_MBALL, SUBSET_DEF]
 >> Q.X_GEN_TAC ‘y’ >> STRIP_TAC
 >> ASM_REWRITE_TAC[]
 >> EXISTS_TAC “r - mdist m (x:'a,y)” >> CONJ_TAC
 >- ASM_REAL_ARITH_TAC
 >> Q.X_GEN_TAC ‘z’
 >> STRIP_TAC
 >> ASM_REWRITE_TAC[]
 >> TRANS_TAC REAL_LET_TRANS “mdist m (x:'a,y) + mdist m (y,z)”
 >> ASM_SIMP_TAC std_ss[MDIST_TRIANGLE]
 >> ASM_REAL_ARITH_TAC
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

Theorem ISMET_R1:
   ismet (\(x,y). abs(y - x:real))
Proof
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
    REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_LID]]
QED

Definition mr1 :
    mr1 = metric(\(x,y). abs(y - x))
End

Theorem MR1_DEF:
   !x y. (dist mr1)(x,y) = abs(y - x)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[mr1, REWRITE_RULE[metric_tybij] ISMET_R1]
  THEN CONV_TAC(ONCE_DEPTH_CONV PAIRED_BETA_CONV) THEN REFL_TAC
QED

Theorem MR1_ADD:
   !x d. (dist mr1)(x,x + d) = abs(d)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[MR1_DEF, REAL_ADD_SUB]
QED

Theorem MR1_SUB:
   !x d. (dist mr1)(x,x - d) = abs(d)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[MR1_DEF, REAL_SUB_SUB, ABS_NEG]
QED

Theorem MR1_ADD_POS:
   !x d. &0 <= d ==> ((dist mr1)(x,x + d) = d)
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[MR1_ADD, abs]
QED

Theorem MR1_SUB_LE:
   !x d. &0 <= d ==> ((dist mr1)(x,x - d) = d)
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[MR1_SUB, abs]
QED

Theorem MR1_ADD_LT:
   !x d. &0 < d ==> ((dist mr1)(x,x + d) = d)
Proof
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
  MATCH_ACCEPT_TAC MR1_ADD_POS
QED

Theorem MR1_SUB_LT:
   !x d. &0 < d ==> ((dist mr1)(x,x - d) = d)
Proof
   REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
  MATCH_ACCEPT_TAC MR1_SUB_LE
QED

Theorem MR1_BETWEEN1:
   !x y z. x < z /\ (dist mr1)(x,y) < (z - x) ==> y < z
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[MR1_DEF, ABS_BETWEEN1]
QED

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

Theorem DIST_REFL:
   !x. dist(x,x) = &0
Proof
  SIMP_TAC std_ss [dist] THEN REAL_ARITH_TAC
QED

Theorem DIST_SYM:
   !x y. dist(x,y) = dist(y,x)
Proof
  SIMP_TAC std_ss [dist] THEN REAL_ARITH_TAC
QED

Theorem DIST_TRIANGLE:
   !x:real y z. dist(x,z) <= dist(x,y) + dist(y,z)
Proof
  SIMP_TAC std_ss [dist] THEN REAL_ARITH_TAC
QED

Theorem DIST_TRIANGLE_ALT:
   !x y z. dist(y,z) <= dist(x,y) + dist(x,z)
Proof
  SIMP_TAC std_ss [dist] THEN REAL_ARITH_TAC
QED

Theorem DIST_EQ_0:
   !x y. (dist(x,y) = 0:real) <=> (x = y)
Proof
  SIMP_TAC std_ss [dist] THEN REAL_ARITH_TAC
QED

Theorem DIST_POS_LT:
   !x y. ~(x = y) ==> &0 < dist(x,y)
Proof
  SIMP_TAC std_ss [dist] THEN REAL_ARITH_TAC
QED

Theorem DIST_NZ:
   !x y. ~(x = y) <=> &0 < dist(x,y)
Proof
  SIMP_TAC std_ss [dist] THEN REAL_ARITH_TAC
QED

Theorem DIST_TRIANGLE_LE:
   !x y z e. dist(x,z) + dist(y,z) <= e ==> dist(x,y) <= e
Proof
  SIMP_TAC std_ss [dist] THEN REAL_ARITH_TAC
QED

Theorem DIST_TRIANGLE_LT:
   !x y z e. dist(x,z) + dist(y,z) < e ==> dist(x,y) < e
Proof
  SIMP_TAC std_ss [dist] THEN REAL_ARITH_TAC
QED

Theorem DIST_TRIANGLE_HALF_L:
   !x1 x2 y. dist(x1,y) < e / &2 /\ dist(x2,y) < e / &2 ==> dist(x1,x2) < e
Proof
  REPEAT STRIP_TAC THEN KNOW_TAC `` dist (x1,y) + dist (x2,y) < e`` THENL
  [METIS_TAC [REAL_LT_ADD2, REAL_HALF_DOUBLE],
   DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC ``dist (x1,y) + dist (x2,y)`` THEN
   METIS_TAC [DIST_TRIANGLE, DIST_SYM]]
QED

Theorem DIST_TRIANGLE_HALF_R:
   !x1 x2 y. dist(y,x1) < e / &2 /\ dist(y,x2) < e / &2 ==> dist(x1,x2) < e
Proof
  REPEAT STRIP_TAC THEN KNOW_TAC `` dist (y, x1) + dist (y, x2) < e`` THENL
  [METIS_TAC [REAL_LT_ADD2, REAL_HALF_DOUBLE],
   DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC ``dist (y, x1) + dist (y, x2)`` THEN
   METIS_TAC [DIST_TRIANGLE, DIST_SYM]]
QED

Theorem DIST_TRIANGLE_ADD:
   !x x' y y'. dist(x + y,x' + y') <= dist(x,x') + dist(y,y')
Proof
  SIMP_TAC std_ss [dist] THEN REAL_ARITH_TAC
QED

Theorem DIST_MUL:
   !x y c. dist(c * x,c * y) = abs(c) * dist(x,y)
Proof
  REWRITE_TAC[dist, GSYM ABS_MUL] THEN REAL_ARITH_TAC
QED

Theorem DIST_TRIANGLE_ADD_HALF:
   !x x' y y':real.
    dist(x,x') < e / &2 /\ dist(y,y') < e / &2 ==> dist(x + y,x' + y') < e
Proof
  REPEAT STRIP_TAC THEN KNOW_TAC `` dist (x, x') + dist (y, y') < e`` THENL
  [METIS_TAC [REAL_LT_ADD2, REAL_HALF_DOUBLE],
   DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC ``dist (x, x') + dist (y, y')`` THEN
   METIS_TAC [DIST_TRIANGLE_ADD, DIST_SYM]]
QED

Theorem DIST_LE_0:
   !x y. dist(x,y) <= &0 <=> (x = y)
Proof
  SIMP_TAC std_ss [dist] THEN REAL_ARITH_TAC
QED

Theorem DIST_POS_LE:
   !x y. &0 <= dist(x,y)
Proof
  METIS_TAC [DIST_EQ_0, DIST_NZ, REAL_LE_LT]
QED

Theorem DIST_EQ:
   !w x y z. (dist(w,x) = dist(y,z)) <=> (dist(w,x) pow 2 = dist(y,z) pow 2)
Proof
  REPEAT GEN_TAC THEN EQ_TAC THENL [RW_TAC std_ss [],
  DISCH_TAC THEN MATCH_MP_TAC POW_EQ THEN EXISTS_TAC ``1:num`` THEN
  RW_TAC arith_ss [DIST_POS_LE]]
QED

Theorem DIST_0:
   !x. (dist(x,0) = abs(x)) /\ (dist(0,x) = abs(x))
Proof
  RW_TAC arith_ss [dist, REAL_SUB_RZERO, REAL_SUB_LZERO, ABS_NEG]
QED

Theorem REAL_CHOOSE_DIST:
   !x e. &0 <= e ==> (?y. dist (x,y) = e)
Proof
  REPEAT STRIP_TAC THEN EXISTS_TAC ``x - e:real`` THEN
  ASM_REWRITE_TAC [dist, REAL_SUB_SUB2, ABS_REFL]
QED

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

(* ------------------------------------------------------------------------- *)
(* Continuous functions on metric spaces.                                    *)
(* ------------------------------------------------------------------------- *)

Theorem METRIC_CONTINUOUS_MAP :
   !m m' (f :'a -> 'b).
     continuous_map (mtopology m,mtopology m') f <=>
     (!x. x IN mspace m ==> f x IN mspace m') /\
     (!a e. &0 < e /\ a IN mspace m
            ==> (?d. &0 < d /\
                     (!x. x IN mspace m /\ mdist m (a,x) < d
                          ==> mdist m' (f a, f x) < e)))
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[continuous_map, TOPSPACE_MTOPOLOGY] THEN
  EQ_TAC THEN SIMP_TAC std_ss[] THENL
 [ (* goal 1 (of 2) *)
   rpt STRIP_TAC THEN
   Q.PAT_X_ASSUM ‘!u. open_in (mtop m') u ==> P’
      (MP_TAC o SPEC “mball m' (f (a:'a):'b,e)”) THEN
   REWRITE_TAC[OPEN_IN_MBALL] THEN
   simp [OPEN_IN_MTOPOLOGY, SUBSET_DEF, IN_MBALL] THEN
   DISCH_THEN (MP_TAC o SPEC “a:'a”) THEN ASM_SIMP_TAC std_ss[MDIST_REFL],
   (* goal 2 (of 2) *)
   rw [OPEN_IN_MTOPOLOGY, SUBSET_DEF, IN_MBALL, MSPACE] THEN
   ASM_MESON_TAC[] ]
QED

Theorem CONTINUOUS_MAP_TO_METRIC :
   !t m (f :'a -> 'b).
     continuous_map (t,mtopology m) f <=>
     (!x. x IN topspace t
          ==> (!r. &0 < r
                   ==> (?u. open_in t u /\
                            x IN u /\
                            (!y. y IN u ==> f y IN mball m (f x,r)))))
Proof
    rpt GEN_TAC
 >> REWRITE_TAC[CONTINUOUS_MAP_EQ_TOPCONTINUOUS_AT, topcontinuous_at,
                TOPSPACE_MTOPOLOGY]
 >> EQ_TAC
 >- (rw [] \\
     Q.PAT_X_ASSUM ‘!x. P’ (MP_TAC o Q.SPEC ‘x’) >> rw [] \\
     POP_ASSUM MATCH_MP_TAC \\
     ASM_SIMP_TAC std_ss[OPEN_IN_MBALL, CENTRE_IN_MBALL])
 >> rw [] >- rw [MSPACE] (* A shortcut *)
 >> Q.PAT_X_ASSUM ‘!x. P’ (MP_TAC o Q.SPEC ‘x’) >> rw []
 >> fs [OPEN_IN_MTOPOLOGY]
 >> Q.PAT_X_ASSUM ‘!x. x IN v ==> _’ (MP_TAC o Q.SPEC ‘f x’) >> rw []
 >> Q.PAT_X_ASSUM ‘!r. 0 < r ==> _’ (MP_TAC o Q.SPEC ‘r’)
 >> rw [IN_MBALL]
 >> Q.EXISTS_TAC ‘u’ >> rw []
 >> Suff ‘f y IN mball m (f x,r)’ >- METIS_TAC [SUBSET_DEF]
 >> Q.PAT_X_ASSUM ‘!y. y IN u ==> _’ (MP_TAC o Q.SPEC ‘y’)
 >> rw [IN_MBALL]
QED

Theorem CONTINUOUS_MAP_FROM_METRIC :
   !m top (f :'a -> 'b).
        continuous_map (mtopology m,top) f <=>
        IMAGE f (mspace m) SUBSET topspace top /\
        !a. a IN mspace m
            ==> !u. open_in top u /\ f(a) IN u
                    ==> ?d. &0 < d /\
                            !x. x IN mspace m /\ mdist m (a,x) < d
                                ==> f x IN u
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTINUOUS_MAP, TOPSPACE_MTOPOLOGY] THEN
  ASM_CASES_TAC “IMAGE (f :'a -> 'b) (mspace m) SUBSET topspace top” THEN
  ASM_REWRITE_TAC[OPEN_IN_MTOPOLOGY] THEN EQ_TAC THEN DISCH_TAC THENL
  [ (* goal 1 (of 2) *)
    X_GEN_TAC “a :'a” THEN DISCH_TAC THEN
    X_GEN_TAC “u :'b set” THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC “u :'b set”) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC “a :'a” o CONJUNCT2) THEN
    simp [SUBSET_DEF, IN_MBALL],
    (* goal 2 (of 2) *)
    X_GEN_TAC “u :'b set” THEN DISCH_TAC THEN
    simp [SUBSET_RESTRICT] THEN
    X_GEN_TAC “a :'a” THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC “a :'a”) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC “u :'b set”) THEN ASM_REWRITE_TAC[] THEN
    simp [SUBSET_DEF, IN_MBALL] ]
QED

(*---------------------------------------------------------------------------*)
(* closed ball in metric space + prove basic properties                      *)
(*  (ported from HOL-Light's Multivariate/metric.ml)                         *)
(*---------------------------------------------------------------------------*)

Theorem CLOSED_IN_METRIC :
   !m (c :'a set).
     closed_in (mtopology m) c <=>
     c SUBSET mspace m /\
     (!x. x IN mspace m DIFF c ==> ?r. &0 < r /\ DISJOINT c (mball m (x,r)))
Proof
    rw[closed_in, OPEN_IN_MTOPOLOGY, DISJOINT_DEF, TOPSPACE_MTOPOLOGY]
 >> MP_TAC MBALL_SUBSET_MSPACE >> ASM_SET_TAC[]
QED

Definition mcball :
    mcball m (x :'a,r) =
      {y | x IN mspace m /\ y IN mspace m /\ mdist m (x,y) <= r}
End

Theorem IN_MCBALL :
   !m (x :'a) r y.
     y IN mcball m (x,r) <=>
     x IN mspace m /\ y IN mspace m /\ mdist m (x,y) <= r
Proof
    rw [mcball]
QED

Theorem CENTRE_IN_MCBALL :
   !m (x :'a) r. &0 <= r /\ x IN mspace m ==> x IN mcball m (x,r)
Proof
  SIMP_TAC std_ss[IN_MCBALL, MDIST_REFL]
QED

Theorem CENTRE_IN_MCBALL_EQ :
   !m (x :'a) r. x IN mcball m (x,r) <=> x IN mspace m /\ &0 <= r
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_MCBALL] THEN
  ASM_CASES_TAC “(x :'a) IN mspace m” THEN ASM_SIMP_TAC std_ss[MDIST_REFL]
QED

Theorem MCBALL_EQ_EMPTY :
   !m (x :'a) r. mcball m (x,r) = {} <=> ~(x IN mspace m) \/ r < &0
Proof
  REPEAT GEN_TAC THEN
  rw [Once EXTENSION, IN_MCBALL, NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[REAL_NOT_LT, REAL_LE_TRANS, MDIST_POS_LE, MDIST_REFL]
QED

Theorem MCBALL_EMPTY :
   !m (x :'a) r. r < &0 ==> mcball m (x,r) = {}
Proof
  SIMP_TAC std_ss[MCBALL_EQ_EMPTY]
QED

Theorem MCBALL_EMPTY_ALT :
   !m (x :'a) r. ~(x IN mspace m) ==> mcball m (x,r) = {}
Proof
  SIMP_TAC std_ss[MCBALL_EQ_EMPTY]
QED

Theorem MCBALL_SUBSET_MSPACE :
   !m (x :'a) r. mcball m (x,r) SUBSET (mspace m)
Proof
  rw [mcball, SUBSET_DEF]
QED

Theorem MBALL_SUBSET_MCBALL :
   !m (x :'a) r. mball m (x,r) SUBSET mcball m (x,r)
Proof
  SIMP_TAC std_ss[SUBSET_DEF, IN_MBALL, IN_MCBALL, REAL_LT_IMP_LE]
QED

Theorem MCBALL_SUBSET :
   !m x (y :'a) a b. y IN mspace m /\ mdist m (x,y) + a <= b
                 ==> mcball m (x,a) SUBSET mcball m (y,b)
Proof
  REPEAT GEN_TAC THEN ASM_CASES_TAC “(x :'a) IN mspace m” THENL
  [STRIP_TAC, rw [MCBALL_EMPTY_ALT]] THEN
  simp [SUBSET_DEF, IN_MCBALL] \\
  Q.X_GEN_TAC ‘z’ \\
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  Suff `mdist m (y,z) <= mdist m (x,y) + mdist m (x,z)` >- REAL_ASM_ARITH_TAC \\
  ASM_MESON_TAC[MDIST_SYM, MDIST_TRIANGLE]
QED

Theorem MCBALL_SUBSET_CONCENTRIC :
   !m (x :'a) a b. a <= b ==> mcball m (x,a) SUBSET mcball m (x,b)
Proof
  SIMP_TAC std_ss[SUBSET_DEF, IN_MCBALL] THEN MESON_TAC[REAL_LE_TRANS]
QED

Theorem CLOSED_IN_MCBALL :
    !(m :'a metric) x r. closed_in (mtopology m) (mcball m (x,r))
Proof
    RW_TAC std_ss [CLOSED_IN_METRIC, MCBALL_SUBSET_MSPACE, IN_MCBALL,
                   DE_MORGAN_THM, REAL_NOT_LE, IN_DIFF]
 >> rename1 ‘y IN mspace m’
 >- (simp [MCBALL_EMPTY_ALT] \\
     Q.EXISTS_TAC ‘1’ >> rw [])
 >> Q.EXISTS_TAC ‘mdist m (x,y) - r’
 >> rw [REAL_SUB_LT]
 >> simp [Once EXTENSION, DISJOINT_DEF, NOT_IN_EMPTY, IN_MBALL, IN_MCBALL]
 >> Q.X_GEN_TAC ‘z’
 >> Cases_on ‘z IN mspace m’ >> rw []
 >> Cases_on ‘x IN mspace m’ >> rw []
 >> STRONG_DISJ_TAC
 >> simp [real_lt]
 >> Know ‘dist m (x,y) - r <= dist m (y,z) <=>
          dist m (x,y) - dist m (y,z) <= r’ >- REAL_ARITH_TAC
 >> Rewr'
 >> Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘dist m (x,z)’ >> art []
 >> rw [MDIST_TRIANGLE_SUB]
QED

(* ------------------------------------------------------------------------- *)
(* More general infimum of distance between two sets.                        *)
(* ------------------------------------------------------------------------- *)

(* This is a generalized ‘setdist’ with a metric parameter d *)
Definition set_dist_def :
    set_dist (d :'a metric) ((s,t) :'a set # 'a set) =
      if (s = {}) \/ (t = {}) then (0 :real)
      else inf {dist d (x,y) | x IN s /\ y IN t}
End

Theorem SET_DIST_EMPTY :
  (!t. set_dist m({},t) = &0) /\ (!s. set_dist m(s,{}) = &0)
Proof
  REWRITE_TAC[set_dist_def]
QED

Theorem SET_DIST_POS_LE :
   !s t. &0 <= set_dist m(s,t)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[set_dist_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_INF THEN
  SIMP_TAC std_ss [FORALL_IN_GSPEC, MDIST_POS_LE] THEN
  SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, EXISTS_PROD] THEN ASM_SET_TAC[]
QED

Theorem SET_DIST_SUBSETS_EQ :
   !s t s' t'.
     s' SUBSET s /\ t' SUBSET t /\
     (!x y. x IN s /\ y IN t
            ==> ?x' y'. x' IN s' /\ y' IN t' /\ dist m(x',y') <= dist m(x,y))
     ==> (set_dist m(s',t') = set_dist m(s,t))
Proof
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC ``s:'a->bool = {}`` THENL
   [ASM_CASES_TAC ``s':'a->bool = {}`` THEN
    ASM_REWRITE_TAC[SET_DIST_EMPTY] THEN ASM_SET_TAC[],
    ALL_TAC] THEN
  ASM_CASES_TAC ``t:'a->bool = {}`` THENL
   [ASM_CASES_TAC ``t':'a->bool = {}`` THEN
    ASM_REWRITE_TAC[SET_DIST_EMPTY] THEN ASM_SET_TAC[],
    ALL_TAC] THEN
  ASM_CASES_TAC ``s':'a->bool = {}`` THENL [ASM_SET_TAC[], ALL_TAC] THEN
  ASM_CASES_TAC ``t':'a->bool = {}`` THENL [ASM_SET_TAC[], ALL_TAC] THEN
  ASM_REWRITE_TAC[set_dist_def] THEN MATCH_MP_TAC INF_EQ THEN
  SIMP_TAC std_ss [FORALL_IN_GSPEC] THEN
  CONJ_TAC >- (SIMP_TAC std_ss [EXTENSION, GSPECIFICATION,
                                EXISTS_PROD, NOT_IN_EMPTY] \\
               fs [GSYM MEMBER_NOT_EMPTY] \\
               rename1 `a IN s'` >> Q.EXISTS_TAC `a` \\
               rename1 `b IN t'` >> Q.EXISTS_TAC `b` \\
               ASM_REWRITE_TAC []) \\
  CONJ_TAC >- (Q.EXISTS_TAC `0` >> rw [MDIST_POS_LE, mspace]) \\
  CONJ_TAC >- (SIMP_TAC std_ss [EXTENSION, GSPECIFICATION,
                                EXISTS_PROD, NOT_IN_EMPTY] \\
               fs [GSYM MEMBER_NOT_EMPTY] \\
               rename1 `a IN s` >> Q.EXISTS_TAC `a` \\
               rename1 `b IN t` >> Q.EXISTS_TAC `b` \\
               ASM_REWRITE_TAC []) \\
  CONJ_TAC >- (Q.EXISTS_TAC `0` >> rw [MDIST_POS_LE, mspace]) \\
  ASM_MESON_TAC[SUBSET_DEF, REAL_LE_TRANS]
QED

Theorem REAL_LE_SET_DIST :
    !s t:'a->bool d.
        ~(s = {}) /\ ~(t = {}) /\
        (!x y. x IN s /\ y IN t ==> d <= dist m(x,y))
        ==> d <= set_dist m(s,t)
Proof
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[set_dist_def] THEN
  MP_TAC(ISPEC ``{dist m(x:'a,y) | x IN s /\ y IN t}`` INF) THEN
  SIMP_TAC std_ss [FORALL_IN_GSPEC] THEN
  KNOW_TAC ``{dist m(x,y) | x IN s /\ y IN t} <> {} /\
             (?b. !x y. x IN s /\ y IN t ==> b <= dist m(x,y))`` THENL
   [CONJ_TAC THENL
    [SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, EXISTS_PROD] THEN
     ASM_SET_TAC[],
     Q.EXISTS_TAC ‘d’ >> rw []],
     DISCH_TAC THEN ASM_REWRITE_TAC []] THEN
  ASM_MESON_TAC[]
QED

Theorem SET_DIST_LE_DIST :
   !s t x y. x IN s /\ y IN t ==> set_dist m(s,t) <= dist m(x,y)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[set_dist_def] THEN
  COND_CASES_TAC THENL [ASM_SET_TAC[], ALL_TAC] THEN
  MP_TAC(ISPEC ``{dist m(x,y) | x IN s /\ y IN t}`` INF) THEN
  SIMP_TAC std_ss [FORALL_IN_GSPEC] THEN
  KNOW_TAC ``{dist m(x,y) | x IN s /\ y IN t} <> {} /\
             (?b. !x y. x IN s /\ y IN t ==> b <= dist m(x,y))`` THENL
   [CONJ_TAC THENL
    [SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, EXISTS_PROD] THEN
     ASM_SET_TAC[],
     Q.EXISTS_TAC ‘0’ >> simp[MDIST_POS_LE]],
     DISCH_TAC THEN ASM_REWRITE_TAC []] THEN
  ASM_MESON_TAC[]
QED

Theorem REAL_LE_SET_DIST_EQ :
   !d s t:'a->bool.
        d <= set_dist m(s,t) <=>
        (!x y. x IN s /\ y IN t ==> d <= dist m(x,y)) /\
        ((s = {}) \/ (t = {}) ==> d <= &0)
Proof
  REPEAT GEN_TAC THEN MAP_EVERY ASM_CASES_TAC
   [``s:'a->bool = {}``, ``t:'a->bool = {}``] THEN
  ASM_REWRITE_TAC[SET_DIST_EMPTY, NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[REAL_LE_SET_DIST, SET_DIST_LE_DIST, REAL_LE_TRANS]
QED

Theorem REAL_SET_DIST_LT_EXISTS :
   !s t:'a->bool b.
        ~(s = {}) /\ ~(t = {}) /\ set_dist m(s,t) < b
        ==> ?x y. x IN s /\ y IN t /\ dist m(x,y) < b
Proof
  REWRITE_TAC[GSYM REAL_NOT_LE, REAL_LE_SET_DIST_EQ] THEN MESON_TAC[]
QED

Theorem SET_DIST_REFL :
   !s:'a->bool. set_dist m(s,s) = &0
Proof
  GEN_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM, SET_DIST_POS_LE] THEN
  ASM_CASES_TAC ``s:'a->bool = {}`` THENL
   [ASM_REWRITE_TAC[set_dist_def, REAL_LE_REFL], ALL_TAC] THEN
  ASM_MESON_TAC[SET_DIST_LE_DIST, MEMBER_NOT_EMPTY, MDIST_REFL]
QED

Theorem SET_DIST_SYM :
   !s t. set_dist m(s,t) = set_dist m(t,s)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[set_dist_def] THEN ONCE_REWRITE_TAC [DISJ_SYM] THEN
  COND_CASES_TAC THEN ONCE_REWRITE_TAC [DISJ_SYM] THEN ASM_SIMP_TAC std_ss [] THEN
  AP_TERM_TAC THEN SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, EXISTS_PROD] THEN
  METIS_TAC[MDIST_SYM]
QED

Theorem SET_DIST_TRIANGLE :
   !s a t:'a->bool.
        set_dist m(s,t) <= set_dist m(s,{a}) + set_dist m({a},t)
Proof
  REPEAT STRIP_TAC THEN ASM_CASES_TAC ``s:'a->bool = {}`` THEN
  ASM_REWRITE_TAC[SET_DIST_EMPTY, REAL_ADD_LID, SET_DIST_POS_LE] THEN
  ASM_CASES_TAC ``t:'a->bool = {}`` THEN
  ASM_REWRITE_TAC[SET_DIST_EMPTY, REAL_ADD_RID, SET_DIST_POS_LE] THEN
  ONCE_REWRITE_TAC[GSYM REAL_LE_SUB_RADD] THEN
  MATCH_MP_TAC REAL_LE_SET_DIST THEN
  ASM_SIMP_TAC std_ss [NOT_INSERT_EMPTY, IN_SING, CONJ_EQ_IMP,
                  RIGHT_FORALL_IMP_THM, UNWIND_FORALL_THM2] THEN
  X_GEN_TAC ``x:'a`` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH ``x - y <= z <=> x - z <= y:real``] THEN
  MATCH_MP_TAC REAL_LE_SET_DIST THEN
  ASM_REWRITE_TAC[NOT_INSERT_EMPTY, IN_SING, CONJ_EQ_IMP,
                  RIGHT_FORALL_IMP_THM, UNWIND_FORALL_THM2] THEN
  X_GEN_TAC ``y:'a`` THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_LE_SUB_RADD] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC ``dist m(x:'a,y')`` THEN
  ASM_SIMP_TAC std_ss [SET_DIST_LE_DIST] THEN
  rename1 ‘z IN t’ THEN
  Q.PAT_X_ASSUM ‘y = a’ (fs o wrap o SYM) \\
  ONCE_REWRITE_TAC [REAL_ADD_COMM] \\
  REWRITE_TAC [MDIST_TRIANGLE]
QED

Theorem SET_DIST_SINGS :
   !x y. set_dist m({x},{y}) = dist m(x,y)
Proof
  REWRITE_TAC[set_dist_def, NOT_INSERT_EMPTY] THEN
  ONCE_REWRITE_TAC [METIS [] ``dist m(x,y) = (\x y. dist m(x,y)) x y``] THEN
  KNOW_TAC ``!f:'a->'a->real x y a b. {f x y | x IN {a} /\ y IN {b}} = {f a b}`` THENL
  [SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, EXISTS_PROD] THEN SET_TAC [],
   DISCH_TAC] THEN ASM_REWRITE_TAC [] THEN
  SIMP_TAC std_ss [INF_INSERT_FINITE, FINITE_EMPTY]
QED

Theorem SET_DIST_LIPSCHITZ :
   !s x (y :'a). abs(set_dist m({x},s) - set_dist m({y},s)) <= dist m(x,y)
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SET_DIST_SINGS] THEN
  REWRITE_TAC[REAL_ARITH
   ``abs(x - y) <= z <=> x <= z + y /\ y <= z + x:real``] THEN
  MESON_TAC[SET_DIST_TRIANGLE, SET_DIST_SYM]
QED

Theorem SET_DIST_SUBSET_RIGHT :
   !s t u:'a->bool.
    ~(t = {}) /\ t SUBSET u ==> set_dist m(s,u) <= set_dist m(s,t)
Proof
  REPEAT STRIP_TAC THEN
  MAP_EVERY ASM_CASES_TAC [``s:'a->bool = {}``, ``u:'a->bool = {}``] THEN
  ASM_SIMP_TAC std_ss [SET_DIST_EMPTY, SET_DIST_POS_LE, REAL_LE_REFL] THEN
  ASM_REWRITE_TAC[set_dist_def] THEN MATCH_MP_TAC REAL_LE_INF_SUBSET THEN
  ASM_SIMP_TAC std_ss [FORALL_IN_GSPEC, SUBSET_DEF, EXISTS_PROD, GSPECIFICATION] THEN
  REPEAT(CONJ_TAC THENL
  [ASM_SIMP_TAC std_ss [EXTENSION, EXISTS_PROD, GSPECIFICATION] THEN ASM_SET_TAC[],
   ALL_TAC]) \\
  Q.EXISTS_TAC ‘0’ >> rw [MDIST_POS_LE]
QED

Theorem SET_DIST_SUBSET_LEFT :
   !s t u:'a->bool.
    ~(s = {}) /\ s SUBSET t ==> set_dist m(t,u) <= set_dist m(s,u)
Proof
  MESON_TAC[SET_DIST_SUBSET_RIGHT, SET_DIST_SYM]
QED

Theorem SET_DIST_UNIQUE :
   !s t a b:'a d.
        a IN s /\ b IN t /\ (dist m(a,b) = d) /\
        (!x y. x IN s /\ y IN t ==> dist m(a,b) <= dist m(x,y))
        ==> (set_dist m(s,t) = d)
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SET_DIST_LE_DIST],
    MATCH_MP_TAC REAL_LE_SET_DIST THEN ASM_SET_TAC[]]
QED

Theorem SET_DIST_UNIV :
   (!s. set_dist m(s,univ(:'a)) = &0) /\
   (!t. set_dist m(univ(:'a),t) = &0)
Proof
  GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV) [SET_DIST_SYM] THEN
  REWRITE_TAC[] THEN X_GEN_TAC ``s:'a->bool`` THEN
  ASM_CASES_TAC ``s:'a->bool = {}`` THEN ASM_REWRITE_TAC[SET_DIST_EMPTY] THEN
  MATCH_MP_TAC SET_DIST_UNIQUE THEN
  SIMP_TAC std_ss [IN_UNIV, MDIST_EQ_0, RIGHT_EXISTS_AND_THM] THEN
  ASM_REWRITE_TAC[UNWIND_THM1, MDIST_REFL, MDIST_POS_LE, MEMBER_NOT_EMPTY]
QED

Theorem SET_DIST_ZERO :
   !s t:'a->bool. ~(DISJOINT s t) ==> (set_dist m(s,t) = &0)
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SET_DIST_UNIQUE THEN
  KNOW_TAC ``?a. a IN s /\ a IN t /\ (dist m(a,a) = 0) /\
             !x y. x IN s /\ y IN t ==> dist m(a,a) <= dist m(x,y)`` THENL
  [ALL_TAC, METIS_TAC []] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r /\ s <=> r /\ p /\ q /\ s`] THEN
  REWRITE_TAC[MDIST_EQ_0, UNWIND_THM2, MDIST_REFL, MDIST_POS_LE] THEN
  ASM_SET_TAC[]
QED

Theorem SET_DIST_LE_SING :
   !s t x:'a. x IN s ==> set_dist m(s,t) <= set_dist m({x},t)
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SET_DIST_SUBSET_LEFT THEN ASM_SET_TAC[]
QED

Theorem SET_DIST_SING_IN_SET :
   !x s. x IN s ==> (set_dist m({x},s) = &0)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC SET_DIST_ZERO
 >> rw [DISJOINT_ALT]
QED

Theorem SET_DIST_EQ_0_CLOSED :
   !s x. closed_in (mtop m) s ==> (set_dist m({x},s) = &0 <=> (s = {}) \/ x IN s)
Proof
    rpt STRIP_TAC
 >> reverse EQ_TAC
 >- (STRIP_TAC >- rw [SET_DIST_EMPTY] \\
     MATCH_MP_TAC SET_DIST_ZERO \\
     rw [DISJOINT_ALT])
 >> DISCH_TAC
 >> Cases_on ‘s = {}’ >> rw []
 >> fs [CLOSED_IN_METRIC, MSPACE]
 >> CCONTR_TAC
 >> Q.PAT_X_ASSUM ‘!x. x NOTIN s ==> _’ (MP_TAC o Q.SPEC ‘x’) >> rw []
 >> STRONG_DISJ_TAC
 >> rw [DISJOINT_ALT, IN_MBALL, MSPACE]
 >> fs [set_dist_def]
 >> qabbrev_tac ‘p = {dist m (x',y) | x' = x /\ y IN s}’
 (* applying INF_CLOSE *)
 >> Know ‘?x. x IN p /\ x < inf p + r’
 >- (MATCH_MP_TAC INF_CLOSE >> art [] \\
     fs [GSYM MEMBER_NOT_EMPTY] \\
     rename1 ‘y IN s’ \\
     Q.EXISTS_TAC ‘dist m (x,y)’ >> rw [Abbr ‘p’] \\
     Q.EXISTS_TAC ‘y’ >> art [])
 >> rw [Abbr ‘p’]
 >> Q.EXISTS_TAC ‘y’ >> art []
QED

(* ------------------------------------------------------------------------- *)
(*  closed ball based on a set                                               *)
(* ------------------------------------------------------------------------- *)

(* Unlike the usual closed ball (cball) generated from a single point, this
   version generates it from a set of points.
 *)
Definition set_mcball_def :
    set_mcball m s e = {x | set_dist m({x},s) <= e}
End

(* NOTE: Usually ‘0 < e’ is assumed, but the lemma also holds when ‘e <= 0’. *)
Theorem closed_in_set_mcball :
    !m s e. closed_in (mtop m) (set_mcball m s e)
Proof
    rw [CLOSED_IN_METRIC, MSPACE, set_mcball_def, GSYM real_lt]
 >> qabbrev_tac ‘d = set_dist m ({x},s)’
 >> qabbrev_tac ‘r = d - e’
 >> ‘0 < r’ by simp [Abbr ‘r’, REAL_SUB_LT]
 >> Q.EXISTS_TAC ‘r’ >> art []
 >> simp [DISJOINT_ALT, IN_MBALL]
 >> Q.X_GEN_TAC ‘y’ >> rw [MSPACE, real_lt]
 (* applying SET_DIST_LIPSCHITZ *)
 >> MP_TAC (Q.SPECL [‘s’, ‘x’, ‘y’] SET_DIST_LIPSCHITZ)
 >> qabbrev_tac ‘r' = dist m (x,y)’
 >> qabbrev_tac ‘d' = set_dist m ({y},s)’
 >> simp []
 >> Cases_on ‘0 <= d - d'’
 >- (‘abs (d - d') = d - d'’ by rw [ABS_REFL] \\
     rw [Abbr ‘r’] \\
     Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘d - d'’ >> simp [] \\
     simp [REAL_LE_SUB_CANCEL1])
 >> fs [GSYM real_lt]
 >> ‘abs (d - d') = -(d - d')’ by rw [ABS_EQ_NEG]
 >> POP_ORW
 >> rw [REAL_NEG_SUB]
 >> fs [REAL_ARITH “a - b < 0 <=> a < (b :real)”, Abbr ‘r’, REAL_SUB_LT]
 >> ‘d < e’ by PROVE_TAC [REAL_LTE_TRANS]
 >> PROVE_TAC [REAL_LT_ANTISYM]
QED

(* ------------------------------------------------------------------------- *)
(*  Lipschitz continuous functions                                           *)
(* ------------------------------------------------------------------------- *)

Definition Lipschitz_condition_def :
    Lipschitz_condition (E1,E2) k f <=>
      !x y. dist E2 (f x,f y) <= k * dist E1 (x,y)
End

(* Definition 13.8 [1, p.249], cf. topologyTheory.continuous_map *)
Definition Lipschitz_continuous_map :
    Lipschitz_continuous_map (E1,E2) f <=>
      ?k. 0 < k /\ Lipschitz_condition (E1,E2) k f
End

(* |- !E1 E2 f.
        Lipschitz_continuous_map (E1,E2) f <=>
        ?k. 0 < k /\ !x y. dist E2 (f x,f y) <= k * dist E1 (x,y)
 *)
Theorem Lipschitz_continuous_map_def =
        Lipschitz_continuous_map |> REWRITE_RULE [Lipschitz_condition_def]

Theorem Lipschitz_continuous_map_imp_continuous_map :
    !E1 E2 f. Lipschitz_continuous_map (E1,E2) f ==>
              continuous_map (mtop E1,mtop E2) f
Proof
    rw [Lipschitz_continuous_map_def, METRIC_CONTINUOUS_MAP, MSPACE]
 >> ‘k <> 0’ by rw [REAL_LT_IMP_NE]
 >> Q.EXISTS_TAC ‘e / k’ >> rw [REAL_LT_DIV]
 >> Q_TAC (TRANS_TAC REAL_LET_TRANS) ‘k * dist E1 (a,x)’ >> art []
QED

(* Another form of SET_DIST_LIPSCHITZ *)
Theorem Lipschitz_continuous_map_set_dist :
    !E s. Lipschitz_continuous_map (E,mr1) (\x. set_dist E ({x},s))
Proof
    rw [Lipschitz_continuous_map_def]
 >> Q.EXISTS_TAC ‘1’
 >> rw [GSYM dist_def, dist, SET_DIST_LIPSCHITZ]
QED

(* Lemma 13.10 [1, p.249] *)
Theorem Lipschitz_continuous_map_exists :
    !E A e. 0 < e ==>
        ?f. Lipschitz_continuous_map (E,mr1) f /\
           (!x. 0 <= f x /\ f x <= 1) /\
           (!x. x IN A ==> f x = 1) /\
           (!x. e <= set_dist E ({x},A) ==> f x = 0)
Proof
    rw [Lipschitz_continuous_map, IN_FUNSET]
 >> qabbrev_tac ‘g :real -> real = \x. max 0 (min 1 x)’
 >> ‘!x. 0 <= g x /\ g x <= 1’
       by rw [Abbr ‘g’, REAL_LE_MAX, REAL_LE_MIN, REAL_MIN_LE, REAL_MAX_LE]
 >> Know ‘!x. 0 <= x /\ x <= 1 ==> g x = x’
 >- (RW_TAC real_ss [Abbr ‘g’, max_def, min_def] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       rw [GSYM REAL_LE_ANTISYM],
       (* goal 2 (of 2) *)
       fs [GSYM real_lt] \\
       Cases_on ‘1 <= x’ >> fs [] \\
       rw [GSYM REAL_LE_ANTISYM, REAL_LT_IMP_LE] ])
 >> DISCH_TAC
 >> ‘!x. 1 <= x ==> g x = 1’ by rw [Abbr ‘g’, min_def]
 >> qabbrev_tac ‘f = \x. 1 - g (set_dist E ({x},A) / e)’
 >> Q.EXISTS_TAC ‘f’ >> simp [mspace]
 >> Know ‘!x. 0 <= f x /\ f x <= 1’
 >- (Q.X_GEN_TAC ‘x’ \\
     simp [Abbr ‘f’, REAL_SUB_LE] \\
     qmatch_abbrev_tac ‘1 - g y <= 1’ \\
     Q.PAT_X_ASSUM ‘!x. 0 <= g x /\ g x <= 1’ (MP_TAC o Q.SPEC ‘y’) \\
     REAL_ARITH_TAC)
 >> DISCH_TAC
 >> ‘!x. x IN A ==> f x = 1’ by rw [Abbr ‘f’, SET_DIST_SING_IN_SET]
 >> simp []
 >> Know ‘!x. e <= set_dist E ({x},A) ==> f x = 0’
 >- (rw [Abbr ‘f’] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     qmatch_abbrev_tac ‘1 <= z / e’ \\
     MATCH_MP_TAC REAL_LE_RDIV >> rw [])
 >> simp [] >> DISCH_TAC
 (* ?k. Lipschitz_condition (E,mr1) k f *)
 >> simp [Lipschitz_condition_def, GSYM dist_def, dist, mspace]
 >> ‘e <> 0’ by rw [REAL_LT_IMP_NE]
 >> Q.EXISTS_TAC ‘1 / e’ >> rw [Abbr ‘f’]
 >> qabbrev_tac ‘a = g (set_dist E ({x},A) / e)’
 >> qabbrev_tac ‘b = g (set_dist E ({y},A) / e)’
 >> simp [REAL_ARITH “1 - a - (1 - b) = b - (a :real)”]
 (* stage work *)
 >> Cases_on ‘x IN A’
 >- (simp [Abbr ‘a’, SET_DIST_SING_IN_SET] \\
    ‘abs b = b’ by rw [ABS_REFL, Abbr ‘b’] >> POP_ORW \\
     qunabbrev_tac ‘b’ \\
     Cases_on ‘y IN A’ >- rw [SET_DIST_SING_IN_SET, MDIST_POS_LE] \\
     qmatch_abbrev_tac ‘e * g (z / e) <= _’ \\
    ‘0 <= z’ by rw [Abbr ‘z’, SET_DIST_POS_LE] \\
     Cases_on ‘e <= z’
     >- (‘1 <= z / e’ by rw [REAL_LE_LDIV_EQ_NEG] \\
         ‘g (z / e) = 1’ by rw [] >> rw [] \\
         Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘z’ >> art [] \\
         simp [Abbr ‘z’, Once SET_DIST_SYM] \\
         MATCH_MP_TAC SET_DIST_LE_DIST >> rw []) \\
     fs [GSYM real_lt] \\
    ‘z / e < 1’ by rw [REAL_LT_LDIV_EQ] \\
     Know ‘g (z / e) = z / e’
     >- (FIRST_X_ASSUM MATCH_MP_TAC >> rw [REAL_LT_IMP_LE]) >> Rewr' \\
     simp [Abbr ‘z’, Once SET_DIST_SYM] \\
     MATCH_MP_TAC SET_DIST_LE_DIST >> rw [])
 >> Cases_on ‘y IN A’
 >- (rw [Abbr ‘b’, SET_DIST_SING_IN_SET, MDIST_POS_LE] \\
    ‘abs a = a’ by rw [ABS_REFL, Abbr ‘a’] >> POP_ORW \\
     qunabbrev_tac ‘a’ \\
     qmatch_abbrev_tac ‘e * g (z / e) <= _’ \\
    ‘0 <= z’ by rw [Abbr ‘z’, SET_DIST_POS_LE] \\
     Cases_on ‘e <= z’
     >- (‘1 <= z / e’ by rw [REAL_LE_LDIV_EQ_NEG] \\
         ‘g (z / e) = 1’ by rw [] >> rw [] \\
         Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘z’ >> art [] \\
         simp [Abbr ‘z’] \\
         MATCH_MP_TAC SET_DIST_LE_DIST >> rw []) \\
     fs [GSYM real_lt] \\
    ‘z / e < 1’ by rw [REAL_LT_LDIV_EQ] \\
     Know ‘g (z / e) = z / e’
     >- (FIRST_X_ASSUM MATCH_MP_TAC >> rw [REAL_LT_IMP_LE]) >> Rewr' \\
     simp [Abbr ‘z’] \\
     MATCH_MP_TAC SET_DIST_LE_DIST >> rw [])
 (* applying SET_DIST_LIPSCHITZ *)
 >> rw [Abbr ‘a’, Abbr ‘b’]
 >> qmatch_abbrev_tac ‘e * abs (g (z1 / e) - g (z2 / e)) <= _’
 >> ‘0 <= z1 /\ 0 <= z2’ by rw [Abbr ‘z1’, Abbr ‘z2’, SET_DIST_POS_LE]
 >> Cases_on ‘e <= z1’
 >- (‘1 <= z1 / e’ by rw [REAL_LE_LDIV_EQ_NEG] \\
     ‘g (z1 / e) = 1’ by rw [] >> POP_ORW \\
     Cases_on ‘e <= z2’
     >- (‘1 <= z2 / e’ by rw [REAL_LE_LDIV_EQ_NEG] \\
         ‘g (z2 / e) = 1’ by rw [] >> POP_ORW \\
         simp [MDIST_POS_LE]) \\
     fs [GSYM real_lt] \\
    ‘z2 / e < 1’ by rw [REAL_LT_LDIV_EQ] \\
     Know ‘g (z2 / e) = z2 / e’
     >- (FIRST_X_ASSUM MATCH_MP_TAC >> rw [REAL_LT_IMP_LE]) >> Rewr' \\
    ‘0 < 1 - z2 / e’ by rw [REAL_SUB_LT] \\
    ‘abs (1 - z2 / e) = 1 - z2 / e’ by rw [ABS_REFL, REAL_LT_IMP_LE] \\
     POP_ORW \\
     simp [REAL_SUB_LDISTRIB, Abbr ‘z2’] \\
     Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘z1 - set_dist E ({x},A)’ \\
     simp [REAL_LE_SUB_CANCEL2, Abbr ‘z1’] \\
     rw [Once MDIST_SYM] \\
     qmatch_abbrev_tac ‘(a :real) - b <= _’ \\
     Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘abs (a - b)’ >> rw [ABS_LE] \\
     simp [Abbr ‘a’, Abbr ‘b’, SET_DIST_LIPSCHITZ])
 >> fs [GSYM real_lt]
 >> Cases_on ‘e <= z2’
 >- (‘1 <= z2 / e’ by rw [REAL_LE_LDIV_EQ_NEG] \\
     ‘g (z2 / e) = 1’ by rw [] >> POP_ORW \\
     ‘z1 / e < 1’ by rw [REAL_LT_LDIV_EQ] \\
     Know ‘g (z1 / e) = z1 / e’
     >- (FIRST_X_ASSUM MATCH_MP_TAC >> rw [REAL_LT_IMP_LE]) >> Rewr' \\
    ‘z1 / e - 1 < 0’ by rw [REAL_LT_SUB_RADD] \\
    ‘abs (z1 / e - 1) = -(z1 / e - 1)’ by rw [ABS_EQ_NEG] >> POP_ORW \\
     REWRITE_TAC [REAL_NEG_SUB] \\
     simp [REAL_SUB_LDISTRIB, Abbr ‘z1’] \\
     Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘z2 - set_dist E ({y},A)’ \\
     simp [REAL_LE_SUB_CANCEL2, Abbr ‘z2’] \\
     qmatch_abbrev_tac ‘(a :real) - b <= _’ \\
     Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘abs (a - b)’ >> rw [ABS_LE] \\
     simp [Abbr ‘a’, Abbr ‘b’, SET_DIST_LIPSCHITZ])
 >> fs [GSYM real_lt]
 >> ‘z1 / e < 1 /\ z2 / e < 1’ by rw [REAL_LT_LDIV_EQ]
 >> Know ‘g (z1 / e) = z1 / e’
 >- (FIRST_X_ASSUM MATCH_MP_TAC >> rw [REAL_LT_IMP_LE])
 >> Rewr'
 >> Know ‘g (z2 / e) = z2 / e’
 >- (FIRST_X_ASSUM MATCH_MP_TAC >> rw [REAL_LT_IMP_LE])
 >> Rewr'
 >> rw [REAL_DIV_SUB, ABS_DIV]
 >> ‘abs e = e’ by rw [ABS_REFL, REAL_LT_IMP_LE] >> POP_ORW
 >> simp [Abbr ‘z1’, Abbr ‘z2’]
 >> rw [Once MDIST_SYM, SET_DIST_LIPSCHITZ]
QED

val _ = remove_ovl_mapping "B" {Name = "B", Thy = "metric"};

(* References:

  [1] Klenke, A.: Probability Theory: A Comprehensive Course. Second Edition.
      Springer Science & Business Media, London (2013).
 *)
