(*===========================================================================*)
(* Metric spaces, including metric on real line                              *)
(*===========================================================================*)

open HolKernel Parse bossLib boolLib;

open BasicProvers boolSimps simpLib mesonLib metisLib jrhUtils pairTheory
     pairLib pred_setTheory quotientTheory realTheory topologyTheory;

val _ = new_theory "metric";

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
(* Now define metric topology and prove equivalent definition of "open"      *)
(*---------------------------------------------------------------------------*)

Definition mtop :
    mtop (m :'a metric) =
    topology (\S'. !x. S' x ==> ?e. &0 < e /\ !y. (dist m)(x,y) < e ==> S' y)
End

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
  ASM_REWRITE_TAC[REAL_LT_HALF1]);

val _ = remove_ovl_mapping "B" {Name = "B", Thy = "metric"};

val _ = export_theory();
