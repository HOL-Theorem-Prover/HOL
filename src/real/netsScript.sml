(*===========================================================================*)
(* Theory of Moore-Smith covergence nets, and special cases like sequences   *)
(*===========================================================================*)

(*
*)
structure netsScript =
struct

(*
app load ["hol88Lib",
          "numLib",
          "reduceLib",
          "pairTheory",
          "PairedLambda",
          "jrhUtils",
          "topologyTheory"];
*)

(*
*)
open HolKernel Parse boolLib hol88Lib numLib reduceLib pairLib
     pairTheory arithmeticTheory numTheory prim_recTheory
     jrhUtils realTheory topologyTheory;

infix THEN THENL ORELSE ORELSEC ##;

val _ = new_theory "nets";

val _ = Parse.reveal "B";

val num_EQ_CONV = Arithconv.NEQ_CONV;

(*---------------------------------------------------------------------------*)
(* Basic definitions: directed set, net, bounded net, pointwise limit        *)
(*---------------------------------------------------------------------------*)

val dorder = new_definition("dorder",
  (--`dorder (g:'a->'a->bool) =
     !x y. g x x /\ g y y ==> ?z. g z z /\ (!w. g w z ==> g w x /\ g w y)`--));

val tends = new_infixr_definition("tends",
  (--`($tends s l)(top,g) =
      !N:'a->bool. neigh(top)(N,l) ==>
            ?n:'b. g n n /\ !m:'b. g m n ==> N(s m)`--), 750);

val bounded = new_definition("bounded",
  (--`bounded(m:('a)metric,(g:'b->'b->bool)) f =
      ?k x N. g N N /\ (!n. g n N ==> (dist m)(f(n),x) < k)`--));

val tendsto = new_definition("tendsto",
  (--`tendsto(m:('a)metric,x) y z =
      &0 < (dist m)(x,y) /\ (dist m)(x,y) <= (dist m)(x,z)`--));

val DORDER_LEMMA = prove_thm("DORDER_LEMMA",
  (--`!g:'a->'a->bool.
      dorder g ==>
        !P Q. (?n. g n n /\ (!m. g m n ==> P m)) /\
              (?n. g n n /\ (!m. g m n ==> Q m))
                  ==> (?n. g n n /\ (!m. g m n ==> P m /\ Q m))`--),
  GEN_TAC THEN REWRITE_TAC[dorder] THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN (--`N1:'a`--) STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN (--`N2:'a`--) STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o SPECL [(--`N1:'a`--), (--`N2:'a`--)]) THEN
  REWRITE_TAC[ASSUME (--`(g:'a->'a->bool) N1 N1`--),ASSUME (--`(g:'a->'a->bool) N2 N2`--)] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`n:'a`--) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC (--`n:'a`--) THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC (--`m:'a`--) THEN DISCH_TAC THEN
  CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  FIRST_ASSUM(UNDISCH_TAC o
    assert(is_conj o snd o dest_imp o snd o dest_forall) o concl) THEN
  DISCH_THEN(MP_TAC o SPEC (--`m:'a`--)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[]);

(*---------------------------------------------------------------------------*)
(* Following tactic is useful in the following proofs                        *)
(*---------------------------------------------------------------------------*)

fun DORDER_THEN tac th =
  let val findpr = snd o dest_imp o body o rand o rand o body o rand
      val [t1,t2] = map (rand o rand o body o rand) (conjuncts(concl th))
      val dog = (rator o rator o rand o rator o body) t1
      val thl = map ((uncurry X_BETA_CONV) o (I ## rand) o dest_abs) [t1,t2]
      val th1 = CONV_RULE(EXACT_CONV thl) th
      val th2 = MATCH_MP DORDER_LEMMA (ASSUME (--`dorder ^dog`--))
      val th3 = MATCH_MP th2 th1
      val th4 = CONV_RULE(EXACT_CONV(map SYM thl)) th3 in
      tac th4 end;

(*---------------------------------------------------------------------------*)
(* Show that sequences and pointwise limits in a metric space are directed   *)
(*---------------------------------------------------------------------------*)

val DORDER_NGE = prove_thm("DORDER_NGE",
  (--`dorder ($>= :num->num->bool)`--),
  REWRITE_TAC[dorder, GREATER_EQ, LESS_EQ_REFL] THEN
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC(SPECL [(--`x:num`--), (--`y:num`--)] LESS_EQ_CASES) THENL
    [EXISTS_TAC (--`y:num`--), EXISTS_TAC (--`x:num`--)] THEN
  GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LESS_EQ_TRANS THENL
    [EXISTS_TAC (--`y:num`--), EXISTS_TAC (--`x:num`--)] THEN
  ASM_REWRITE_TAC[]);

val DORDER_TENDSTO = prove_thm("DORDER_TENDSTO",
  (--`!m:('a)metric. !x. dorder(tendsto(m,x))`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[dorder, tendsto] THEN
  MAP_EVERY X_GEN_TAC [(--`u:'a`--), (--`v:'a`--)] THEN
  REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN ASM_REWRITE_TAC[] THEN
  DISJ_CASES_TAC(SPECL [(--`(dist m)(x:'a,v)`--), (--`(dist m)(x:'a,u)`--)] REAL_LE_TOTAL)
  THENL [EXISTS_TAC (--`v:'a`--), EXISTS_TAC (--`u:'a`--)] THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN FIRST_ASSUM
    (fn th => (EXISTS_TAC o rand o concl) th THEN ASM_REWRITE_TAC[] THEN NO_TAC));

(*---------------------------------------------------------------------------*)
(* Simpler characterization of limit in a metric topology                    *)
(*---------------------------------------------------------------------------*)

val MTOP_TENDS = prove_thm("MTOP_TENDS",
  (--`!d g. !x:'b->'a. !x0. (x tends x0)(mtop(d),g) =
     !e. &0 < e ==> ?n. g n n /\ !m. g m n ==> dist(d)(x(m),x0) < e`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[tends] THEN EQ_TAC THEN DISCH_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC (--`B(d)(x0:'a,e)`--)) THEN
    W(C SUBGOAL_THEN MP_TAC o funpow 2 (rand o rator) o snd) THENL
     [MATCH_MP_TAC BALL_NEIGH THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
    DISCH_THEN(fn th => REWRITE_TAC[th]) THEN REWRITE_TAC[ball] THEN
    BETA_TAC THEN
    GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV) [METRIC_SYM] THEN REWRITE_TAC[],
    GEN_TAC THEN REWRITE_TAC[neigh] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`P:'a->bool`--) STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC (--`open(mtop(d)) (P:'a->bool)`--) THEN
    REWRITE_TAC[MTOP_OPEN] THEN DISCH_THEN(MP_TAC o SPEC (--`x0:'a`--)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`d:real`--) STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o SPEC (--`d:real`--)) THEN
    REWRITE_TAC[ASSUME (--`&0 < d`--)] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`n:'b`--) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (--`n:'b`--) THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC (--`(P:'a->bool) re_subset N`--) THEN
    REWRITE_TAC[re_subset] THEN DISCH_TAC THEN
    REPEAT(FIRST_ASSUM MATCH_MP_TAC) THEN
    ONCE_REWRITE_TAC[METRIC_SYM] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]);

(*---------------------------------------------------------------------------*)
(* Prove that a net in a metric topology cannot converge to different limits *)
(*---------------------------------------------------------------------------*)

val MTOP_TENDS_UNIQ = prove_thm("MTOP_TENDS_UNIQ",
  (--`!g d. dorder (g:'b->'b->bool) ==>
      (x tends x0)(mtop(d),g) /\ (x tends x1)(mtop(d),g) ==> (x0:'a = x1)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[MTOP_TENDS] THEN
  CONV_TAC(ONCE_DEPTH_CONV AND_FORALL_CONV) THEN
  REWRITE_TAC[TAUT_CONV (--`(a ==> b) /\ (a ==> c) = a ==> b /\ c`--)] THEN
  CONV_TAC CONTRAPOS_CONV THEN DISCH_TAC THEN
  CONV_TAC NOT_FORALL_CONV THEN
  EXISTS_TAC (--`dist(d:('a)metric)(x0,x1) / &2`--) THEN
  W(C SUBGOAL_THEN ASSUME_TAC o rand o rator o rand o snd) THENL
   [REWRITE_TAC[REAL_LT_HALF1] THEN MATCH_MP_TAC METRIC_NZ THEN
    FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(DORDER_THEN MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`N:'b`--) (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o SPEC (--`N:'b`--)) THEN ASM_REWRITE_TAC[] THEN
  BETA_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_ADD2) THEN
  REWRITE_TAC[REAL_HALF_DOUBLE, REAL_NOT_LT] THEN
  GEN_REWR_TAC(RAND_CONV o LAND_CONV) [METRIC_SYM] THEN
  MATCH_ACCEPT_TAC METRIC_TRIANGLE);

(*---------------------------------------------------------------------------*)
(* Simpler characterization of limit of a sequence in a metric topology      *)
(*---------------------------------------------------------------------------*)

val geq = Term`$>= : num->num->bool`;

val SEQ_TENDS = prove_thm("SEQ_TENDS",
  (--`!d:('a)metric. !x x0. (x tends x0)(mtop(d), ^geq) =
     !e. &0 < e ==> ?N. !n. ^geq n N ==> dist(d)(x(n),x0) < e`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[MTOP_TENDS, GREATER_EQ, LESS_EQ_REFL]);

(*---------------------------------------------------------------------------*)
(* And of limit of function between metric spaces                            *)
(*---------------------------------------------------------------------------*)

val LIM_TENDS = prove_thm("LIM_TENDS",
  (--`!m1:('a)metric. !m2:('b)metric. !f x0 y0.
      limpt(mtop m1) x0 re_universe ==>
        ((f tends y0)(mtop(m2),tendsto(m1,x0)) =
          !e. &0 < e ==>
            ?d. &0 < d /\ !x. &0 < (dist m1)(x,x0) /\ (dist m1)(x,x0) <= d ==>
              (dist m2)(f(x),y0) < e)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[MTOP_TENDS, tendsto] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  ASM_CASES_TAC (--`&0 < e`--) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_LE_REFL] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN (--`z:'a`--) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (--`(dist m1)(x0:'a,z)`--) THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(ISPECL [(--`m1:('a)metric`--), (--`x0:'a`--), (--`x:'a`--)] METRIC_SYM) THEN
    ASM_REWRITE_TAC[],
    DISCH_THEN(X_CHOOSE_THEN (--`d:real`--) STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC (--`limpt(mtop m1) (x0:'a) re_universe`--) THEN
    REWRITE_TAC[MTOP_LIMPT] THEN
    DISCH_THEN(MP_TAC o SPEC (--`d:real`--)) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[re_universe] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`y:'a`--) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (--`y:'a`--) THEN CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_NZ THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
    X_GEN_TAC (--`x:'a`--) THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC[METRIC_SYM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`(dist m1)(x0:'a,y)`--) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_ASSUM ACCEPT_TAC]);

(*---------------------------------------------------------------------------*)
(* Similar, more conventional version, is also true at a limit point         *)
(*---------------------------------------------------------------------------*)

val LIM_TENDS2 = prove_thm("LIM_TENDS2",
  (--`!m1:('a)metric. !m2:('b)metric. !f x0 y0.
      limpt(mtop m1) x0 re_universe ==>
        ((f tends y0)(mtop(m2),tendsto(m1,x0)) =
          !e. &0 < e ==>
            ?d. &0 < d /\ !x. &0 < (dist m1)(x,x0) /\ (dist m1)(x,x0) < d ==>
              (dist m2)(f(x),y0) < e)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP LIM_TENDS th]) THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN (--`d:real`--) STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC (--`d:real`--) THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[],
    EXISTS_TAC (--`d / &2`--) THEN ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
    GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC (--`d / &2`--) THEN ASM_REWRITE_TAC[REAL_LT_HALF2]]);

(*---------------------------------------------------------------------------*)
(* Simpler characterization of boundedness for the real line                 *)
(*---------------------------------------------------------------------------*)

val MR1_BOUNDED = prove_thm("MR1_BOUNDED",
  (--`!(g:'a->'a->bool) f. bounded(mr1,g) f =
        ?k N. g N N /\ (!n. g n N ==> abs(f n) < k)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[bounded, MR1_DEF] THEN
  (CONV_TAC o LAND_CONV o RAND_CONV o ABS_CONV) SWAP_EXISTS_CONV
  THEN CONV_TAC(ONCE_DEPTH_CONV SWAP_EXISTS_CONV) THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  CONV_TAC(REDEPTH_CONV EXISTS_AND_CONV) THEN
  AP_TERM_TAC THEN EQ_TAC THEN 
  DISCH_THEN(X_CHOOSE_THEN (--`k:real`--) MP_TAC) THENL
   [DISCH_THEN(X_CHOOSE_TAC (--`x:real`--)) THEN
    EXISTS_TAC (--`abs(x) + k`--) THEN GEN_TAC THEN DISCH_TAC THEN
    SUBST1_TAC
      (SYM(SPECL [(--`(f:'a->real) n`--), (--`x:real`--)] REAL_SUB_ADD)) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC (--`abs((f:'a->real) n - x) + abs(x)`--) THEN
    REWRITE_TAC[ABS_TRIANGLE] THEN
    GEN_REWR_TAC RAND_CONV  [REAL_ADD_SYM] THEN
    REWRITE_TAC[REAL_LT_RADD] THEN
    ONCE_REWRITE_TAC[ABS_SUB] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC,
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [(--`k:real`--), (--`&0`--)] THEN
    ASM_REWRITE_TAC[REAL_SUB_LZERO, ABS_NEG]]);

(*---------------------------------------------------------------------------*)
(* Firstly, prove useful forms of null and bounded nets                      *)
(*---------------------------------------------------------------------------*)

val NET_NULL = prove_thm("NET_NULL",
  (--`!g:'a->'a->bool. !x x0.
      (x tends x0)(mtop(mr1),g) = ((\n. x(n) - x0) tends &0)(mtop(mr1),g)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[MTOP_TENDS] THEN BETA_TAC THEN
  REWRITE_TAC[MR1_DEF, REAL_SUB_LZERO] THEN EQUAL_TAC THEN
  REWRITE_TAC[REAL_NEG_SUB]);

val NET_CONV_BOUNDED = prove_thm("NET_CONV_BOUNDED",
  (--`!g:'a->'a->bool. !x x0.
      (x tends x0)(mtop(mr1),g) ==> bounded(mr1,g) x`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[MTOP_TENDS, bounded] THEN
  DISCH_THEN(MP_TAC o SPEC (--`&1`--)) THEN
  REWRITE_TAC[REAL_LT, ONE, LESS_0] THEN
  REWRITE_TAC[GSYM(ONE)] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`N:'a`--) STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [(--`&1`--), (--`x0:real`--), (--`N:'a`--)] THEN
  ASM_REWRITE_TAC[]);

val NET_CONV_NZ = prove_thm("NET_CONV_NZ",
  (--`!g:'a->'a->bool. !x x0.
      (x tends x0)(mtop(mr1),g) /\ ~(x0 = &0) ==>
        ?N. g N N /\ (!n. g n N ==> ~(x n = &0))`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[MTOP_TENDS, bounded] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC (--`abs(x0)`--)) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[GSYM ABS_NZ] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`N:'a`--) (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_TAC THEN EXISTS_TAC (--`N:'a`--) THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
  CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MR1_DEF, REAL_SUB_RZERO, REAL_LT_REFL]);

val NET_CONV_IBOUNDED = prove_thm("NET_CONV_IBOUNDED",
  (--`!g:'a->'a->bool. !x x0.
      (x tends x0)(mtop(mr1),g) /\ ~(x0 = &0) ==>
        bounded(mr1,g) (\n. inv(x n))`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[MTOP_TENDS, MR1_BOUNDED, MR1_DEF] THEN
  BETA_TAC THEN REWRITE_TAC[ABS_NZ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC (--`abs(x0) / &2`--)) THEN
  ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`N:'a`--) STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [(--`&2 / abs(x0)`--), (--`N:'a`--)] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC (--`n:'a`--) THEN
  DISCH_THEN(ANTE_RES_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN (--`(abs(x0) / & 2) < abs(x(n:'a))`--) ASSUME_TAC THENL
   [SUBST1_TAC(SYM(SPECL [(--`abs(x0) / &2`--), (--`abs(x0) / &2`--), (--`abs(x(n:'a))`--)]
      REAL_LT_LADD)) THEN
    REWRITE_TAC[REAL_HALF_DOUBLE] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC (--`abs(x0 - x(n:'a)) + abs(x(n))`--) THEN
    ASM_REWRITE_TAC[REAL_LT_RADD] THEN
    SUBST1_TAC(SYM(AP_TERM (--`abs`--)
      (SPECL [(--`x0:real`--), (--`x(n:'a):real`--)] REAL_SUB_ADD))) THEN
    MATCH_ACCEPT_TAC ABS_TRIANGLE, ALL_TAC] THEN
  SUBGOAL_THEN (--`&0 < abs(x(n:'a))`--) ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (--`abs(x0) / &2`--) THEN
    ASM_REWRITE_TAC[REAL_LT_HALF1], ALL_TAC] THEN
  SUBGOAL_THEN (--`&2 / abs(x0) = inv(abs(x0) / &2)`--) SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_RINV_UNIQ THEN REWRITE_TAC[real_div] THEN
    ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
        (--`(a * b) * (c * d) = (d * a) * (b * c)`--)] THEN
    SUBGOAL_THEN (--`~(abs(x0) = &0) /\ ~(&2 = &0)`--)
      (fn th => CONJUNCTS_THEN(SUBST1_TAC o MATCH_MP REAL_MUL_LINV) th
            THEN REWRITE_TAC[REAL_MUL_LID]) THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[ABS_NZ, ABS_ABS],
      REWRITE_TAC[REAL_INJ] THEN CONV_TAC(RAND_CONV num_EQ_CONV) THEN
      REWRITE_TAC[]], ALL_TAC] THEN
  SUBGOAL_THEN (--`~(x(n:'a) = &0)`--) (SUBST1_TAC o MATCH_MP ABS_INV) THENL
   [ASM_REWRITE_TAC[ABS_NZ], ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[REAL_LT_HALF1]);

(*---------------------------------------------------------------------------*)
(* Now combining theorems for null nets                                      *)
(*---------------------------------------------------------------------------*)

val NET_NULL_ADD = prove_thm("NET_NULL_ADD",
  (--`!g:'a->'a->bool. dorder g ==>
        !x y. (x tends &0)(mtop(mr1),g) /\ (y tends &0)(mtop(mr1),g) ==>
                ((\n. x(n) + y(n)) tends &0)(mtop(mr1),g)`--),
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[MTOP_TENDS, MR1_DEF, REAL_SUB_LZERO, ABS_NEG] THEN
  DISCH_THEN(curry op THEN (X_GEN_TAC (--`e:real`--) THEN DISCH_TAC) o
    MP_TAC o end_itlist CONJ o map (SPEC (--`e / &2`--)) o CONJUNCTS) THEN
  ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
  DISCH_THEN(DORDER_THEN (X_CHOOSE_THEN (--`N:'a`--) STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC (--`N:'a`--) THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN ASSUME_TAC) THEN
  BETA_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC (--`abs(x(m:'a)) + abs(y(m:'a))`--) THEN
  REWRITE_TAC[ABS_TRIANGLE] THEN RULE_ASSUM_TAC BETA_RULE THEN
  GEN_REWR_TAC RAND_CONV [GSYM REAL_HALF_DOUBLE] THEN
  MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC[]);

val NET_NULL_MUL = prove_thm("NET_NULL_MUL",
  (--`!g:'a->'a->bool. dorder g ==>
      !x y. bounded(mr1,g) x /\ (y tends &0)(mtop(mr1),g) ==>
              ((\n. x(n) * y(n)) tends &0)(mtop(mr1),g)`--),
  GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[MR1_BOUNDED] THEN
  REWRITE_TAC[MTOP_TENDS, MR1_DEF, REAL_SUB_LZERO, ABS_NEG] THEN
  DISCH_THEN(curry op THEN (X_GEN_TAC (--`e:real`--) THEN DISCH_TAC) o MP_TAC) THEN
  CONV_TAC(LAND_CONV LEFT_AND_EXISTS_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`k:real`--) MP_TAC) THEN
  DISCH_THEN(ASSUME_TAC o uncurry CONJ o (I ## SPEC (--`e / k`--)) o CONJ_PAIR) THEN
  SUBGOAL_THEN (--`&0 < k`--) ASSUME_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_THEN (--`N:'a`--)
      (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) o CONJUNCT1) THEN
    DISCH_THEN(MP_TAC o SPEC (--`N:'a`--)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC (--`abs(x(N:'a))`--) THEN ASM_REWRITE_TAC[ABS_POS], ALL_TAC] THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_conj o concl) THEN
  SUBGOAL_THEN (--`&0 < e / k`--) ASSUME_TAC THENL
   [FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_LT_RDIV_0 th] THEN
    ASM_REWRITE_TAC[] THEN NO_TAC), ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DORDER_THEN(X_CHOOSE_THEN (--`N:'a`--) STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC (--`N:'a`--) THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN (ASSUME_TAC o BETA_RULE)) THEN
  SUBGOAL_THEN (--`e = k * (e / k)`--) SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
    DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (--`&0 < &0`--) THEN
    REWRITE_TAC[REAL_LT_REFL], ALL_TAC] THEN BETA_TAC THEN
  REWRITE_TAC[ABS_MUL] THEN MATCH_MP_TAC REAL_LT_MUL2 THEN
  ASM_REWRITE_TAC[ABS_POS]);

val NET_NULL_CMUL = prove_thm("NET_NULL_CMUL",
  (--`!g:'a->'a->bool. !k x.
      (x tends &0)(mtop(mr1),g) ==> ((\n. k * x(n)) tends &0)(mtop(mr1),g)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[MTOP_TENDS, MR1_DEF] THEN
  BETA_TAC THEN REWRITE_TAC[REAL_SUB_LZERO, ABS_NEG] THEN
  DISCH_THEN(curry op THEN (X_GEN_TAC (--`e:real`--) THEN DISCH_TAC) o MP_TAC) THEN
  ASM_CASES_TAC (--`k = &0`--) THENL
   [DISCH_THEN(MP_TAC o SPEC (--`&1`--)) THEN
    REWRITE_TAC[REAL_LT, ONE, LESS_SUC_REFL] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`N:'a`--) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (--`N:'a`--) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO, abs, REAL_LE_REFL],
    DISCH_THEN(MP_TAC o SPEC (--`e / abs(k)`--)) THEN
    SUBGOAL_THEN (--`&0 < e / abs(k)`--) ASSUME_TAC THENL
     [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_INV_POS THEN
      ASM_REWRITE_TAC[GSYM ABS_NZ], ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`N:'a`--) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (--`N:'a`--) THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN (--`e = abs(k) * (e / abs(k))`--) SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
      ASM_REWRITE_TAC[ABS_ZERO], ALL_TAC] THEN
    REWRITE_TAC[ABS_MUL] THEN
    SUBGOAL_THEN (--`&0 < abs k`--) (fn th => REWRITE_TAC[MATCH_MP REAL_LT_LMUL th])
    THEN ASM_REWRITE_TAC[GSYM ABS_NZ]]);

(*---------------------------------------------------------------------------*)
(* Now real arithmetic theorems for convergent nets                          *)
(*---------------------------------------------------------------------------*)

val NET_ADD = prove_thm("NET_ADD",
  (--`!g:'a->'a->bool. dorder g ==>
      !x x0 y y0. (x tends x0)(mtop(mr1),g) /\ (y tends y0)(mtop(mr1),g) ==>
                      ((\n. x(n) + y(n)) tends (x0 + y0))(mtop(mr1),g)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[NET_NULL] THEN
  DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th o MATCH_MP NET_NULL_ADD))
  THEN MATCH_MP_TAC(TAUT_CONV (--`(a = b) ==> a ==> b`--)) THEN EQUAL_TAC THEN
  BETA_TAC THEN REWRITE_TAC[real_sub, REAL_NEG_ADD] THEN
  CONV_TAC(AC_CONV(REAL_ADD_ASSOC,REAL_ADD_SYM)));

val NET_NEG = prove_thm("NET_NEG",
  (--`!g:'a->'a->bool. dorder g ==>
        (!x x0. (x tends x0)(mtop(mr1),g) =
                  ((\n. ~(x n)) tends ~x0)(mtop(mr1),g))`--),
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[MTOP_TENDS, MR1_DEF] THEN BETA_TAC THEN
  REWRITE_TAC[REAL_SUB_NEG2] THEN
  GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ABS_SUB]
  THEN REFL_TAC);

val NET_SUB = prove_thm("NET_SUB",
  (--`!g:'a->'a->bool. dorder g ==>
      !x x0 y y0. (x tends x0)(mtop(mr1),g) /\ (y tends y0)(mtop(mr1),g) ==>
                      ((\n. x(n) - y(n)) tends (x0 - y0))(mtop(mr1),g)`--),
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[real_sub] THEN
  CONV_TAC(EXACT_CONV[X_BETA_CONV (--`n:'a`--) (--`~(y (n:'a))`--)]) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP NET_ADD) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fn th => ONCE_REWRITE_TAC[GSYM(MATCH_MP NET_NEG th)]) THEN
  ASM_REWRITE_TAC[]);

val NET_MUL = prove_thm("NET_MUL",
  (--`!g:'a->'a->bool. dorder g ==>
        !x y x0 y0. (x tends x0)(mtop(mr1),g) /\ (y tends y0)(mtop(mr1),g) ==>
              ((\n. x(n) * y(n)) tends (x0 * y0))(mtop(mr1),g)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[NET_NULL] THEN
  DISCH_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN (--`!a b c d. (a * b) - (c * d) =
                             (a * (b - d)) + ((a - c) * d)`--)
  (fn th => ONCE_REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[real_sub, REAL_LDISTRIB, REAL_RDISTRIB, GSYM REAL_ADD_ASSOC]
    THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL, GSYM REAL_NEG_RMUL] THEN
    REWRITE_TAC[REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_LID], ALL_TAC] THEN
  CONV_TAC(EXACT_CONV[X_BETA_CONV (--`n:'a`--) (--`x(n:'a) * (y(n) - y0)`--)]) THEN
  CONV_TAC(EXACT_CONV[X_BETA_CONV (--`n:'a`--) (--`(x(n:'a) - x0) * y0`--)]) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP NET_NULL_ADD) THEN
  GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
  (CONV_TAC o EXACT_CONV o map (X_BETA_CONV (--`n:'a`--)))
   [(--`y(n:'a) - y0`--), (--`x(n:'a) - x0`--)] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP NET_NULL_MUL) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NET_CONV_BOUNDED THEN
    EXISTS_TAC (--`x0:real`--) THEN ONCE_REWRITE_TAC[NET_NULL] THEN
    ASM_REWRITE_TAC[],
    MATCH_MP_TAC NET_NULL_CMUL THEN ASM_REWRITE_TAC[]]);

val NET_INV = prove_thm("NET_INV",
  (--`!g:'a->'a->bool. dorder g ==>
        !x x0. (x tends x0)(mtop(mr1),g) /\ ~(x0 = &0) ==>
                   ((\n. inv(x(n))) tends inv x0)(mtop(mr1),g)`--),
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fn th => STRIP_ASSUME_TAC th THEN
    MP_TAC(CONJ (MATCH_MP NET_CONV_IBOUNDED th)
                    (MATCH_MP NET_CONV_NZ th))) THEN
  REWRITE_TAC[MR1_BOUNDED] THEN
  CONV_TAC(ONCE_DEPTH_CONV LEFT_AND_EXISTS_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`k:real`--) MP_TAC) THEN
  DISCH_THEN(DORDER_THEN MP_TAC) THEN BETA_TAC THEN
  DISCH_THEN(MP_TAC o C CONJ(ASSUME (--`(x tends x0)(mtop mr1,(g:'a->'a->bool))`--))) THEN
  ONCE_REWRITE_TAC[NET_NULL] THEN
  REWRITE_TAC[MTOP_TENDS, MR1_DEF, REAL_SUB_LZERO, ABS_NEG] THEN BETA_TAC
  THEN DISCH_THEN(curry op THEN (X_GEN_TAC (--`e:real`--) THEN DISCH_TAC) o MP_TAC) THEN
  CONV_TAC(ONCE_DEPTH_CONV RIGHT_AND_FORALL_CONV) THEN
  DISCH_THEN(ASSUME_TAC o SPEC (--`e * (abs(x0) * (inv k))`--)) THEN
  SUBGOAL_THEN (--`&0 < k`--) ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1) THEN
    DISCH_THEN(X_CHOOSE_THEN (--`N:'a`--) (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(MP_TAC o SPEC (--`N:'a`--)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`abs(inv(x(N:'a)))`--) THEN
    ASM_REWRITE_TAC[ABS_POS], ALL_TAC] THEN
  SUBGOAL_THEN (--`&0 < e * (abs(x0) * inv k)`--) ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[GSYM ABS_NZ] THEN
    MATCH_MP_TAC REAL_INV_POS THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_conj o concl) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(DORDER_THEN MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`N:'a`--) (CONJUNCTS_THEN ASSUME_TAC)) THEN
  EXISTS_TAC (--`N:'a`--) THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC (--`n:'a`--) THEN DISCH_THEN(ANTE_RES_THEN STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC BETA_RULE THEN POP_ASSUM_LIST(MAP_EVERY STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN (--`inv(x n) - inv x0 =
                inv(x n) * (inv x0 * (x0 - x(n:'a)))`--) SUBST1_TAC THENL
   [REWRITE_TAC[REAL_SUB_LDISTRIB] THEN
    REWRITE_TAC[MATCH_MP REAL_MUL_LINV (ASSUME (--`~(x0 = &0)`--))] THEN
    REWRITE_TAC[REAL_MUL_RID] THEN REPEAT AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC[MATCH_MP REAL_MUL_RINV (ASSUME (--`~(x(n:'a) = &0)`--))] THEN
    REWRITE_TAC[REAL_MUL_RID], ALL_TAC] THEN
  REWRITE_TAC[ABS_MUL] THEN ONCE_REWRITE_TAC[ABS_SUB] THEN
  SUBGOAL_THEN (--`e = e * ((abs(inv x0) * abs(x0)) * (inv k * k))`--)
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM ABS_MUL] THEN
    REWRITE_TAC[MATCH_MP REAL_MUL_LINV (ASSUME (--`~(x0 = &0)`--))] THEN
    REWRITE_TAC[MATCH_MP REAL_MUL_LINV
      (GSYM(MATCH_MP REAL_LT_IMP_NE (ASSUME (--`&0 < k`--))))] THEN
    REWRITE_TAC[REAL_MUL_RID] THEN
    REWRITE_TAC[abs, REAL_LE, LESS_OR_EQ, ONE, LESS_SUC_REFL] THEN
    REWRITE_TAC[SYM ONE, REAL_MUL_RID], ALL_TAC] THEN
  ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
    (--`a * ((b * c) * (d * e)) = e * (b * (a * (c * d)))`--)] THEN
  REWRITE_TAC[GSYM ABS_MUL] THEN
  MATCH_MP_TAC ABS_LT_MUL2 THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ABS_MUL] THEN SUBGOAL_THEN (--`&0 < abs(inv x0)`--)
    (fn th => ASM_REWRITE_TAC[MATCH_MP REAL_LT_LMUL th]) THEN
  REWRITE_TAC[GSYM ABS_NZ] THEN
  MATCH_MP_TAC REAL_INV_NZ THEN ASM_REWRITE_TAC[]);

val NET_DIV = prove_thm("NET_DIV",
  (--`!g:'a->'a->bool. dorder g ==>
      !x x0 y y0. (x tends x0)(mtop(mr1),g) /\
                  (y tends y0)(mtop(mr1),g) /\ ~(y0 = &0) ==>
                      ((\n. x(n) / y(n)) tends (x0 / y0))(mtop(mr1),g)`--),
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[real_div] THEN
  CONV_TAC(EXACT_CONV[X_BETA_CONV (--`n:'a`--) (--`inv(y(n:'a))`--)]) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP NET_MUL) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP NET_INV) THEN
  ASM_REWRITE_TAC[]);

val NET_ABS = prove_thm("NET_ABS",
  (--`!g x x0. (x tends x0)(mtop(mr1),g) ==>
               ((\n:'a. abs(x n)) tends abs(x0))(mtop(mr1),g)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[MTOP_TENDS] THEN
  DISCH_TAC THEN X_GEN_TAC (--`e:real`--) THEN
  DISCH_THEN(fn th => POP_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`N:'a`--) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC (--`N:'a`--) THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC (--`n:'a`--) THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC (--`dist(mr1)(x(n:'a),x0)`--) THEN CONJ_TAC THENL
   [REWRITE_TAC[MR1_DEF, ABS_SUB_ABS],
    FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]);

(*---------------------------------------------------------------------------*)
(* Comparison between limits                                                 *)
(*---------------------------------------------------------------------------*)

val NET_LE = prove_thm("NET_LE",
  (--`!g:'a->'a->bool. dorder g ==>
      !x x0 y y0. (x tends x0)(mtop(mr1),g) /\
                  (y tends y0)(mtop(mr1),g) /\
                  (?N. g N N /\ !n. g n N ==> x(n) <= y(n))
                        ==> x0 <= y0`--),
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  GEN_REWR_TAC I [TAUT_CONV (--`a = ~~a:bool`--)] THEN
  PURE_ONCE_REWRITE_TAC[REAL_NOT_LE] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN DISCH_TAC THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_conj o concl) THEN
  REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[MTOP_TENDS] THEN
  DISCH_THEN(MP_TAC o end_itlist CONJ o
    map (SPEC (--`(x0 - y0) / &2`--)) o CONJUNCTS) THEN
  ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
  DISCH_THEN(DORDER_THEN MP_TAC) THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_exists o concl) THEN
  DISCH_THEN(fn th1 => DISCH_THEN (fn th2 => MP_TAC(CONJ th1 th2))) THEN
  DISCH_THEN(DORDER_THEN MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`N:'a`--) (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  BETA_TAC THEN DISCH_THEN(MP_TAC o SPEC (--`N:'a`--)) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MR1_DEF] THEN ONCE_REWRITE_TAC[ABS_SUB] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[REAL_NOT_LE] THEN MATCH_MP_TAC ABS_BETWEEN2 THEN
  MAP_EVERY EXISTS_TAC [(--`y0:real`--), (--`x0:real`--)] THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  FIRST_ASSUM ACCEPT_TAC);

val _ = export_theory();

(*
*)
end;
