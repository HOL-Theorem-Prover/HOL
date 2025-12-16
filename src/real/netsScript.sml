(*===========================================================================*)
(* Theory of Moore-Smith convergence nets, and special cases like sequences  *)
(*===========================================================================*)

Theory nets
Ancestors
  pred_set pair arithmetic num prim_rec relation real topology
  metric
Libs
  numLib reduceLib pairLib mesonLib RealArith hurdUtils jrhUtils
  tautLib

val _ = Parse.reveal "B";

val num_EQ_CONV = Arithconv.NEQ_CONV;
val DISC_RW_KILL = DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
                   POP_ASSUM K_TAC;

(*---------------------------------------------------------------------------*)
(* Basic definitions: directed order, net, bounded net, pointwise limit [1]  *)
(*---------------------------------------------------------------------------*)

(* NOTE: According to [1], the property ‘!w. g w z ==> g w x /\ g w y’ is called
  "composition property".
 *)
Definition dorder :
   dorder (g:'a->'a->bool) =
     !x y. g x x /\ g y y ==> ?z. g z z /\ (!w. g w z ==> g w x /\ g w y)
End

val _ = set_fixity "tends" (Infixr 750);

(* A general function (s :'b -> 'a) tends to l (w.r.t. top and g) if for all
   neigh N of l, "eventually" g(m) IN N.
 *)
Definition tends :
   (s tends l) (top,g) =
      !N:'a->bool. neigh(top)(N,l) ==>
            ?n:'b. g n n /\ !m:'b. g m n ==> N(s m)
End

Definition bounded :
   bounded(m:('a)metric,(g:'b->'b->bool)) f =
      ?k x N. g N N /\ (!n. g n N ==> (dist m)(f(n),x) < k)
End

(* ‘tendsto (m,x)’ is a dorder defined on a metric. See also DORDER_TENDSTO.

   NOTE: The net ‘at’ is defined by ‘tendsto’.
 *)
Definition tendsto :
   tendsto(m:('a)metric,x) y z =
      (&0 < (dist m)(x,y) /\ (dist m)(x,y) <= (dist m)(x,z))
End

Theorem DORDER_LEMMA:
   !g:'a->'a->bool.
      dorder g ==>
        !P Q. (?n. g n n /\ (!m. g m n ==> P m)) /\
              (?n. g n n /\ (!m. g m n ==> Q m))
                  ==> (?n. g n n /\ (!m. g m n ==> P m /\ Q m))
Proof
  GEN_TAC THEN REWRITE_TAC[dorder] THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN “N1:'a” STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN “N2:'a” STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o SPECL [“N1:'a”, “N2:'a”]) THEN
  REWRITE_TAC[ASSUME “(g:'a->'a->bool) N1 N1”,ASSUME “(g:'a->'a->bool) N2 N2”] THEN
  DISCH_THEN(X_CHOOSE_THEN “n:'a” STRIP_ASSUME_TAC) THEN
  EXISTS_TAC “n:'a” THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC “m:'a” THEN DISCH_TAC THEN
  CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  FIRST_ASSUM(UNDISCH_TAC o
    assert(is_conj o snd o dest_imp o snd o dest_forall) o concl) THEN
  DISCH_THEN(MP_TAC o SPEC “m:'a”) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[]
QED

(*---------------------------------------------------------------------------*)
(* Following tactic is useful in the following proofs                        *)
(*---------------------------------------------------------------------------*)

fun DORDER_THEN tac th =
  let val findpr = snd o dest_imp o body o rand o rand o body o rand
      val (t1,t2) = case map (rand o rand o body o rand)
            (strip_conj (concl th)) of
          [t1, t2] => (t1, t2)
        | _ => raise Match
      val dog = (rator o rator o rand o rator o body) t1
      val thl = map ((uncurry X_BETA_CONV) o (I ## rand) o dest_abs) [t1,t2]
      val th1 = CONV_RULE(EXACT_CONV thl) th
      val th2 = MATCH_MP DORDER_LEMMA (ASSUME “dorder ^dog”)
      val th3 = MATCH_MP th2 th1
      val th4 = CONV_RULE(EXACT_CONV(map SYM thl)) th3 in
      tac th4 end;

(*---------------------------------------------------------------------------*)
(* Show that sequences and pointwise limits in a metric space are directed   *)
(*---------------------------------------------------------------------------*)

Theorem DORDER_NGE:
   dorder ($>= :num->num->bool)
Proof
  REWRITE_TAC[dorder, GREATER_EQ, LESS_EQ_REFL] THEN
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC(SPECL [“x:num”, “y:num”] LESS_EQ_CASES) THENL
    [EXISTS_TAC “y:num”, EXISTS_TAC “x:num”] THEN
  GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LESS_EQ_TRANS THENL
    [EXISTS_TAC “y:num”, EXISTS_TAC “x:num”] THEN
  ASM_REWRITE_TAC[]
QED

Theorem DORDER_TENDSTO:
   !m:('a)metric. !x. dorder(tendsto(m,x))
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[dorder, tendsto] THEN
  MAP_EVERY X_GEN_TAC [“u:'a”, “v:'a”] THEN
  REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN ASM_REWRITE_TAC[] THEN
  DISJ_CASES_TAC(SPECL [“(dist m)(x:'a,v)”, “(dist m)(x:'a,u)”] REAL_LE_TOTAL)
  THENL [EXISTS_TAC “v:'a”, EXISTS_TAC “u:'a”] THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN FIRST_ASSUM
    (fn th => (EXISTS_TAC o rand o concl) th THEN ASM_REWRITE_TAC[] THEN NO_TAC)
QED

(*---------------------------------------------------------------------------*)
(* Simpler characterization of limit in a metric topology                    *)
(*---------------------------------------------------------------------------*)

Theorem MTOP_TENDS :
  !d g. !x:'b->'a. !x0. (x tends x0)(mtop(d),g) <=>
     !e. &0 < e ==> ?n. g n n /\ !m. g m n ==> dist(d)(x(m),x0) < e
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[tends] THEN EQ_TAC THEN DISCH_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC “B(d)(x0:'a,e)”) THEN
    W(C SUBGOAL_THEN MP_TAC o funpow 2 (rand o rator) o snd) THENL
     [MATCH_MP_TAC BALL_NEIGH THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
    DISCH_THEN(fn th => REWRITE_TAC[th]) THEN REWRITE_TAC[ball] THEN
    BETA_TAC THEN
    GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV) [METRIC_SYM] THEN REWRITE_TAC[],
    GEN_TAC THEN REWRITE_TAC[neigh] THEN
    DISCH_THEN(X_CHOOSE_THEN “P:'a->bool” STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC “open_in(mtop(d)) (P:'a->bool)” THEN
    REWRITE_TAC[MTOP_OPEN] THEN DISCH_THEN(MP_TAC o SPEC “x0:'a”) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN “d:real” STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o SPEC “d:real”) THEN
    REWRITE_TAC[ASSUME “&0 < d”] THEN
    DISCH_THEN(X_CHOOSE_THEN “n:'b” STRIP_ASSUME_TAC) THEN
    EXISTS_TAC “n:'b” THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC “(P:'a->bool) SUBSET N” THEN
    REWRITE_TAC[SUBSET_applied] THEN DISCH_TAC THEN
    REPEAT(FIRST_ASSUM MATCH_MP_TAC) THEN
    ONCE_REWRITE_TAC[METRIC_SYM] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]
QED

(*---------------------------------------------------------------------------*)
(* Prove that a net in a metric topology cannot converge to different limits *)
(*---------------------------------------------------------------------------*)

Theorem MTOP_TENDS_UNIQ :
    !g d. dorder (g:'b->'b->bool) ==>
          (x tends x0)(mtop(d),g) /\ (x tends x1)(mtop(d),g) ==> (x0:'a = x1)
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[MTOP_TENDS] THEN
  CONV_TAC(ONCE_DEPTH_CONV AND_FORALL_CONV) THEN
  REWRITE_TAC[TAUT ‘(a ==> b) /\ (a ==> c) <=> a ==> b /\ c’] THEN
  CONV_TAC CONTRAPOS_CONV THEN DISCH_TAC THEN
  CONV_TAC NOT_FORALL_CONV THEN
  EXISTS_TAC “dist(d:('a)metric)(x0,x1) / &2” THEN
  W(C SUBGOAL_THEN ASSUME_TAC o rand o rator o rand o snd) THENL
   [REWRITE_TAC[REAL_LT_HALF1] THEN MATCH_MP_TAC METRIC_NZ THEN
    FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(DORDER_THEN MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN “N:'b” (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o SPEC “N:'b”) THEN ASM_REWRITE_TAC[] THEN
  BETA_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_ADD2) THEN
  REWRITE_TAC[REAL_HALF_DOUBLE, REAL_NOT_LT] THEN
  GEN_REWR_TAC(RAND_CONV o LAND_CONV) [METRIC_SYM] THEN
  MATCH_ACCEPT_TAC METRIC_TRIANGLE
QED

(*---------------------------------------------------------------------------*)
(* Simpler characterization of limit of a sequence in a metric topology      *)
(*---------------------------------------------------------------------------*)

val geq = Term`$>= : num->num->bool`;

Theorem SEQ_TENDS:
   !d:('a)metric. !x x0. (x tends x0)(mtop(d), ^geq) =
     !e. &0 < e ==> ?N. !n. ^geq n N ==> dist(d)(x(n),x0) < e
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[MTOP_TENDS, GREATER_EQ, LESS_EQ_REFL]
QED

(*---------------------------------------------------------------------------*)
(* And of limit of function between metric spaces                            *)
(*---------------------------------------------------------------------------*)

Theorem LIM_TENDS:
   !m1:('a)metric. !m2:('b)metric. !f x0 y0.
      limpt(mtop m1) x0 UNIV ==>
        ((f tends y0)(mtop(m2),tendsto(m1,x0)) =
          !e. &0 < e ==>
            ?d. &0 < d /\ !x. &0 < (dist m1)(x,x0) /\ (dist m1)(x,x0) <= d ==>
              (dist m2)(f(x),y0) < e)
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[MTOP_TENDS, tendsto] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  ASM_CASES_TAC “&0 < e” THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_LE_REFL] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN “z:'a” STRIP_ASSUME_TAC) THEN
    EXISTS_TAC “(dist m1)(x0:'a,z)” THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(ISPECL [“m1:('a)metric”, “x0:'a”, “x:'a”] METRIC_SYM) THEN
    ASM_REWRITE_TAC[],
    DISCH_THEN(X_CHOOSE_THEN “d:real” STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC “limpt(mtop m1) (x0:'a) UNIV” THEN
    REWRITE_TAC[MTOP_LIMPT] THEN
    DISCH_THEN(MP_TAC o SPEC “d:real”) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[UNIV_DEF] THEN
    DISCH_THEN(X_CHOOSE_THEN “y:'a” STRIP_ASSUME_TAC) THEN
    EXISTS_TAC “y:'a” THEN CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_NZ THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
    X_GEN_TAC “x:'a” THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC[METRIC_SYM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC “(dist m1)(x0:'a,y)” THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_ASSUM ACCEPT_TAC]
QED

(*---------------------------------------------------------------------------*)
(* Similar, more conventional version, is also true at a limit point         *)
(*---------------------------------------------------------------------------*)

Theorem LIM_TENDS2:
   !m1:('a)metric. !m2:('b)metric. !f x0 y0.
      limpt(mtop m1) x0 UNIV ==>
        ((f tends y0)(mtop(m2),tendsto(m1,x0)) =
          !e. &0 < e ==>
            ?d. &0 < d /\ !x. &0 < (dist m1)(x,x0) /\ (dist m1)(x,x0) < d ==>
              (dist m2)(f(x),y0) < e)
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP LIM_TENDS th]) THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN “d:real” STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC “d:real” THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[],
    EXISTS_TAC “d / &2” THEN ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
    GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC “d / &2” THEN ASM_REWRITE_TAC[REAL_LT_HALF2]]
QED

(*---------------------------------------------------------------------------*)
(* Simpler characterization of boundedness for the real line                 *)
(*---------------------------------------------------------------------------*)

Theorem MR1_BOUNDED:
   !(g:'a->'a->bool) f. bounded(mr1,g) f =
        ?k N. g N N /\ (!n. g n N ==> abs(f n) < k)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[bounded, MR1_DEF] THEN
  (CONV_TAC o LAND_CONV o RAND_CONV o ABS_CONV) SWAP_EXISTS_CONV
  THEN CONV_TAC(ONCE_DEPTH_CONV SWAP_EXISTS_CONV) THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  CONV_TAC(REDEPTH_CONV EXISTS_AND_CONV) THEN
  AP_TERM_TAC THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN “k:real” MP_TAC) THENL
   [DISCH_THEN(X_CHOOSE_TAC “x:real”) THEN
    EXISTS_TAC “abs(x) + k” THEN GEN_TAC THEN DISCH_TAC THEN
    SUBST1_TAC
      (SYM(SPECL [“(f:'a->real) n”, “x:real”] REAL_SUB_ADD)) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC “abs((f:'a->real) n - x) + abs(x)” THEN
    REWRITE_TAC[ABS_TRIANGLE] THEN
    GEN_REWR_TAC RAND_CONV  [REAL_ADD_SYM] THEN
    REWRITE_TAC[REAL_LT_RADD] THEN
    ONCE_REWRITE_TAC[ABS_SUB] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC,
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [“k:real”, “&0”] THEN
    ASM_REWRITE_TAC[REAL_SUB_LZERO, ABS_NEG]]
QED

(*---------------------------------------------------------------------------*)
(* Firstly, prove useful forms of null and bounded nets                      *)
(*---------------------------------------------------------------------------*)

Theorem NET_NULL:
   !g:'a->'a->bool. !x x0.
      (x tends x0)(mtop(mr1),g) = ((\n. x(n) - x0) tends &0)(mtop(mr1),g)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[MTOP_TENDS] THEN BETA_TAC THEN
  REWRITE_TAC[MR1_DEF, REAL_SUB_LZERO] THEN EQUAL_TAC THEN
  REWRITE_TAC[REAL_NEG_SUB]
QED

Theorem NET_CONV_BOUNDED:
   !g:'a->'a->bool. !x x0.
      (x tends x0)(mtop(mr1),g) ==> bounded(mr1,g) x
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[MTOP_TENDS, bounded] THEN
  DISCH_THEN(MP_TAC o SPEC “&1”) THEN
  REWRITE_TAC[REAL_LT, ONE, LESS_0] THEN
  REWRITE_TAC[GSYM(ONE)] THEN
  DISCH_THEN(X_CHOOSE_THEN “N:'a” STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [“&1”, “x0:real”, “N:'a”] THEN
  ASM_REWRITE_TAC[]
QED

Theorem NET_CONV_NZ:
   !g:'a->'a->bool. !x x0.
      (x tends x0)(mtop(mr1),g) /\ ~(x0 = &0) ==>
        ?N. g N N /\ (!n. g n N ==> ~(x n = &0))
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[MTOP_TENDS, bounded] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC “abs(x0)”) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[GSYM ABS_NZ] THEN
  DISCH_THEN(X_CHOOSE_THEN “N:'a” (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_TAC THEN EXISTS_TAC “N:'a” THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
  CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MR1_DEF, REAL_SUB_RZERO, REAL_LT_REFL]
QED

Theorem NET_CONV_IBOUNDED:
   !g:'a->'a->bool. !x x0.
      (x tends x0)(mtop(mr1),g) /\ ~(x0 = &0) ==>
        bounded(mr1,g) (\n. inv(x n))
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[MTOP_TENDS, MR1_BOUNDED, MR1_DEF] THEN
  BETA_TAC THEN REWRITE_TAC[ABS_NZ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC “abs(x0) / &2”) THEN
  ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
  DISCH_THEN(X_CHOOSE_THEN “N:'a” STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [“&2 / abs(x0)”, “N:'a”] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC “n:'a” THEN
  DISCH_THEN(ANTE_RES_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN “(abs(x0) / & 2) < abs(x(n:'a))” ASSUME_TAC THENL
   [SUBST1_TAC(SYM(SPECL [“abs(x0) / &2”, “abs(x0) / &2”, “abs(x(n:'a))”]
      REAL_LT_LADD)) THEN
    REWRITE_TAC[REAL_HALF_DOUBLE] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC “abs(x0 - x(n:'a)) + abs(x(n))” THEN
    ASM_REWRITE_TAC[REAL_LT_RADD] THEN
    SUBST1_TAC(SYM(AP_TERM “abs”
      (SPECL [“x0:real”, “x(n:'a):real”] REAL_SUB_ADD))) THEN
    MATCH_ACCEPT_TAC ABS_TRIANGLE, ALL_TAC] THEN
  SUBGOAL_THEN “&0 < abs(x(n:'a))” ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC “abs(x0) / &2” THEN
    ASM_REWRITE_TAC[REAL_LT_HALF1], ALL_TAC] THEN
  SUBGOAL_THEN “&2 / abs(x0) = inv(abs(x0) / &2)” SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_RINV_UNIQ THEN REWRITE_TAC[real_div] THEN
    ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
        “(a * b) * (c * d) = (d * a) * (b * c)”] THEN
    SUBGOAL_THEN “~(abs(x0) = &0) /\ ~(&2 = &0)”
      (fn th => CONJUNCTS_THEN(SUBST1_TAC o MATCH_MP REAL_MUL_LINV) th
            THEN REWRITE_TAC[REAL_MUL_LID]) THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[ABS_NZ, ABS_ABS],
      REWRITE_TAC[REAL_INJ] THEN CONV_TAC(RAND_CONV num_EQ_CONV) THEN
      REWRITE_TAC[]], ALL_TAC] THEN
  SUBGOAL_THEN “~(x(n:'a) = &0)” (SUBST1_TAC o MATCH_MP ABS_INV) THENL
   [ASM_REWRITE_TAC[ABS_NZ], ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[REAL_LT_HALF1]
QED

(*---------------------------------------------------------------------------*)
(* Now combining theorems for null nets                                      *)
(*---------------------------------------------------------------------------*)

Theorem NET_NULL_ADD:
   !g:'a->'a->bool. dorder g ==>
        !x y. (x tends &0)(mtop(mr1),g) /\ (y tends &0)(mtop(mr1),g) ==>
                ((\n. x(n) + y(n)) tends &0)(mtop(mr1),g)
Proof
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[MTOP_TENDS, MR1_DEF, REAL_SUB_LZERO, ABS_NEG] THEN
  DISCH_THEN(curry op THEN (X_GEN_TAC “e:real” THEN DISCH_TAC) o
    MP_TAC o end_itlist CONJ o map (SPEC “e / &2”) o CONJUNCTS) THEN
  ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
  DISCH_THEN(DORDER_THEN (X_CHOOSE_THEN “N:'a” STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC “N:'a” THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN ASSUME_TAC) THEN
  BETA_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC “abs(x(m:'a)) + abs(y(m:'a))” THEN
  REWRITE_TAC[ABS_TRIANGLE] THEN RULE_ASSUM_TAC BETA_RULE THEN
  GEN_REWR_TAC RAND_CONV [GSYM REAL_HALF_DOUBLE] THEN
  MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC[]
QED

Theorem NET_NULL_MUL:
   !g:'a->'a->bool. dorder g ==>
      !x y. bounded(mr1,g) x /\ (y tends &0)(mtop(mr1),g) ==>
              ((\n. x(n) * y(n)) tends &0)(mtop(mr1),g)
Proof
  GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[MR1_BOUNDED] THEN
  REWRITE_TAC[MTOP_TENDS, MR1_DEF, REAL_SUB_LZERO, ABS_NEG] THEN
  DISCH_THEN(curry op THEN (X_GEN_TAC “e:real” THEN DISCH_TAC) o MP_TAC) THEN
  CONV_TAC(LAND_CONV LEFT_AND_EXISTS_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN “k:real” MP_TAC) THEN
  DISCH_THEN(ASSUME_TAC o uncurry CONJ o (I ## SPEC “e / k”) o CONJ_PAIR) THEN
  SUBGOAL_THEN “&0 < k” ASSUME_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_THEN “N:'a”
      (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) o CONJUNCT1) THEN
    DISCH_THEN(MP_TAC o SPEC “N:'a”) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC “abs(x(N:'a))” THEN ASM_REWRITE_TAC[ABS_POS], ALL_TAC] THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_conj o concl) THEN
  SUBGOAL_THEN “&0 < e / k” ASSUME_TAC THENL
   [FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_LT_RDIV_0 th] THEN
    ASM_REWRITE_TAC[] THEN NO_TAC), ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DORDER_THEN(X_CHOOSE_THEN “N:'a” STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC “N:'a” THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN (ASSUME_TAC o BETA_RULE)) THEN
  SUBGOAL_THEN “e = k * (e / k)” SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
    DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC “&0 < &0” THEN
    REWRITE_TAC[REAL_LT_REFL], ALL_TAC] THEN BETA_TAC THEN
  REWRITE_TAC[ABS_MUL] THEN MATCH_MP_TAC REAL_LT_MUL2 THEN
  ASM_REWRITE_TAC[ABS_POS]
QED

Theorem NET_NULL_CMUL:
   !g:'a->'a->bool. !k x.
      (x tends &0)(mtop(mr1),g) ==> ((\n. k * x(n)) tends &0)(mtop(mr1),g)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[MTOP_TENDS, MR1_DEF] THEN
  BETA_TAC THEN REWRITE_TAC[REAL_SUB_LZERO, ABS_NEG] THEN
  DISCH_THEN(curry op THEN (X_GEN_TAC “e:real” THEN DISCH_TAC) o MP_TAC) THEN
  ASM_CASES_TAC “k = &0” THENL
   [DISCH_THEN(MP_TAC o SPEC “&1”) THEN
    REWRITE_TAC[REAL_LT, ONE, LESS_SUC_REFL] THEN
    DISCH_THEN(X_CHOOSE_THEN “N:'a” STRIP_ASSUME_TAC) THEN
    EXISTS_TAC “N:'a” THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO, abs, REAL_LE_REFL],
    DISCH_THEN(MP_TAC o SPEC “e / abs(k)”) THEN
    SUBGOAL_THEN “&0 < e / abs(k)” ASSUME_TAC THENL
     [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_INV_POS THEN
      ASM_REWRITE_TAC[GSYM ABS_NZ], ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN “N:'a” STRIP_ASSUME_TAC) THEN
    EXISTS_TAC “N:'a” THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN “e = abs(k) * (e / abs(k))” SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
      ASM_REWRITE_TAC[ABS_ZERO], ALL_TAC] THEN
    REWRITE_TAC[ABS_MUL] THEN
    SUBGOAL_THEN “&0 < abs k” (fn th => REWRITE_TAC[MATCH_MP REAL_LT_LMUL th])
    THEN ASM_REWRITE_TAC[GSYM ABS_NZ]]
QED

(*---------------------------------------------------------------------------*)
(* Now real arithmetic theorems for convergent nets                          *)
(*---------------------------------------------------------------------------*)

Theorem NET_ADD:
   !g:'a->'a->bool. dorder g ==>
      !x x0 y y0. (x tends x0)(mtop(mr1),g) /\ (y tends y0)(mtop(mr1),g) ==>
                      ((\n. x(n) + y(n)) tends (x0 + y0))(mtop(mr1),g)
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[NET_NULL] THEN
  DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th o MATCH_MP NET_NULL_ADD))
  THEN MATCH_MP_TAC(TAUT ‘(a = b) ==> a ==> b’) THEN EQUAL_TAC THEN
  BETA_TAC THEN REWRITE_TAC[real_sub, REAL_NEG_ADD] THEN
  CONV_TAC(AC_CONV(REAL_ADD_ASSOC,REAL_ADD_SYM))
QED

Theorem NET_NEG:
   !g:'a->'a->bool. dorder g ==>
        (!x x0. (x tends x0)(mtop(mr1),g) =
                  ((\n. ~(x n)) tends ~x0)(mtop(mr1),g))
Proof
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[MTOP_TENDS, MR1_DEF] THEN BETA_TAC THEN
  REWRITE_TAC[REAL_SUB_NEG2] THEN
  GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ABS_SUB]
  THEN REFL_TAC
QED

Theorem NET_SUB:
   !g:'a->'a->bool. dorder g ==>
      !x x0 y y0. (x tends x0)(mtop(mr1),g) /\ (y tends y0)(mtop(mr1),g) ==>
                      ((\n. x(n) - y(n)) tends (x0 - y0))(mtop(mr1),g)
Proof
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[real_sub] THEN
  CONV_TAC(EXACT_CONV[X_BETA_CONV “n:'a” “-(y (n:'a))”]) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP NET_ADD) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fn th => ONCE_REWRITE_TAC[GSYM(MATCH_MP NET_NEG th)]) THEN
  ASM_REWRITE_TAC[]
QED

Theorem NET_MUL:
   !g:'a->'a->bool. dorder g ==>
        !x y x0 y0. (x tends x0)(mtop(mr1),g) /\ (y tends y0)(mtop(mr1),g) ==>
              ((\n. x(n) * y(n)) tends (x0 * y0))(mtop(mr1),g)
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[NET_NULL] THEN
  DISCH_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN “!a b c d. (a * b) - (c * d) =
                             (a * (b - d)) + ((a - c) * d)”
  (fn th => ONCE_REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[real_sub, REAL_LDISTRIB, REAL_RDISTRIB, GSYM REAL_ADD_ASSOC]
    THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL, GSYM REAL_NEG_RMUL] THEN
    REWRITE_TAC[REAL_ADD_ASSOC, REAL_ADD_LINV, REAL_ADD_LID], ALL_TAC] THEN
  CONV_TAC(EXACT_CONV[X_BETA_CONV “n:'a” “x(n:'a) * (y(n) - y0)”]) THEN
  CONV_TAC(EXACT_CONV[X_BETA_CONV “n:'a” “(x(n:'a) - x0) * y0”]) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP NET_NULL_ADD) THEN
  GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
  (CONV_TAC o EXACT_CONV o map (X_BETA_CONV “n:'a”))
   [“y(n:'a) - y0”, “x(n:'a) - x0”] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP NET_NULL_MUL) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NET_CONV_BOUNDED THEN
    EXISTS_TAC “x0:real” THEN ONCE_REWRITE_TAC[NET_NULL] THEN
    ASM_REWRITE_TAC[],
    MATCH_MP_TAC NET_NULL_CMUL THEN ASM_REWRITE_TAC[]]
QED

Theorem NET_INV:
   !g:'a->'a->bool. dorder g ==>
        !x x0. (x tends x0)(mtop(mr1),g) /\ ~(x0 = &0) ==>
                   ((\n. inv(x(n))) tends inv x0)(mtop(mr1),g)
Proof
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fn th => STRIP_ASSUME_TAC th THEN
    MP_TAC(CONJ (MATCH_MP NET_CONV_IBOUNDED th)
                    (MATCH_MP NET_CONV_NZ th))) THEN
  REWRITE_TAC[MR1_BOUNDED] THEN
  CONV_TAC(ONCE_DEPTH_CONV LEFT_AND_EXISTS_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN “k:real” MP_TAC) THEN
  DISCH_THEN(DORDER_THEN MP_TAC) THEN BETA_TAC THEN
  DISCH_THEN(MP_TAC o C CONJ(ASSUME “(x tends x0)(mtop mr1,(g:'a->'a->bool))”)) THEN
  ONCE_REWRITE_TAC[NET_NULL] THEN
  REWRITE_TAC[MTOP_TENDS, MR1_DEF, REAL_SUB_LZERO, ABS_NEG] THEN BETA_TAC
  THEN DISCH_THEN(curry op THEN (X_GEN_TAC “e:real” THEN DISCH_TAC) o MP_TAC) THEN
  CONV_TAC(ONCE_DEPTH_CONV RIGHT_AND_FORALL_CONV) THEN
  DISCH_THEN(ASSUME_TAC o SPEC “e * (abs(x0) * (inv k))”) THEN
  SUBGOAL_THEN “&0 < k” ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1) THEN
    DISCH_THEN(X_CHOOSE_THEN “N:'a” (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(MP_TAC o SPEC “N:'a”) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC “abs(inv(x(N:'a)))” THEN
    ASM_REWRITE_TAC[ABS_POS], ALL_TAC] THEN
  SUBGOAL_THEN “&0 < e * (abs(x0) * inv k)” ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[GSYM ABS_NZ] THEN
    MATCH_MP_TAC REAL_INV_POS THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_conj o concl) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(DORDER_THEN MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN “N:'a” (CONJUNCTS_THEN ASSUME_TAC)) THEN
  EXISTS_TAC “N:'a” THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC “n:'a” THEN DISCH_THEN(ANTE_RES_THEN STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC BETA_RULE THEN POP_ASSUM_LIST(MAP_EVERY STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN “inv(x n) - inv x0 =
                inv(x n) * (inv x0 * (x0 - x(n:'a)))” SUBST1_TAC THENL
   [REWRITE_TAC[REAL_SUB_LDISTRIB] THEN
    REWRITE_TAC[MATCH_MP REAL_MUL_LINV (ASSUME “~(x0 = &0)”)] THEN
    REWRITE_TAC[REAL_MUL_RID] THEN REPEAT AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC[MATCH_MP REAL_MUL_RINV (ASSUME “~(x(n:'a) = &0)”)] THEN
    REWRITE_TAC[REAL_MUL_RID], ALL_TAC] THEN
  REWRITE_TAC[ABS_MUL] THEN ONCE_REWRITE_TAC[ABS_SUB] THEN
  SUBGOAL_THEN “e = e * ((abs(inv x0) * abs(x0)) * (inv k * k))”
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM ABS_MUL] THEN
    REWRITE_TAC[MATCH_MP REAL_MUL_LINV (ASSUME “~(x0 = &0)”)] THEN
    REWRITE_TAC[MATCH_MP REAL_MUL_LINV
      (GSYM(MATCH_MP REAL_LT_IMP_NE (ASSUME “&0 < k”)))] THEN
    REWRITE_TAC[REAL_MUL_RID] THEN
    REWRITE_TAC[abs, REAL_LE, LESS_OR_EQ, ONE, LESS_SUC_REFL] THEN
    REWRITE_TAC[SYM ONE, REAL_MUL_RID], ALL_TAC] THEN
  ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
    “a * ((b * c) * (d * e)) = e * (b * (a * (c * d)))”] THEN
  REWRITE_TAC[GSYM ABS_MUL] THEN
  MATCH_MP_TAC ABS_LT_MUL2 THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ABS_MUL] THEN SUBGOAL_THEN “&0 < abs(inv x0)”
    (fn th => ASM_REWRITE_TAC[MATCH_MP REAL_LT_LMUL th]) THEN
  REWRITE_TAC[GSYM ABS_NZ] THEN
  MATCH_MP_TAC REAL_INV_NZ THEN ASM_REWRITE_TAC[]
QED

Theorem NET_DIV:
   !g:'a->'a->bool. dorder g ==>
      !x x0 y y0. (x tends x0)(mtop(mr1),g) /\
                  (y tends y0)(mtop(mr1),g) /\ ~(y0 = &0) ==>
                      ((\n. x(n) / y(n)) tends (x0 / y0))(mtop(mr1),g)
Proof
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[real_div] THEN
  CONV_TAC(EXACT_CONV[X_BETA_CONV “n:'a” “inv(y(n:'a))”]) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP NET_MUL) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP NET_INV) THEN
  ASM_REWRITE_TAC[]
QED

Theorem NET_ABS:
   !g x x0. (x tends x0)(mtop(mr1),g) ==>
               ((\n:'a. abs(x n)) tends abs(x0))(mtop(mr1),g)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[MTOP_TENDS] THEN
  DISCH_TAC THEN X_GEN_TAC “e:real” THEN
  DISCH_THEN(fn th => POP_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  DISCH_THEN(X_CHOOSE_THEN “N:'a” STRIP_ASSUME_TAC) THEN
  EXISTS_TAC “N:'a” THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC “n:'a” THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC “dist(mr1)(x(n:'a),x0)” THEN CONJ_TAC THENL
   [REWRITE_TAC[MR1_DEF, ABS_SUB_ABS],
    FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]
QED

(*---------------------------------------------------------------------------*)
(* Comparison between limits                                                 *)
(*---------------------------------------------------------------------------*)

Theorem NET_LE:
   !g:'a->'a->bool. dorder g ==>
      !x x0 y y0. (x tends x0)(mtop(mr1),g) /\
                  (y tends y0)(mtop(mr1),g) /\
                  (?N. g N N /\ !n. g n N ==> x(n) <= y(n))
                        ==> x0 <= y0
Proof
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  GEN_REWR_TAC I [TAUT ‘a = ~~a:bool’] THEN
  PURE_ONCE_REWRITE_TAC[REAL_NOT_LE] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN DISCH_TAC THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_conj o concl) THEN
  REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[MTOP_TENDS] THEN
  DISCH_THEN(MP_TAC o end_itlist CONJ o
    map (SPEC “(x0 - y0) / &2”) o CONJUNCTS) THEN
  ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
  DISCH_THEN(DORDER_THEN MP_TAC) THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_exists o concl) THEN
  DISCH_THEN(fn th1 => DISCH_THEN (fn th2 => MP_TAC(CONJ th1 th2))) THEN
  DISCH_THEN(DORDER_THEN MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN “N:'a” (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  BETA_TAC THEN DISCH_THEN(MP_TAC o SPEC “N:'a”) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MR1_DEF] THEN ONCE_REWRITE_TAC[ABS_SUB] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[REAL_NOT_LE] THEN MATCH_MP_TAC ABS_BETWEEN2 THEN
  MAP_EVERY EXISTS_TAC [“y0:real”, “x0:real”] THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  FIRST_ASSUM ACCEPT_TAC
QED

(* ------------------------------------------------------------------------- *)
(*  Net As Type                                                              *)
(* ------------------------------------------------------------------------- *)

Definition isnet :
   isnet g <=> !x y. (!z. g z x ==> g z y) \/ (!z. g z y ==> g z x)
End

val net_tydef = new_type_definition
 ("net",
  prove (``?(g:'a->'a->bool). isnet g``,
        EXISTS_TAC ``\x:'a y:'a. F`` THEN REWRITE_TAC[isnet]));

val net_ty_bij = define_new_type_bijections
    {name="net_tybij",
     ABS="mk_net", REP="netord",tyax=net_tydef};

Theorem net_tybij[allow_rebind]:
  (!a. mk_net (netord a) = a) /\
  (!r. (!x y. (!z. r z x ==> r z y) \/ (!z. r z y ==> r z x)) <=>
       (netord (mk_net r) = r))
Proof
  SIMP_TAC std_ss [net_ty_bij, GSYM isnet]
QED

Theorem NET :
   !n x y. (!z. netord n z x ==> netord n z y) \/
           (!z. netord n z y ==> netord n z x)
Proof
   REWRITE_TAC[net_tybij, ETA_AX]
QED

Theorem OLDNET :
    !n x y. netord n x x /\ netord n y y
           ==> ?z. netord n z z /\
                   !w. netord n w z ==> netord n w x /\ netord n w y
Proof
  MESON_TAC[NET]
QED

Theorem NET_DILEMMA :
   !net. (?a. (?x. netord net x a) /\ (!x. netord net x a ==> P x)) /\
         (?b. (?x. netord net x b) /\ (!x. netord net x b ==> Q x))
     ==> ?c. (?x. netord net x c) /\ (!x. netord net x c ==> P x /\ Q x)
Proof
  MESON_TAC[NET]
QED

(* NOTE: It seems that purpose of “g x x” in dorder for “at a”, is to make
   sure ‘x <> a’, or 0 < mdist m (x,a).
 *)
Theorem DORDER_NET :
    !net. dorder (netord net)
Proof
    RW_TAC std_ss [dorder, OLDNET]
QED

(* ------------------------------------------------------------------------- *)
(* Common nets and the "within" modifier for nets.                           *)
(* ------------------------------------------------------------------------- *)

val _ = set_fixity "within" (Infix(NONASSOC, 450));
val _ = set_fixity "in_direction" (Infix(NONASSOC, 450));

(* HOL-Light: (atpointof top a) = mk_net({u | open_in top u /\ a IN u},{a})

   NOTE: HOL-Light's “atpointof” takes a (general) topology, while here HOL4
   takes a metric (therefore only works for metrizable topology).
 *)
Definition atpointof_def[nocompute]:
    atpointof m a = mk_net (tendsto (m,a))
End

(* HOL-Light: at a = atpointof euclidean a *)
Definition at_DEF :
    at z = atpointof mr1 z
End

(* The previous "definition" now (again) becomes a theorem. *)
Theorem at_def :
    !z. at z = mk_net (tendsto (mr1,z))
Proof
    RW_TAC std_ss [at_DEF, atpointof_def]
QED

Theorem atpointof :
    !m a. atpointof m a =
          mk_net (\x y. 0 < mdist m (x,a) /\ mdist m (x,a) <= mdist m (y,a))
Proof
    RW_TAC std_ss [atpointof_def]
 >> AP_TERM_TAC
 >> RW_TAC std_ss [FUN_EQ_THM, tendsto]
 >> PROVE_TAC [METRIC_SYM]
QED

(* |- !a. at a = mk_net (\x y. 0 < dist (x,a) /\ dist (x,a) <= dist (y,a)) *)
Theorem at = atpointof |> ISPEC “mr1”
                       |> REWRITE_RULE [GSYM at_DEF, GSYM dist_def]

(* HOL-Light: at_infinity = mk_net({{x | b <= norm x} | b IN (:real)},{}) *)
Definition at_infinity[nocompute]:
  at_infinity = mk_net(\x y. abs(x) >= abs(y))
End

(* HOL-Light: at_posinfinity = mk_net({{x | a <= x} | a IN (:real)},{}) *)
Definition at_posinfinity[nocompute]:
  at_posinfinity = mk_net(\x y:real. x >= y)
End

(* HOL-Light: at_neginfinity = mk_net({{x | x <= a} | a IN (:real)},{}) *)
Definition at_neginfinity[nocompute]:
  at_neginfinity = mk_net(\x y:real. x <= y)
End

(* HOL-Light: sequentially = mk_net({from n | n IN (:num)},{}) *)
Definition sequentially[nocompute]:
  sequentially = mk_net(\m:num n. m >= n)
End

(* NOTE: “within” only requires “x IN s” (next step) but not for “y” *)
Definition within[nocompute]:
  (net within s) = mk_net(\x y. netord net x y /\ x IN s)
End

Definition in_direction[nocompute]:
  (a in_direction v) = ((at a) within {b | ?c. &0 <= c /\ (b - a = c * v)})
End

(* ------------------------------------------------------------------------- *)
(* Prove that they are all nets.                                             *)
(* ------------------------------------------------------------------------- *)

fun NET_PROVE_TAC [def] =
  SIMP_TAC std_ss [GSYM FUN_EQ_THM, def] THEN
  REWRITE_TAC [ETA_AX] THEN
  ASM_SIMP_TAC std_ss [GSYM(CONJUNCT2 net_tybij)];

(* NOTE: Most of the time, user only need to use this theorem instead of the
   definition(s) of “atpointof”.
 *)
Theorem ATPOINTOF :
   !m a x y.
      netord(atpointof m a) x y <=>
      0 < mdist m (x,a) /\ mdist m (x,a) <= mdist m (y,a)
Proof
  NTAC 2 GEN_TAC THEN NET_PROVE_TAC[atpointof] THEN
  METIS_TAC[REAL_LE_TOTAL, REAL_LE_REFL, REAL_LE_TRANS, REAL_LET_TRANS]
QED

(* |- !a x y.
        netord (at a) x y <=> 0 < dist (x,a) /\ dist (x,a) <= dist (y,a)
 *)
Theorem AT = ATPOINTOF |> ISPEC “mr1”
                       |> REWRITE_RULE [GSYM at_DEF, GSYM dist_def]

Theorem tendsto_alt_atpointof :
    !m a. tendsto (m,a) = netord (atpointof m a)
Proof
    rw [FUN_EQ_THM, tendsto, ATPOINTOF]
 >> METIS_TAC [MDIST_SYM]
QED

(* Connection between HOL4's “tendsto” and HOL-Light's “at”, cf. [at_def]

   |- !a. tendsto (mr1,a) = netord (at a)
 *)
Theorem tendsto_mr1 = tendsto_alt_atpointof |> ISPEC “mr1”
                                            |> REWRITE_RULE [GSYM at_DEF]

Theorem AT_INFINITY:
   !x y. netord at_infinity x y <=> abs(x) >= abs(y)
Proof
  NET_PROVE_TAC[at_infinity] THEN
  REWRITE_TAC[real_ge, REAL_LE_REFL] THEN
  MESON_TAC[REAL_LE_TOTAL, REAL_LE_REFL, REAL_LE_TRANS]
QED

Theorem AT_POSINFINITY:
   !x y. netord at_posinfinity x y <=> x >= y
Proof
  NET_PROVE_TAC[at_posinfinity] THEN
  REWRITE_TAC[real_ge, REAL_LE_REFL] THEN
  MESON_TAC[REAL_LE_TOTAL, REAL_LE_REFL, REAL_LE_TRANS]
QED

Theorem AT_NEGINFINITY:
   !x y. netord at_neginfinity x y <=> x <= y
Proof
  NET_PROVE_TAC[at_neginfinity] THEN
  REWRITE_TAC[real_ge, REAL_LE_REFL] THEN
  MESON_TAC[REAL_LE_TOTAL, REAL_LE_REFL, REAL_LE_TRANS]
QED

Theorem SEQUENTIALLY:
   !m n. netord sequentially m n <=> m >= n
Proof
  NET_PROVE_TAC[sequentially] THEN REWRITE_TAC[GREATER_EQ, LESS_EQ_REFL] THEN
  MESON_TAC[LESS_EQ_CASES, LESS_EQ_REFL, LESS_EQ_TRANS]
QED

Theorem WITHIN:
   !n s x y. netord(n within s) x y <=> netord n x y /\ x IN s
Proof
  GEN_TAC THEN GEN_TAC THEN SIMP_TAC std_ss [within, GSYM FUN_EQ_THM] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 net_tybij), ETA_AX] THEN
  METIS_TAC[NET]
QED

Theorem IN_DIRECTION:
   !a v x y. netord(a in_direction v) x y <=>
                &0 < dist(x,a) /\ dist(x,a) <= dist(y,a) /\
                 ?c. &0 <= c /\ (x - a = c * v)
Proof
  SIMP_TAC std_ss [WITHIN, AT, in_direction, GSPECIFICATION] THEN METIS_TAC []
QED

Theorem NET_WITHIN_UNIV :
    !net. (net within UNIV) = net
Proof
    rw [within]
 >> ‘(\x y. netord net x y) = netord net’ by rw [FUN_EQ_THM]
 >> simp [net_tybij]
QED

Theorem WITHIN_UNIV :
    !x. (at x within UNIV) = at x
Proof
    REWRITE_TAC [NET_WITHIN_UNIV]
QED

Theorem WITHIN_WITHIN:
   !net s t. ((net within s) within t) = (net within (s INTER t))
Proof
  ONCE_REWRITE_TAC[within] THEN
  REWRITE_TAC[WITHIN, IN_INTER, GSYM CONJ_ASSOC]
QED

(* ------------------------------------------------------------------------- *)
(* netfilter (compatible with HOL-Light)                                     *)
(* ------------------------------------------------------------------------- *)

Definition netfilter_def :
    netfilter net = {{y | netord net y x} | x | T}
End

Theorem NETFILTER_AT_POSINFINITY :
    netfilter at_posinfinity = {{x | a <= x} | a IN univ(:real)}
Proof
    simp [netfilter_def, AT_POSINFINITY, real_ge]
QED

Theorem NETFILTER_AT_NEGINFINITY :
    netfilter at_neginfinity = {{x | x <= a} | a IN univ(:real)}
Proof
    simp [netfilter_def, AT_NEGINFINITY]
QED

Theorem NETFILTER_AT_INFINITY :
    netfilter at_infinity = {{x | b <= abs x} | b IN univ(:real)}
Proof
    simp [netfilter_def, AT_INFINITY, real_ge]
 >> rw [Once EXTENSION]
 >> EQ_TAC >> rw []
 >- (Q.EXISTS_TAC ‘abs x'’ >> REFL_TAC)
 >> Cases_on ‘0 <= b’
 >- (Q.EXISTS_TAC ‘abs b’ >> simp [ABS_REDUCE])
 >> fs [REAL_NOT_LE]
 >> Know ‘!x. b <= abs x <=> 0 <= abs x’
 >- (Q.X_GEN_TAC ‘x’ \\
     EQ_TAC >> rw [] \\
     Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘0’ >> simp [ABS_POS, REAL_LT_IMP_LE])
 >> Rewr'
 >> Q.EXISTS_TAC ‘0’ >> simp [ABS_0]
QED

Theorem NETFILTER_SEQUENTIALLY :
    netfilter sequentially = {from n | n IN univ(:num)}
Proof
    simp [netfilter_def, SEQUENTIALLY, GREATER_EQ, from_def]
QED

Theorem NETFILTER_ATPOINTOF :
    !m a. netfilter (atpointof m a) =
            {{y | y <> a /\ dist m (y,a) <= dist m (x,a)} | x | T}
Proof
    simp [netfilter_def, ATPOINTOF, MDIST_POS_EQ]
QED

(* |- !a. netfilter (at a) =
          {{y | y <> a /\ dist (y,a) <= dist (x,a)} | x | T}
 *)
Theorem NETFILTER_AT =
        NETFILTER_ATPOINTOF |> ISPEC “mr1”
                            |> REWRITE_RULE [GSYM dist_def, GSYM at_DEF]

(* NOTE: This theorem is HOL-Light's WITHIN *)
Theorem NETFILTER_WITHIN :
    !net s. netfilter (net within s) = netfilter net relative_to s
Proof
    rw [netfilter_def, WITHIN, RELATIVE_TO]
 >> rw [Once EXTENSION]
 >> EQ_TAC >> rw []
 >- (Q.EXISTS_TAC ‘{y | netord net y x'}’ \\
     reverse CONJ_TAC >- (Q.EXISTS_TAC ‘x'’ >> REFL_TAC) \\
     rw [Once EXTENSION] >> PROVE_TAC [])
 >> Q.EXISTS_TAC ‘x'’
 >> rw [Once EXTENSION]
 >> PROVE_TAC []
QED

(* ------------------------------------------------------------------------- *)
(* It's also sometimes useful to extract the limit point from the net.       *)
(* ------------------------------------------------------------------------- *)

Definition netlimit :
    netlimit net = @a. !x. ~(netord net x a)
End

Theorem NETLIMIT_ATPOINTOF :
    !m a. netlimit(atpointof m a) = a
Proof
    RW_TAC std_ss [netlimit, ATPOINTOF]
 >> SELECT_ELIM_TAC
 >> CONJ_TAC
 >- (Q.EXISTS_TAC ‘a’ \\
     rw [MDIST_REFL, REAL_NOT_LE])
 >> rw [REAL_NOT_LE, REAL_NOT_LT]
 >> CCONTR_TAC
 >> Q.PAT_X_ASSUM ‘!x. P’ (MP_TAC o Q.SPEC ‘x’)
 >> simp [REAL_NOT_LE]
 >> rw [REAL_LT_LE, METRIC_NZ]
QED

(* |- !a. netlimit (at a) = a *)
Theorem NETLIMIT_AT = NETLIMIT_ATPOINTOF |> ISPEC “mr1”
                   |> REWRITE_RULE [GSYM at_DEF]

(* NOTE: This definition is compatible with HOL-Light *)
Definition netlimits_def :
    netlimits net = {a | !x. ~(netord net x a)}
End

Theorem NETLIMITS_ATPOINTOF :
    !m a. netlimits (atpointof m a) = {a}
Proof
    rw [netlimits_def, ATPOINTOF, MDIST_POS_EQ, REAL_NOT_LE]
 >> rw [Once EXTENSION]
 >> reverse EQ_TAC >- rw [MDIST_REFL, MDIST_POS_EQ]
 >> rpt STRIP_TAC
 >> CCONTR_TAC
 >> Q.PAT_X_ASSUM ‘!x. P’ (MP_TAC o Q.SPEC ‘x’) >> simp []
QED

(* |- !a. netlimits (at a) = {a} *)
Theorem NETLIMITS_AT = NETLIMITS_ATPOINTOF |> ISPEC “mr1”
                    |> REWRITE_RULE [GSYM at_DEF]

Theorem NETLIMITS_SEQUENTIALLY :
    netlimits sequentially = {}
Proof
    rw [Once EXTENSION, NOT_IN_EMPTY, netlimits_def, SEQUENTIALLY, GREATER_EQ]
 >> Q.EXISTS_TAC ‘x’ >> simp []
QED

Theorem NETLIMITS_AT_POSINFINITY :
    netlimits at_posinfinity = {}
Proof
    rw [Once EXTENSION, NOT_IN_EMPTY, netlimits_def, AT_POSINFINITY, real_ge]
 >> Q.EXISTS_TAC ‘x’ >> simp []
QED

Theorem NETLIMITS_AT_NEGINFINITY :
    netlimits at_neginfinity = {}
Proof
    rw [Once EXTENSION, NOT_IN_EMPTY, netlimits_def, AT_NEGINFINITY]
 >> Q.EXISTS_TAC ‘x’ >> simp []
QED

Theorem NETLIMITS_AT_INFINITY :
    netlimits at_infinity = {}
Proof
    rw [Once EXTENSION, NOT_IN_EMPTY, netlimits_def, AT_INFINITY, real_ge]
 >> Q.EXISTS_TAC ‘x’ >> simp []
QED

(* ------------------------------------------------------------------------- *)
(* Some property holds "sufficiently close" to the limit point.              *)
(* ------------------------------------------------------------------------- *)
(* Identify trivial limits, where we can't approach arbitrarily closely.     *)
(* ------------------------------------------------------------------------- *)

(* old (existing) definitions diverged from HOL-Light *)
Definition trivial_limit :
    trivial_limit net <=>
      (!(a:'a) b. a = b) \/
      ?(a:'a) b. ~(a = b) /\ !x. ~(netord(net) x a) /\ ~(netord(net) x b)
End

Definition eventually :
    eventually p net <=>
      trivial_limit net \/
      ?y. (?x. netord net x y) /\ (!x. netord net x y ==> p x)
End

(* new definitions (compatible with HOL-Light)
Definition eventually_def :
    eventually (P :'a -> bool) net <=>
      netfilter net = {} \/
      ?u. u IN netfilter net /\
            !x. x IN u DIFF netlimits net ==> P x
End

Definition trivial_limit_def :
    trivial_limit net = eventually (\x. F) net
End
 *)

(* ------------------------------------------------------------------------- *)

Theorem NONTRIVIAL_LIMIT_WITHIN :
    !net s. trivial_limit net ==> trivial_limit(net within s)
Proof
    REWRITE_TAC[trivial_limit, WITHIN] THEN MESON_TAC[]
QED

Theorem TRIVIAL_LIMIT_AT_INFINITY :
    ~(trivial_limit at_infinity)
Proof
  REWRITE_TAC[trivial_limit, AT_INFINITY, real_ge] THEN
  MESON_TAC[REAL_LE_REFL, REAL_CHOOSE_SIZE, REAL_LT_01, REAL_LT_LE]
QED

Theorem TRIVIAL_LIMIT_AT_POSINFINITY :
    ~(trivial_limit at_posinfinity)
Proof
  REWRITE_TAC[trivial_limit, AT_POSINFINITY, DE_MORGAN_THM] THEN
  CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o SPECL [``&0:real``, ``&1:real``]) THEN REAL_ARITH_TAC,
    ALL_TAC] THEN
  REWRITE_TAC[DE_MORGAN_THM, NOT_EXISTS_THM, real_ge, REAL_NOT_LE] THEN
  MESON_TAC[REAL_LT_TOTAL, REAL_LT_ANTISYM]
QED

Theorem TRIVIAL_LIMIT_AT_NEGINFINITY :
    ~(trivial_limit at_neginfinity)
Proof
  REWRITE_TAC[trivial_limit, AT_NEGINFINITY, DE_MORGAN_THM] THEN
  CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o SPECL [``&0:real``, ``&1:real``]) THEN REAL_ARITH_TAC,
    ALL_TAC] THEN
  REWRITE_TAC[DE_MORGAN_THM, NOT_EXISTS_THM, real_ge, REAL_NOT_LE] THEN
  MESON_TAC[REAL_LT_TOTAL, REAL_LT_ANTISYM]
QED

Theorem TRIVIAL_LIMIT_SEQUENTIALLY :
    ~(trivial_limit sequentially)
Proof
  REWRITE_TAC[trivial_limit, SEQUENTIALLY] THEN
  MESON_TAC[GREATER_EQ, LESS_EQ_REFL, SUC_NOT]
QED

Theorem EVENTUALLY_FALSE :
    !net. eventually (\x. F) net <=> trivial_limit net
Proof
  REWRITE_TAC[eventually] THEN MESON_TAC[]
QED

Theorem EVENTUALLY_TRUE :
    !net. eventually (\x. T) net <=> T
Proof
  REWRITE_TAC[eventually, trivial_limit] THEN MESON_TAC[]
QED

Theorem EVENTUALLY_HAPPENS :
    !net p. eventually p net ==> trivial_limit net \/ ?x. p x
Proof
  REWRITE_TAC[eventually] THEN MESON_TAC[]
QED

Theorem NOT_EVENTUALLY :
    !net p. (!x. ~(p x)) /\ ~(trivial_limit net) ==> ~(eventually p net)
Proof
  REWRITE_TAC[eventually] THEN MESON_TAC[]
QED

Theorem ALWAYS_EVENTUALLY :
    !net p. (!x. p x) ==> eventually p net
Proof
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[eventually, trivial_limit] THEN
  MESON_TAC[]
QED

Theorem EVENTUALLY_SEQUENTIALLY :
    !p. eventually p sequentially <=> ?N. !n. N <= n ==> p n
Proof
  REWRITE_TAC[eventually, SEQUENTIALLY, GREATER_EQ, LESS_EQ_REFL,
    TRIVIAL_LIMIT_SEQUENTIALLY] THEN  MESON_TAC[LESS_EQ_REFL]
QED

Theorem EVENTUALLY_AT_INFINITY :
    !p. eventually p at_infinity <=> ?b. !x. abs(x) >= b ==> p x
Proof
  SIMP_TAC std_ss [eventually, AT_INFINITY, TRIVIAL_LIMIT_AT_INFINITY] THEN
  REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC[REAL_LE_REFL], ALL_TAC] THEN
  MESON_TAC[real_ge, REAL_LE_REFL, REAL_CHOOSE_SIZE,
    REAL_ARITH ``&0 <= b:real \/ (!x. x >= &0 ==> x >= b)``]
QED

Theorem EVENTUALLY_AT_POSINFINITY :
    !p. eventually p at_posinfinity <=> ?b. !x. x >= b ==> p x
Proof
  REWRITE_TAC[eventually, TRIVIAL_LIMIT_AT_POSINFINITY, AT_POSINFINITY] THEN
  MESON_TAC[REAL_ARITH ``x >= x``]
QED

Theorem EVENTUALLY_AT_NEGINFINITY :
    !p. eventually p at_neginfinity <=> ?b. !x. x <= b ==> p x
Proof
  REWRITE_TAC[eventually, TRIVIAL_LIMIT_AT_NEGINFINITY, AT_NEGINFINITY] THEN
  MESON_TAC[REAL_LE_REFL]
QED

Theorem EVENTUALLY_AT_INFINITY_POS :
    !p:real->bool.
        eventually p at_infinity <=> ?b. &0 < b /\ !x. abs x >= b ==> p x
Proof
  GEN_TAC THEN REWRITE_TAC[EVENTUALLY_AT_INFINITY, real_ge] THEN
  MESON_TAC[REAL_ARITH ``&0 < abs b + &1 /\ (abs b + &1 <= x ==> b <= x:real)``]
QED

(* ------------------------------------------------------------------------- *)
(* Combining theorems for "eventually". *)
(* ------------------------------------------------------------------------- *)

Theorem EVENTUALLY_AND :
  !net:('a net) p q.
   eventually (\x. p x /\ q x) net <=>
   eventually p net /\ eventually q net
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[eventually] THEN
  ASM_CASES_TAC ``trivial_limit(net:('a net))`` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THEN SIMP_TAC std_ss [NET_DILEMMA] THENL [MESON_TAC [], ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC NET_DILEMMA THEN METIS_TAC []
QED

Theorem EVENTUALLY_MONO :
  !net:('a net) p q.
  (!x. p x ==> q x) /\ eventually p net
    ==> eventually q net
Proof
  REWRITE_TAC[eventually] THEN MESON_TAC[]
QED

Theorem EVENTUALLY_MP :
  !net:('a net) p q.
  eventually (\x. p x ==> q x) net /\ eventually p net
  ==> eventually q net
Proof
  REWRITE_TAC[GSYM EVENTUALLY_AND] THEN
  REWRITE_TAC[eventually] THEN MESON_TAC[]
QED

Theorem EVENTUALLY_FORALL :
  !net:('a net) p s:'b->bool.
  FINITE s /\ ~(s = {})
  ==> (eventually (\x. !a. a IN s ==> p a x) net <=>
   !a. a IN s ==> eventually (p a) net)
Proof
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[GSYM AND_IMP_INTRO] THEN
  KNOW_TAC ``!s:'b->bool. (s <> ({} :'b -> bool) ==>
   (eventually (\(x :'a). !(a :'b). a IN s ==> (p :'b -> 'a -> bool) a x)
   (net :'a net) <=> !(a :'b). a IN s ==> eventually (p a) net)) =
             (\s. s <> ({} :'b -> bool) ==>
   (eventually (\(x :'a). !(a :'b). a IN s ==> (p :'b -> 'a -> bool) a x)
   (net :'a net) <=> !(a :'b). a IN s ==> eventually (p a) net)) s`` THENL
  [FULL_SIMP_TAC std_ss [], ALL_TAC] THEN DISC_RW_KILL THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC std_ss [FORALL_IN_INSERT, EVENTUALLY_AND, ETA_AX] THEN
  SIMP_TAC std_ss [GSYM RIGHT_FORALL_IMP_THM] THEN
  MAP_EVERY X_GEN_TAC [``t:'b->bool``, ``b:'b``] THEN
  ASM_CASES_TAC ``t:'b->bool = {}`` THEN
  ASM_SIMP_TAC std_ss [NOT_IN_EMPTY, EVENTUALLY_TRUE] THEN METIS_TAC []
QED

Theorem FORALL_EVENTUALLY :
  !net:('a net) p s:'b->bool.
   FINITE s /\ ~(s = {})
   ==> ((!a. a IN s ==> eventually (p a) net) <=>
   eventually (\x. !a. a IN s ==> p a x) net)
Proof
  SIMP_TAC std_ss [EVENTUALLY_FORALL]
QED

(* NOTE: This theorem is trivial (by NET_WITHIN_UNIV and MSPACE) in HOL4.
   The original HOL-Light version is:

   |- !top a:A. (atpointof top a) within (topspace top) = atpointof top a
 *)
Theorem ATPOINTOF_WITHIN_TOPSPACE :
    !m a. ((atpointof m a) within (mspace m)) = atpointof m a
Proof
    rw [NET_WITHIN_UNIV, MSPACE]
QED

Theorem NETLIMIT_WITHIN :
   !a:real s. ~(trivial_limit (at a within s))
    ==> (netlimit (at a within s) = a)
Proof
  REWRITE_TAC[trivial_limit, netlimit, AT, WITHIN, DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   ``!x:real. ~(&0 < dist(x,a) /\ dist(x,a) <= dist(a,a) /\ x IN s)``
    ASSUME_TAC THENL
    [ ASM_MESON_TAC[DIST_REFL, REAL_NOT_LT], ASM_MESON_TAC[] ]
QED

(* ------------------------------------------------------------------------- *)
(* Limits in a topological space (from HOL-Light's Multivariate/metric.ml)   *)
(* ------------------------------------------------------------------------- *)

Definition limit :
   limit top (f:'a->'b) l net <=>
     l IN topspace top /\
     (!u. open_in top u /\ l IN u ==> eventually (\x. f x IN u) net)
End

(* Connection between HOL-Light's ‘limit’ and HOL4's ‘tends’

   NOTE: The net with ‘limit’ must be reflexive, which is not assumed in general.
   Further more, the net cannot be trivial, and ‘l IN topspace top’ must be
   assumed because it's not included with ‘f tends l’.
 *)
Theorem tends_imp_limit :
    !top f l net. ~trivial_limit net /\ l IN topspace top ==>
                 (f tends l) (top,netord net) ==> limit top (f:'a->'b) l net
Proof
    rw [limit, tends, eventually, OPEN_NEIGH]
 >> Q.PAT_X_ASSUM ‘!x. u x ==> _’ (MP_TAC o Q.SPEC ‘l’)
 >> POP_ASSUM MP_TAC
 >> rw [IN_APP]
 >> Q.PAT_X_ASSUM ‘!N. neigh top (N,l) ==> _’ (MP_TAC o Q.SPEC ‘N’) >> rw []
 >> Q.EXISTS_TAC ‘n’
 >> CONJ_TAC >- (Q.EXISTS_TAC ‘n’ >> art [])
 >> rpt STRIP_TAC
 >> ‘f x IN N’ by rw [IN_APP]
 >> ‘f x IN u’ by PROVE_TAC [SUBSET_DEF] >> fs [IN_APP]
QED

Theorem limit_alt_tends :
    !top f l net. ~trivial_limit net /\ l IN topspace top /\
                 (!x y. netord net x y ==> netord net y y) ==>
                 (limit top (f:'a->'b) l net <=> (f tends l) (top,netord net))
Proof
    rpt STRIP_TAC
 >> reverse EQ_TAC >- rw [tends_imp_limit]
 >> rw [limit, tends, reflexive_def, neigh]
 >> Q.PAT_X_ASSUM ‘!u. open_in top u /\ l IN u ==> _’ (MP_TAC o Q.SPEC ‘P’)
 >> rw [IN_APP, eventually]
 >> Q.EXISTS_TAC ‘y’
 >> CONJ_TAC
 >- (FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘x’ >> art [])
 >> rpt STRIP_TAC
 >> ‘f m IN P’ by rw [IN_APP]
 >> ‘f m IN N’ by PROVE_TAC [SUBSET_DEF] >> fs [IN_APP]
QED

(* References:

 [1] Moore, E.H., Smith, H.L.: A General Theory of Limits. American Journal of
     Mathematics. 44, 102-121 (1922).
 [2] Kelley, J.L.: General Topology. Springer Science & Business Media (1975).
 [3] https://en.wikipedia.org/wiki/Net_(mathematics)
 [4] Schilling, R.L.: Measures, Integrals and Martingales (2nd Edition).
     Cambridge University Press (2017).
 *)
