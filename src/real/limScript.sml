(*===========================================================================*)
(* Theory of limits, continuity and differentiation of real->real functions  *)
(*===========================================================================*)

(*
*)
structure limScript =
struct

(*
app load ["numLib",
          "pairLib",
          "jrhUtils",
          "seqTheory"];
*)

open HolKernel Parse boolLib hol88Lib numLib reduceLib pairLib
     pairTheory arithmeticTheory numTheory prim_recTheory
     jrhUtils realTheory topologyTheory netsTheory seqTheory;

infix THEN THENL ORELSE ORELSEC ##;

val _ = new_theory "lim";

val _ = Parse.reveal "B";

(*---------------------------------------------------------------------------*)
(* Specialize nets theorems to the pointwise limit of real->real functions   *)
(*---------------------------------------------------------------------------*)

val tends_real_real = new_definition(
  "tends_real_real",
  (--`(tends_real_real f l)(x0) =
        (f tends l)(mtop(mr1),tendsto(mr1,x0))`--));

val _ = overload_on (GrammarSpecials.case_arrow_special, ``tends_real_real``);


val LIM = store_thm("LIM",
  (--`!f y0 x0. (f -> y0)(x0) =
        !e. &0 < e ==>
            ?d. &0 < d /\ !x. &0 < abs(x - x0) /\ abs(x - x0) < d ==>
                abs(f(x) - y0) < e`--),
  REPEAT GEN_TAC THEN
  REWRITE_TAC[tends_real_real, MATCH_MP LIM_TENDS2 (SPEC (--`x0:real`--) MR1_LIMPT)]
  THEN REWRITE_TAC[MR1_DEF] THEN
  GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ABS_SUB] THEN
  REFL_TAC);

val LIM_CONST = store_thm("LIM_CONST",
  (--`!k x. ((\x. k) -> k)(x)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_real_real, MTOP_TENDS] THEN
  GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[METRIC_SAME] THEN
  REWRITE_TAC[tendsto, REAL_LE_REFL] THEN
  MP_TAC(REWRITE_RULE[MTOP_LIMPT] (SPEC (--`x:real`--) MR1_LIMPT)) THEN
  DISCH_THEN(MP_TAC o SPEC (--`e:real`--)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`z:real`--) (ASSUME_TAC o CONJUNCT1)) THEN
  EXISTS_TAC (--`z:real`--) THEN REWRITE_TAC[MR1_DEF, GSYM ABS_NZ] THEN
  REWRITE_TAC[REAL_SUB_0] THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
  ASM_REWRITE_TAC[]);

val LIM_ADD = store_thm("LIM_ADD",
  (--`!f g l m x. (f -> l)(x) /\ (g -> m)(x) ==>
      ((\x. f(x) + g(x)) -> (l + m))(x)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_real_real] THEN
  MATCH_MP_TAC NET_ADD THEN MATCH_ACCEPT_TAC DORDER_TENDSTO);

val LIM_MUL = store_thm("LIM_MUL",
  (--`!f g l m x. (f -> l)(x) /\ (g -> m)(x) ==>
      ((\x. f(x) * g(x)) -> (l * m))(x)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_real_real] THEN
  MATCH_MP_TAC NET_MUL THEN MATCH_ACCEPT_TAC DORDER_TENDSTO);

val LIM_NEG = store_thm("LIM_NEG",
  (--`!f l x. (f -> l)(x) = ((\x. ~(f(x))) -> ~l)(x)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_real_real] THEN
  MATCH_MP_TAC NET_NEG THEN MATCH_ACCEPT_TAC DORDER_TENDSTO);

val LIM_INV = store_thm("LIM_INV",
  (--`!f l x. (f -> l)(x) /\ ~(l = &0) ==>
        ((\x. inv(f(x))) -> inv l)(x)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_real_real] THEN
  MATCH_MP_TAC NET_INV THEN MATCH_ACCEPT_TAC DORDER_TENDSTO);

val LIM_SUB = store_thm("LIM_SUB",
  (--`!f g l m x. (f -> l)(x) /\ (g -> m)(x) ==>
      ((\x. f(x) - g(x)) -> (l - m))(x)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_real_real] THEN
  MATCH_MP_TAC NET_SUB THEN MATCH_ACCEPT_TAC DORDER_TENDSTO);

val LIM_DIV = store_thm("LIM_DIV",
  (--`!f g l m x. (f -> l)(x) /\ (g -> m)(x) /\ ~(m = &0) ==>
      ((\x. f(x) / g(x)) -> (l / m))(x)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_real_real] THEN
  MATCH_MP_TAC NET_DIV THEN MATCH_ACCEPT_TAC DORDER_TENDSTO);

val LIM_NULL = store_thm("LIM_NULL",
  (--`!f l x. (f -> l)(x) = ((\x. f(x) - l) -> &0)(x)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_real_real] THEN
  MATCH_ACCEPT_TAC NET_NULL);

(*---------------------------------------------------------------------------*)
(* One extra theorem is handy                                                *)
(*---------------------------------------------------------------------------*)

val LIM_X = store_thm("LIM_X",
  (--`!x0. ((\x. x) -> x0)(x0)`--),
  GEN_TAC THEN REWRITE_TAC[LIM] THEN X_GEN_TAC (--`e:real`--) THEN
  DISCH_TAC THEN EXISTS_TAC (--`e:real`--) THEN ASM_REWRITE_TAC[] THEN
  BETA_TAC THEN GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]);

(*---------------------------------------------------------------------------*)
(* Uniqueness of limit                                                       *)
(*---------------------------------------------------------------------------*)

val LIM_UNIQ = store_thm("LIM_UNIQ",
  (--`!f l m x. (f -> l)(x) /\ (f -> m)(x) ==> (l = m)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_real_real] THEN
  MATCH_MP_TAC MTOP_TENDS_UNIQ THEN
  MATCH_ACCEPT_TAC DORDER_TENDSTO);

(*---------------------------------------------------------------------------*)
(* Show that limits are equal when functions are equal except at limit point *)
(*---------------------------------------------------------------------------*)

val LIM_EQUAL = store_thm("LIM_EQUAL",
  (--`!f g l x0. (!x. ~(x = x0) ==> (f x = g x)) ==>
        ((f -> l)(x0) = (g -> l)(x0))`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM] THEN DISCH_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  ONCE_REWRITE_TAC[TAUT_CONV (--`(a ==> b = a ==> c) = a ==> (b = c)`--)] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
  ASM_REWRITE_TAC[ABS_NZ]);

(*---------------------------------------------------------------------------*)
(* A more general theorem about rearranging the body of a limit              *)
(*---------------------------------------------------------------------------*)

val LIM_TRANSFORM = store_thm("LIM_TRANSFORM",
  (--`!f g x0 l. ((\x. f(x) - g(x)) -> &0)(x0) /\ (g -> l)(x0)
        ==> (f -> l)(x0)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM] THEN
  DISCH_THEN(curry op THEN (X_GEN_TAC (--`e:real`--) THEN DISCH_TAC) o MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN (MP_TAC o SPEC (--`e / &2`--))) THEN
  ASM_REWRITE_TAC[REAL_LT_HALF1] THEN BETA_TAC THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`d:real`--) STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`c:real`--) STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [(--`c:real`--), (--`d:real`--)] REAL_DOWN2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`b:real`--) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC (--`b:real`--) THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC (--`x:real`--) THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`(e / &2) + (e / &2)`--) THEN
  GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REAL_HALF_DOUBLE] THEN
  REWRITE_TAC[REAL_LE_REFL] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC (--`abs(f(x:real) - g(x)) + abs(g(x) - l)`--) THEN
  SUBST1_TAC(SYM(SPECL
    [(--`(f:real->real) x`--), (--`(g:real->real) x`--), (--`l:real`--)] REAL_SUB_TRIANGLE)) THEN
  REWRITE_TAC[ABS_TRIANGLE] THEN MATCH_MP_TAC REAL_LT_ADD2 THEN
  CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (--`b:real`--) THEN
  ASM_REWRITE_TAC[]);

(*---------------------------------------------------------------------------*)
(* Define differentiation and continuity                                     *)
(*---------------------------------------------------------------------------*)

val diffl = new_infixr_definition("diffl",
--`($diffl f l)(x) = ((\h. (f(x + h) - f(x)) / h) -> l)(&0)`--,
  750);

val contl = new_infixr_definition("contl",
  (--`$contl f x = ((\h. f(x + h)) -> f(x))(&0)`--), 750);

val differentiable = new_infixr_definition("differentiable",
  (--`$differentiable f x = ?l. (f diffl l)(x)`--), 750);

(*---------------------------------------------------------------------------*)
(* Derivative is unique                                                      *)
(*---------------------------------------------------------------------------*)

val DIFF_UNIQ = store_thm("DIFF_UNIQ",
  (--`!f l m x. (f diffl l)(x) /\ (f diffl m)(x) ==> (l = m)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[diffl] THEN
  MATCH_ACCEPT_TAC LIM_UNIQ);

(*---------------------------------------------------------------------------*)
(* Differentiability implies continuity                                      *)
(*---------------------------------------------------------------------------*)

val DIFF_CONT = store_thm("DIFF_CONT",
  (--`!f l x. ($diffl f l)(x) ==> $contl f x`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[diffl, contl] THEN DISCH_TAC THEN
  REWRITE_TAC[tends_real_real] THEN ONCE_REWRITE_TAC[NET_NULL] THEN
  REWRITE_TAC[GSYM tends_real_real] THEN BETA_TAC THEN
  SUBGOAL_THEN (--`((\h. f(x + h) - f(x)) -> &0)(&0) =
                ((\h. ((f(x + h) - f(x)) / h) * h) -> &0)(&0)`--) SUBST1_TAC
  THENL
   [MATCH_MP_TAC LIM_EQUAL THEN
    X_GEN_TAC (--`z:real`--) THEN BETA_TAC THEN
    DISCH_THEN(fn th => REWRITE_TAC[MATCH_MP REAL_DIV_RMUL th]), ALL_TAC] THEN
  GEN_REWR_TAC (RATOR_CONV o LAND_CONV o ABS_CONV o RAND_CONV)
               [SYM(BETA_CONV (--`(\h:real. h) h`--))] THEN
  CONV_TAC(EXACT_CONV[X_BETA_CONV (--`h:real`--) (--`(f(x + h) - f(x)) / h`--)]) THEN
  SUBST1_TAC(SYM(SPEC (--`l:real`--) REAL_MUL_RZERO)) THEN
  MATCH_MP_TAC LIM_MUL THEN BETA_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[LIM] THEN BETA_TAC THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  X_GEN_TAC (--`e:real`--) THEN DISCH_TAC THEN EXISTS_TAC (--`e:real`--) THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]);

(*---------------------------------------------------------------------------*)
(* Alternative definition of continuity                                      *)
(*---------------------------------------------------------------------------*)

val CONTL_LIM = store_thm("CONTL_LIM",
  (--`!f x. f contl x = (f -> f(x))(x)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[contl, LIM] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  ONCE_REWRITE_TAC[TAUT_CONV (--`(a ==> b = a ==> c) = a ==> (b = c)`--)] THEN
  DISCH_TAC THEN BETA_TAC THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN (--`d:real`--) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC (--`d:real`--) THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC (--`k:real`--) THENL
   [DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN REWRITE_TAC[REAL_SUB_ADD2],
    DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_ADD_SUB]]);

(*---------------------------------------------------------------------------*)
(* Alternative (Carathe'odory) definition of derivative                      *)
(*---------------------------------------------------------------------------*)

val DIFF_CARAT = store_thm("DIFF_CARAT",
  (--`!f l x. (f diffl l)(x) =
      ?g. (!z. f(z) - f(x) = g(z) * (z - x)) /\ g contl x /\ (g(x) = l)`--),
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [EXISTS_TAC (--`\z. if (z = x) then l
                       else (f(z) - f(x)) / (z - x)`--) THEN
    BETA_TAC THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC (--`z:real`--) THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[REAL_SUB_REFL, REAL_MUL_RZERO] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
      ASM_REWRITE_TAC[REAL_SUB_0],
      POP_ASSUM MP_TAC THEN MATCH_MP_TAC(TAUT_CONV (--`(a = b) ==> a ==> b`--)) THEN
      REWRITE_TAC[diffl, contl] THEN BETA_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC LIM_EQUAL THEN GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
      ASM_REWRITE_TAC[REAL_ADD_RID_UNIQ, REAL_ADD_SUB]],
    POP_ASSUM(X_CHOOSE_THEN (--`g:real->real`--) STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(UNDISCH_TAC o assert is_eq o concl) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN UNDISCH_TAC (--`g contl x`--) THEN
    ASM_REWRITE_TAC[contl, diffl, REAL_ADD_SUB] THEN
    MATCH_MP_TAC(TAUT_CONV (--`(a = b) ==> a ==> b`--)) THEN
    MATCH_MP_TAC LIM_EQUAL THEN GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
    REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC] THEN
    FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_MUL_RINV th]) THEN
    REWRITE_TAC[REAL_MUL_RID]]);

(*---------------------------------------------------------------------------*)
(* Simple combining theorems for continuity, including composition           *)
(*---------------------------------------------------------------------------*)

val CONT_CONST = store_thm("CONT_CONST",
  (--`!k x. $contl (\x. k) x`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTL_LIM] THEN
  MATCH_ACCEPT_TAC LIM_CONST);

val CONT_ADD = store_thm("CONT_ADD",
  (--`!f g x. $contl f x /\ $contl g x ==> $contl (\x. f(x) + g(x)) x`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTL_LIM] THEN BETA_TAC THEN
  MATCH_ACCEPT_TAC LIM_ADD);

val CONT_MUL = store_thm("CONT_MUL",
  (--`!f g x. $contl f x /\ $contl g x ==> $contl (\x. f(x) * g(x)) x`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTL_LIM] THEN BETA_TAC THEN
  MATCH_ACCEPT_TAC LIM_MUL);

val CONT_NEG = store_thm("CONT_NEG",
  (--`!f x. $contl f x ==> $contl (\x. ~(f(x))) x`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTL_LIM] THEN BETA_TAC THEN
  REWRITE_TAC[GSYM LIM_NEG]);

val CONT_INV = store_thm("CONT_INV",
  (--`!f x. $contl f x /\ ~(f x = &0) ==> $contl (\x. inv(f(x))) x`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTL_LIM] THEN BETA_TAC THEN
  MATCH_ACCEPT_TAC LIM_INV);

val CONT_SUB = store_thm("CONT_SUB",
  (--`!f g x. $contl f x /\ $contl g x ==> $contl (\x. f(x) - g(x)) x`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTL_LIM] THEN BETA_TAC THEN
  MATCH_ACCEPT_TAC LIM_SUB);

val CONT_DIV = store_thm("CONT_DIV",
  (--`!f g x. $contl f x /\ $contl g x /\ ~(g x = &0) ==>
             $contl (\x. f(x) / g(x)) x`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTL_LIM] THEN BETA_TAC THEN
  MATCH_ACCEPT_TAC LIM_DIV);

val CONT_COMPOSE = store_thm("CONT_COMPOSE",
  (--`!f g x. f contl x /\ g contl (f x) ==> (\x. g(f x)) contl x`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[contl, LIM, REAL_SUB_RZERO] THEN
  BETA_TAC THEN DISCH_TAC THEN X_GEN_TAC (--`e:real`--) THEN DISCH_TAC THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_conj o concl) THEN
  DISCH_THEN(CONJUNCTS_THEN MP_TAC) THEN
  DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`d:real`--) STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC (--`d:real`--)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`c:real`--) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC (--`c:real`--) THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC (--`h:real`--) THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
  ASM_CASES_TAC (--`&0 < abs(f(x + h) - f(x))`--) THENL
   [UNDISCH_TAC (--`&0 < abs(f(x + h) - f(x))`--) THEN
    DISCH_THEN(fn th => DISCH_THEN(MP_TAC o CONJ th)) THEN
    DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN REWRITE_TAC[REAL_SUB_ADD2],
    UNDISCH_TAC (--`~(&0 < abs(f(x + h) - f(x)))`--) THEN
    REWRITE_TAC[GSYM ABS_NZ, REAL_SUB_0] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL, ABS_0]]);

(*---------------------------------------------------------------------------*)
(* Intermediate Value Theorem (we prove contrapositive by bisection)         *)
(*---------------------------------------------------------------------------*)

val IVT = store_thm("IVT",
  (--`!f a b y. a <= b /\
             (f(a) <= y /\ y <= f(b)) /\
             (!x. a <= x /\ x <= b ==> f contl x)
        ==> (?x. a <= x /\ x <= b /\ (f(x) = y))`--),
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
  CONV_TAC CONTRAPOS_CONV THEN
  DISCH_THEN(ASSUME_TAC o CONV_RULE NOT_EXISTS_CONV) THEN
  (MP_TAC o C SPEC BOLZANO_LEMMA)
    (--`\(u,v). a <= u /\ u <= v /\ v <= b ==> ~(f(u) <= y /\ y <= f(v))`--) THEN
  CONV_TAC(ONCE_DEPTH_CONV PAIRED_BETA_CONV) THEN
  W(C SUBGOAL_THEN (fn t => REWRITE_TAC[t]) o funpow 2(fst o dest_imp) o snd) THENL
   [ALL_TAC,
    DISCH_THEN(MP_TAC o SPECL [(--`a:real`--), (--`b:real`--)]) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL]] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [(--`u:real`--), (--`v:real`--), (--`w:real`--)] THEN
    CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[DE_MORGAN_THM, NOT_IMP] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY ASM_CASES_TAC [(--`u <= v`--), (--`v <= w`--)] THEN ASM_REWRITE_TAC[] THEN
    DISJ_CASES_TAC(SPECL [(--`y:real`--), (--`(f:real->real) v`--)] REAL_LE_TOTAL) THEN
    ASM_REWRITE_TAC[] THENL [DISJ1_TAC, DISJ2_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC (--`w:real`--), EXISTS_TAC (--`u:real`--)] THEN ASM_REWRITE_TAC[],
    ALL_TAC] THEN
  X_GEN_TAC (--`x:real`--) THEN ASM_CASES_TAC (--`a <= x /\ x <= b`--) THENL
   [ALL_TAC,
    EXISTS_TAC (--`&1`--) THEN REWRITE_TAC[REAL_LT_01] THEN
    MAP_EVERY X_GEN_TAC [(--`u:real`--), (--`v:real`--)] THEN
    REPEAT STRIP_TAC THEN UNDISCH_TAC (--`~(a <= x /\ x <= b)`--) THEN
    REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC (--`u:real`--), EXISTS_TAC (--`v:real`--)] THEN
    ASM_REWRITE_TAC[]] THEN
  UNDISCH_TAC (--`!x. ~(a <= x /\ x <= b /\ (f(x) = (y:real)))`--) THEN
  DISCH_THEN(MP_TAC o SPEC (--`x:real`--)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC (--`!x. a <= x /\ x <= b ==> f contl x`--) THEN
  DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
  REWRITE_TAC[contl, LIM] THEN
  DISCH_THEN(MP_TAC o SPEC (--`abs(y - f(x:real))`--)) THEN
  GEN_REWR_TAC (funpow 2 LAND_CONV) [GSYM ABS_NZ] THEN
  REWRITE_TAC[REAL_SUB_0, REAL_SUB_RZERO] THEN BETA_TAC THEN
  ASSUM_LIST(fn thl => REWRITE_TAC(map GSYM thl)) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`d:real`--) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC (--`d:real`--) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [(--`u:real`--), (--`v:real`--)] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [(--`(f:real->real) x`--), (--`y:real`--)] REAL_LT_TOTAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN DISJ_CASES_TAC THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THENL
   [DISCH_THEN(MP_TAC o SPEC (--`v - x`--)) THEN REWRITE_TAC[NOT_IMP] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[abs, REAL_SUB_LE, REAL_SUB_LT] THEN
      ASM_REWRITE_TAC[REAL_LT_LE] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC (--`f(v:real) < y`--) THEN ASM_REWRITE_TAC[GSYM REAL_NOT_LE],
      ASM_REWRITE_TAC[abs, REAL_SUB_LE] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`v - u`--) THEN
      ASM_REWRITE_TAC[real_sub, REAL_LE_LADD, REAL_LE_NEG, REAL_LE_RADD],
      ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN REWRITE_TAC[REAL_SUB_ADD] THEN
      REWRITE_TAC[REAL_NOT_LT, abs, REAL_SUB_LE] THEN
      SUBGOAL_THEN (--`f(x:real) <= y`--) ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
      SUBGOAL_THEN (--`f(x:real) <= f(v)`--) ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`y:real`--), ALL_TAC] THEN
      ASM_REWRITE_TAC[real_sub, REAL_LE_RADD]],
    DISCH_THEN(MP_TAC o SPEC (--`u - x`--)) THEN REWRITE_TAC[NOT_IMP] THEN
    REPEAT CONJ_TAC THENL
     [ONCE_REWRITE_TAC[ABS_SUB] THEN
      ASM_REWRITE_TAC[abs, REAL_SUB_LE, REAL_SUB_LT] THEN
      ASM_REWRITE_TAC[REAL_LT_LE] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC (--`y < f(x:real)`--) THEN ASM_REWRITE_TAC[GSYM REAL_NOT_LE],
      ONCE_REWRITE_TAC[ABS_SUB] THEN ASM_REWRITE_TAC[abs, REAL_SUB_LE] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`v - u`--) THEN
      ASM_REWRITE_TAC[real_sub, REAL_LE_LADD, REAL_LE_NEG, REAL_LE_RADD],
      ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN REWRITE_TAC[REAL_SUB_ADD] THEN
      REWRITE_TAC[REAL_NOT_LT, abs, REAL_SUB_LE] THEN
      SUBGOAL_THEN (--`f(u:real) < f(x)`--) ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`y:real`--) THEN
        ASM_REWRITE_TAC[], ALL_TAC] THEN
      ASM_REWRITE_TAC[GSYM REAL_NOT_LT] THEN
      ASM_REWRITE_TAC[REAL_NOT_LT, REAL_LE_NEG, real_sub, REAL_LE_RADD]]]);

(*---------------------------------------------------------------------------*)
(* Intermediate value theorem where value at the left end is bigger          *)
(*---------------------------------------------------------------------------*)

val IVT2 = store_thm("IVT2",
  (--`!f a b y. (a <= b) /\ (f(b) <= y /\ y <= f(a)) /\
             (!x. a <= x /\ x <= b ==> $contl f x) ==>
        ?x. a <= x /\ x <= b /\ (f(x) = y)`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL
    [(--`\x:real. ~(f x)`--), (--`a:real`--), (--`b:real`--), (--`~y`--)] IVT)
  THEN BETA_TAC THEN ASM_REWRITE_TAC[REAL_LE_NEG, REAL_NEG_EQ, REAL_NEGNEG]
  THEN DISCH_THEN MATCH_MP_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC CONT_NEG THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);

(*---------------------------------------------------------------------------*)
(* Prove the simple combining theorems for differentiation                   *)
(*---------------------------------------------------------------------------*)

val DIFF_CONST = store_thm("DIFF_CONST",
  (--`!k x. ((\x. k) diffl &0)(x)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[diffl] THEN
  REWRITE_TAC[REAL_SUB_REFL, real_div, REAL_MUL_LZERO] THEN
  MATCH_ACCEPT_TAC LIM_CONST);

val DIFF_ADD = store_thm("DIFF_ADD",
  (--`!f g l m x. (f diffl l)(x) /\ (g diffl m)(x) ==>
                   ((\x. f(x) + g(x)) diffl (l + m))(x)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[diffl] THEN
  DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[REAL_ADD2_SUB2] THEN
  REWRITE_TAC[real_div, REAL_RDISTRIB] THEN
  REWRITE_TAC[GSYM real_div] THEN
  CONV_TAC(EXACT_CONV[X_BETA_CONV (--`h:real`--) (--`(f(x + h) - f(x)) / h`--)]) THEN
  CONV_TAC(EXACT_CONV[X_BETA_CONV (--`h:real`--) (--`(g(x + h) - g(x)) / h`--)]) THEN
  MATCH_MP_TAC LIM_ADD THEN ASM_REWRITE_TAC[]);

val DIFF_MUL = store_thm("DIFF_MUL",
  (--`!f g l m x. (f diffl l)(x) /\ (g diffl m)(x) ==>
                  ((\x. f(x) * g(x)) diffl ((l * g(x)) + (m * f(x))))(x)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[diffl] THEN
  DISCH_TAC THEN BETA_TAC THEN SUBGOAL_THEN
    (--`!a b c d. (a * b) - (c * d) = ((a * b) - (a * d)) + ((a * d) - (c * d))`--)
  (fn th => ONCE_REWRITE_TAC[GEN_ALL th]) THENL
   [REWRITE_TAC[real_sub] THEN
    ONCE_REWRITE_TAC[AC(REAL_ADD_ASSOC,REAL_ADD_SYM)
      (--`(a + b) + (c + d) = (b + c) + (a + d)`--)] THEN
    REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_LID], ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB, GSYM REAL_SUB_RDISTRIB] THEN SUBGOAL_THEN
    (--`!a b c d e. ((a * b) + (c * d)) / e = ((b / e) * a) + ((c / e) * d)`--)
    (fn th => ONCE_REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[real_div] THEN
    REWRITE_TAC[REAL_RDISTRIB] THEN BINOP_TAC THEN
    CONV_TAC(AC_CONV(REAL_MUL_ASSOC,REAL_MUL_SYM)), ALL_TAC] THEN
  GEN_REWR_TAC LAND_CONV [REAL_ADD_SYM] THEN
  CONV_TAC(EXACT_CONV(map (X_BETA_CONV (--`h:real`--))
    [(--`((g(x + h) - g(x)) / h) * f(x + h)`--),
     (--`((f(x + h) - f(x)) / h) * g(x)`--)])) THEN
  MATCH_MP_TAC LIM_ADD THEN
  CONV_TAC(EXACT_CONV(map (X_BETA_CONV (--`h:real`--))
    [(--`(g(x + h) - g(x)) / h`--), (--`f(x + h):real`--),
     (--`(f(x + h) - f(x)) / h`--), (--`g(x:real):real`--)])) THEN
  CONJ_TAC THEN MATCH_MP_TAC LIM_MUL THEN
  BETA_TAC THEN ASM_REWRITE_TAC[LIM_CONST] THEN
  REWRITE_TAC[GSYM contl] THEN
  MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC (--`l:real`--) THEN
  ASM_REWRITE_TAC[diffl]);

val DIFF_CMUL = store_thm("DIFF_CMUL",
  (--`!f c l x. (f diffl l)(x) ==> ((\x. c * f(x)) diffl (c * l))(x)`--),
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o CONJ (SPECL [(--`c:real`--), (--`x:real`--)] DIFF_CONST)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIFF_MUL) THEN BETA_TAC THEN
  REWRITE_TAC[REAL_MUL_LZERO, REAL_ADD_LID] THEN
  MATCH_MP_TAC(TAUT_CONV((--`(a = b) ==> a ==> b`--))) THEN AP_THM_TAC THEN
  GEN_REWR_TAC (RAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
  REWRITE_TAC[]);

val DIFF_NEG = store_thm("DIFF_NEG",
  (--`!f l x. (f diffl l)(x) ==> ((\x. ~(f x)) diffl ~l)(x)`--),
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_NEG_MINUS1] THEN
  MATCH_ACCEPT_TAC DIFF_CMUL);

val DIFF_SUB = store_thm("DIFF_SUB",
  (--`!f g l m x. (f diffl l)(x) /\ (g diffl m)(x) ==>
                   ((\x. f(x) - g(x)) diffl (l - m))(x)`--),
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIFF_ADD o (uncurry CONJ) o
              (I ## MATCH_MP DIFF_NEG) o CONJ_PAIR) THEN
  BETA_TAC THEN REWRITE_TAC[real_sub]);

(*---------------------------------------------------------------------------*)
(* Now the chain rule                                                        *)
(*---------------------------------------------------------------------------*)

val DIFF_CHAIN = store_thm("DIFF_CHAIN",
  (--`!f g l m x.
     (f diffl l)(g x) /\ (g diffl m)(x) ==> ((\x. f(g x)) diffl (l * m))(x)`--),
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN MP_TAC) THEN
  DISCH_THEN(fn th => MP_TAC th THEN ASSUME_TAC(MATCH_MP DIFF_CONT th)) THEN
  REWRITE_TAC[DIFF_CARAT] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`g':real->real`--) STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`f':real->real`--) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC (--`\z. if (z = x) then l * m
                     else (f(g(z):real) - f(g(x))) / (z - x)`--) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL, REAL_MUL_RZERO] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    ASM_REWRITE_TAC[REAL_SUB_0],
    MP_TAC(CONJ (ASSUME (--`g contl x`--)) (ASSUME (--`f' contl (g(x:real))`--))) THEN
    DISCH_THEN(MP_TAC o MATCH_MP CONT_COMPOSE) THEN
    DISCH_THEN(MP_TAC o C CONJ (ASSUME (--`g' contl x`--))) THEN
    DISCH_THEN(MP_TAC o MATCH_MP CONT_MUL) THEN BETA_TAC THEN
    ASM_REWRITE_TAC[contl] THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT_CONV (--`(a = b) ==> a ==> b`--)) THEN
    MATCH_MP_TAC LIM_EQUAL THEN X_GEN_TAC (--`z:real`--) THEN
    DISCH_TAC THEN BETA_TAC THEN ASM_REWRITE_TAC[REAL_ADD_RID_UNIQ] THEN
    REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC, REAL_ADD_SUB] THEN
    FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_MUL_RINV th]) THEN
    REWRITE_TAC[REAL_MUL_RID]]);

(*---------------------------------------------------------------------------*)
(* Differentiation of natural number powers                                  *)
(*---------------------------------------------------------------------------*)

val DIFF_X = store_thm("DIFF_X",
  (--`!x. ((\x. x) diffl &1)(x)`--),
  GEN_TAC THEN REWRITE_TAC[diffl] THEN BETA_TAC THEN
  REWRITE_TAC[REAL_ADD_SUB] THEN REWRITE_TAC[LIM, REAL_SUB_RZERO] THEN
  BETA_TAC THEN X_GEN_TAC (--`e:real`--) THEN DISCH_TAC THEN
  EXISTS_TAC (--`&1`--) THEN REWRITE_TAC[REAL_LT_01] THEN
  GEN_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[GSYM ABS_NZ] THEN
  DISCH_THEN(fn th => REWRITE_TAC[MATCH_MP REAL_DIV_REFL th]) THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL, ABS_0]);

val DIFF_POW = store_thm("DIFF_POW",
  (--`!n x. ((\x. x pow n) diffl (&n * (x pow (n - 1))))(x)`--),
  INDUCT_TAC THEN REWRITE_TAC[pow, DIFF_CONST, REAL_MUL_LZERO] THEN
  X_GEN_TAC (--`x:real`--) THEN
  POP_ASSUM(MP_TAC o CONJ(SPEC (--`x:real`--) DIFF_X) o SPEC (--`x:real`--)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIFF_MUL) THEN BETA_TAC THEN
  MATCH_MP_TAC(TAUT_CONV (--`(a = b) ==> a ==> b`--)) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[REAL_MUL_LID] THEN
  REWRITE_TAC[REAL, REAL_RDISTRIB, REAL_MUL_LID] THEN
  GEN_REWR_TAC RAND_CONV [REAL_ADD_SYM] THEN BINOP_TAC THENL
   [REWRITE_TAC[ADD1, ADD_SUB],
    STRUCT_CASES_TAC (SPEC (--`n:num`--) num_CASES) THEN
    REWRITE_TAC[REAL_MUL_LZERO] THEN
    REWRITE_TAC[ADD1, ADD_SUB, POW_ADD] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
    REWRITE_TAC[ONE, pow] THEN
    REWRITE_TAC[SYM ONE, REAL_MUL_RID]]);

(*---------------------------------------------------------------------------*)
(* Now power of -1 (then differentiation of inverses follows from chain rule)*)
(*---------------------------------------------------------------------------*)

val DIFF_XM1 = store_thm("DIFF_XM1",
  (--`!x. ~(x = &0) ==> ((\x. inv(x)) diffl (~(inv(x) pow 2)))(x)`--),
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[diffl] THEN BETA_TAC THEN
  MATCH_MP_TAC LIM_TRANSFORM THEN
  EXISTS_TAC (--`\h. ~(inv(x + h) * inv(x))`--) THEN
  BETA_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[LIM] THEN X_GEN_TAC (--`e:real`--) THEN DISCH_TAC THEN
    EXISTS_TAC (--`abs(x)`--) THEN
    EVERY_ASSUM(fn th => REWRITE_TAC[REWRITE_RULE[ABS_NZ] th]) THEN
    X_GEN_TAC (--`h:real`--) THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN BETA_TAC THEN
    W(C SUBGOAL_THEN SUBST1_TAC o C (curry mk_eq) (--`&0`--) o
      rand o rator o snd) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ABS_ZERO, REAL_SUB_0] THEN
    SUBGOAL_THEN (--`~(x + h = &0)`--) ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LNEG_UNIQ] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC (--`abs(h) < abs(~h)`--) THEN
      REWRITE_TAC[ABS_NEG, REAL_LT_REFL], ALL_TAC] THEN
    W(fn (asl,w) => MP_TAC(SPECL [(--`x * (x + h)`--), lhs w, rhs w] REAL_EQ_LMUL)) THEN
    ASM_REWRITE_TAC[REAL_ENTIRE] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL, GSYM REAL_NEG_RMUL] THEN
    REWRITE_TAC[real_div, REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB] THEN
    ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
      (--`(a * b) * (c * d) = (c * b) * (d * a)`--)] THEN
    REWRITE_TAC(map (MATCH_MP REAL_MUL_LINV o ASSUME)
     [(--`~(x = &0)`--), (--`~(x + h = &0)`--)]) THEN REWRITE_TAC[REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
      (--`(a * b) * (c * d) = (a * d) * (c * b)`--)] THEN
    REWRITE_TAC[MATCH_MP REAL_MUL_LINV (ASSUME (--`~(x = &0)`--))] THEN
    REWRITE_TAC[REAL_MUL_LID, GSYM REAL_SUB_LDISTRIB] THEN
    REWRITE_TAC[REWRITE_RULE[REAL_NEG_SUB]
      (AP_TERM (--`$~`--) (SPEC_ALL REAL_ADD_SUB))] THEN
    REWRITE_TAC[GSYM REAL_NEG_RMUL] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[ABS_NZ],

    REWRITE_TAC[POW_2] THEN
    CONV_TAC(EXACT_CONV[X_BETA_CONV (--`h:real`--) (--`inv(x + h) * inv(x)`--)]) THEN
    REWRITE_TAC[GSYM LIM_NEG] THEN
    CONV_TAC(EXACT_CONV(map (X_BETA_CONV (--`h:real`--)) [(--`inv(x + h)`--), (--`inv(x)`--)]))
    THEN MATCH_MP_TAC LIM_MUL THEN BETA_TAC THEN
    REWRITE_TAC[LIM_CONST] THEN
    CONV_TAC(EXACT_CONV[X_BETA_CONV (--`h:real`--) (--`x + h`--)]) THEN
    MATCH_MP_TAC LIM_INV THEN ASM_REWRITE_TAC[] THEN
    GEN_REWR_TAC LAND_CONV [GSYM REAL_ADD_RID] THEN
    CONV_TAC(EXACT_CONV(map (X_BETA_CONV (--`h:real`--)) [(--`x:real`--), (--`h:real`--)])) THEN
    MATCH_MP_TAC LIM_ADD THEN BETA_TAC THEN REWRITE_TAC[LIM_CONST] THEN
    MATCH_ACCEPT_TAC LIM_X]);

(*---------------------------------------------------------------------------*)
(* Now differentiation of inverse and quotient                               *)
(*---------------------------------------------------------------------------*)

val DIFF_INV = store_thm("DIFF_INV",
  (--`!f l x. (f diffl l)(x) /\ ~(f(x) = &0) ==>
        ((\x. inv(f x)) diffl ~(l / (f(x) pow 2)))(x)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[real_div, REAL_NEG_RMUL] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN DISCH_TAC THEN
  MATCH_MP_TAC DIFF_CHAIN THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP POW_INV (CONJUNCT2 th)]) THEN
  MATCH_MP_TAC(CONV_RULE(ONCE_DEPTH_CONV ETA_CONV) DIFF_XM1) THEN
  ASM_REWRITE_TAC[]);

val DIFF_DIV = store_thm("DIFF_DIV",
  (--`!f g l m x. (f diffl l)(x) /\ (g diffl m)(x) /\ ~(g(x) = &0) ==>
    ((\x. f(x) / g(x)) diffl (((l * g(x)) - (m * f(x))) / (g(x) pow 2)))(x)`--),
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  REWRITE_TAC[real_div] THEN
  MP_TAC(SPECL [(--`g:real->real`--), (--`m:real`--), (--`x:real`--)] DIFF_INV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJ(ASSUME (--`(f diffl l)(x)`--))) THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIFF_MUL) THEN BETA_TAC THEN
  W(C SUBGOAL_THEN SUBST1_TAC o mk_eq o
      ((rand o rator) ## (rand o rator)) o dest_imp o snd) THEN
  REWRITE_TAC[] THEN REWRITE_TAC[real_sub] THEN
  REWRITE_TAC[REAL_LDISTRIB, REAL_RDISTRIB] THEN BINOP_TAC THENL
   [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
    REWRITE_TAC[POW_2] THEN
    FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_INV_MUL (W CONJ th)]) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_MUL_RINV th]) THEN
    REWRITE_TAC[REAL_MUL_LID],
    REWRITE_TAC[real_div, GSYM REAL_NEG_LMUL, GSYM REAL_NEG_RMUL] THEN
    AP_TERM_TAC THEN CONV_TAC(AC_CONV(REAL_MUL_ASSOC,REAL_MUL_SYM))]);

(*---------------------------------------------------------------------------*)
(* Differentiation of finite sum                                             *)
(*---------------------------------------------------------------------------*)

val DIFF_SUM = store_thm("DIFF_SUM",
  (--`!f f' m n x. (!r:num. m <= r /\ r < (m + n)
                 ==> ((\x. f r x) diffl (f' r x))(x))
     ==> ((\x. sum(m,n)(\n. f n x)) diffl (sum(m,n) (\r. f' r x)))(x)`--),
  REPEAT GEN_TAC THEN SPEC_TAC((--`n:num`--),(--`n:num`--)) THEN
  INDUCT_TAC THEN REWRITE_TAC[sum, DIFF_CONST] THEN DISCH_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV HABS_CONV) THEN MATCH_MP_TAC DIFF_ADD THEN
  BETA_TAC THEN CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LESS_TRANS THEN
    EXISTS_TAC (--`m + n:num`--) THEN ASM_REWRITE_TAC[ADD_CLAUSES, LESS_SUC_REFL],
    REWRITE_TAC[LESS_EQ_ADD, ADD_CLAUSES, LESS_SUC_REFL]]);

(*---------------------------------------------------------------------------*)
(* By bisection, function continuous on closed interval is bounded above     *)
(*---------------------------------------------------------------------------*)

val CONT_BOUNDED = store_thm("CONT_BOUNDED",
  (--`!f a b. (a <= b /\ !x. a <= x /\ x <= b ==> $contl f x)
        ==> ?M. !x. a <= x /\ x <= b ==> f(x) <= M`--),
  REPEAT STRIP_TAC THEN
  (MP_TAC o C SPEC BOLZANO_LEMMA)
    (--`\(u,v). a <= u /\ u <= v /\ v <= b ==>
               ?M. !x. u <= x /\ x <= v ==> f x <= M`--) THEN
  CONV_TAC(ONCE_DEPTH_CONV PAIRED_BETA_CONV) THEN
  W(C SUBGOAL_THEN (fn t => REWRITE_TAC[t]) o funpow 2(fst o dest_imp) o snd) THENL
   [ALL_TAC,
    DISCH_THEN(MP_TAC o SPECL [(--`a:real`--), (--`b:real`--)]) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL]] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [(--`u:real`--), (--`v:real`--), (--`w:real`--)] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    DISCH_TAC THEN
    REPEAT(FIRST_ASSUM(UNDISCH_TAC o assert is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN (--`v <= b`--) ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`w:real`--) THEN
      ASM_REWRITE_TAC[], ALL_TAC] THEN
    SUBGOAL_THEN (--`a <= v`--) ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`u:real`--) THEN
      ASM_REWRITE_TAC[], ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC (--`M1:real`--)) THEN
    DISCH_THEN(X_CHOOSE_TAC (--`M2:real`--)) THEN
    DISJ_CASES_TAC(SPECL [(--`M1:real`--), (--`M2:real`--)] REAL_LE_TOTAL) THENL
     [EXISTS_TAC (--`M2:real`--) THEN X_GEN_TAC (--`x:real`--) THEN STRIP_TAC THEN
      DISJ_CASES_TAC(SPECL [(--`x:real`--), (--`v:real`--)] REAL_LE_TOTAL) THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`M1:real`--) THEN
        ASM_REWRITE_TAC[], ALL_TAC] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[],
      EXISTS_TAC (--`M1:real`--) THEN X_GEN_TAC (--`x:real`--) THEN STRIP_TAC THEN
      DISJ_CASES_TAC(SPECL [(--`x:real`--), (--`v:real`--)] REAL_LE_TOTAL) THENL
       [ALL_TAC, MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC (--`M2:real`--) THEN ASM_REWRITE_TAC[]] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]],
    ALL_TAC] THEN
  X_GEN_TAC (--`x:real`--) THEN ASM_CASES_TAC (--`a <= x /\ x <= b`--) THENL
   [ALL_TAC,
    EXISTS_TAC (--`&1`--) THEN REWRITE_TAC[REAL_LT_01] THEN
    MAP_EVERY X_GEN_TAC [(--`u:real`--), (--`v:real`--)] THEN
    REPEAT STRIP_TAC THEN UNDISCH_TAC (--`~(a <= x /\ x <= b)`--) THEN
    CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC (--`u:real`--), EXISTS_TAC (--`v:real`--)] THEN
    ASM_REWRITE_TAC[]] THEN
  UNDISCH_TAC (--`!x. a <= x /\ x <= b ==> f contl x`--) THEN
  DISCH_THEN(MP_TAC o SPEC (--`x:real`--)) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[contl, LIM] THEN
  DISCH_THEN(MP_TAC o SPEC (--`&1`--)) THEN REWRITE_TAC[REAL_LT_01] THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN (--`d:real`--) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC (--`d:real`--) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [(--`u:real`--), (--`v:real`--)] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC (--`abs(f(x:real)) + &1`--) THEN
  X_GEN_TAC (--`z:real`--) THEN STRIP_TAC THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
  DISCH_THEN(MP_TAC o SPEC (--`z - x`--)) THEN
  GEN_REWR_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_ADD_SYM] THEN
  REWRITE_TAC[REAL_SUB_ADD] THEN DISCH_TAC THEN
  MP_TAC(SPECL [(--`f(z:real) - f(x)`--), (--`(f:real->real) x`--)] ABS_TRIANGLE) THEN
  REWRITE_TAC[REAL_SUB_ADD] THEN
  DISCH_THEN(ASSUME_TAC o ONCE_REWRITE_RULE[REAL_ADD_SYM]) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`abs(f(z:real))`--) THEN
  REWRITE_TAC[ABS_LE] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC (--`abs(f(x:real)) + (abs(f(z) - f(x)))`--) THEN
  ASM_REWRITE_TAC[REAL_LE_LADD] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
  ASM_CASES_TAC (--`z:real = x`--) THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL, ABS_0, REAL_LT_01],
    FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[GSYM ABS_NZ] THEN
    ASM_REWRITE_TAC[REAL_SUB_0, abs, REAL_SUB_LE] THEN
    REWRITE_TAC[REAL_NEG_SUB] THEN COND_CASES_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`v - u`--) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC (--`v - x`--), EXISTS_TAC (--`v - z`--)] THEN
    ASM_REWRITE_TAC[real_sub, REAL_LE_RADD, REAL_LE_LADD, REAL_LE_NEG]]);

(*---------------------------------------------------------------------------*)
(* Refine the above to existence of least upper bound                        *)
(*---------------------------------------------------------------------------*)

val CONT_HASSUP = store_thm("CONT_HASSUP",
  (--`!f a b. (a <= b /\ !x. a <= x /\ x <= b ==> $contl f x)
        ==> ?M. (!x. a <= x /\ x <= b ==> f(x) <= M) /\
                (!N. N < M ==> ?x. a <= x /\ x <= b /\ N < f(x))`--),
  let val tm = (--`\y:real. ?x. a <= x /\ x <= b /\ (y = f(x))`--) in
  REPEAT GEN_TAC THEN DISCH_TAC THEN MP_TAC(SPEC tm REAL_SUP_LE) THEN
  BETA_TAC THEN
  W(C SUBGOAL_THEN (fn t => REWRITE_TAC[t]) o funpow 2 (fst o dest_imp) o snd)
  THENL
   [CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [(--`(f:real->real) a`--), (--`a:real`--)] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL, REAL_LE_LT],
      POP_ASSUM(X_CHOOSE_TAC (--`M:real`--) o MATCH_MP CONT_BOUNDED) THEN
      EXISTS_TAC (--`M:real`--) THEN X_GEN_TAC (--`y:real`--) THEN
      DISCH_THEN(X_CHOOSE_THEN (--`x:real`--) MP_TAC) THEN
      REWRITE_TAC[CONJ_ASSOC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC SUBST1_TAC) THEN
      POP_ASSUM MATCH_ACCEPT_TAC],
    DISCH_TAC THEN EXISTS_TAC (--`sup ^tm`--) THEN CONJ_TAC THENL
     [X_GEN_TAC (--`x:real`--) THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC (--`sup ^tm`--)) THEN
      REWRITE_TAC[REAL_LT_REFL] THEN
      CONV_TAC(ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
      DISCH_THEN(MP_TAC o SPEC (--`(f:real->real) x`--)) THEN
      REWRITE_TAC[DE_MORGAN_THM, REAL_NOT_LT] THEN
      CONV_TAC(ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
      DISCH_THEN(DISJ_CASES_THEN MP_TAC) THEN REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC (--`x:real`--)) THEN ASM_REWRITE_TAC[],
      GEN_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM o SPEC (--`N:real`--)) THEN
      DISCH_THEN(X_CHOOSE_THEN (--`y:real`--) MP_TAC) THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN (--`x:real`--) MP_TAC) THEN
      REWRITE_TAC[CONJ_ASSOC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC SUBST_ALL_TAC) THEN
      DISCH_TAC THEN EXISTS_TAC (--`x:real`--) THEN ASM_REWRITE_TAC[]]] end);

(*---------------------------------------------------------------------------*)
(* Now show that it attains its upper bound                                  *)
(*---------------------------------------------------------------------------*)

val CONT_ATTAINS = store_thm("CONT_ATTAINS",
  (--`!f a b. (a <= b /\ !x. a <= x /\ x <= b ==> $contl f x)
        ==> ?M. (!x. a <= x /\ x <= b ==> f(x) <= M) /\
                (?x. a <= x /\ x <= b /\ (f(x) = M))`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN (--`M:real`--) STRIP_ASSUME_TAC o MATCH_MP CONT_HASSUP)
  THEN EXISTS_TAC (--`M:real`--) THEN ASM_REWRITE_TAC[] THEN
  GEN_REWR_TAC I [TAUT_CONV (--`a:bool = ~~a`--)] THEN
  CONV_TAC(RAND_CONV NOT_EXISTS_CONV) THEN
  REWRITE_TAC[TAUT_CONV (--`~(a /\ b /\ c) = a /\ b ==> ~c`--)] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN (--`!x. a <= x /\ x <= b ==> f(x) < M`--) MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_LT_LE] THEN
    CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
  PURE_ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN (--`!x. a <= x /\ x <= b ==> $contl (\x. inv(M - f(x))) x`--)
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    CONV_TAC(ONCE_DEPTH_CONV HABS_CONV) THEN
    MATCH_MP_TAC CONT_INV THEN BETA_TAC THEN
    REWRITE_TAC[REAL_SUB_0] THEN CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
    CONJ_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC REAL_LT_IMP_NE THEN
      ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
    CONV_TAC(ONCE_DEPTH_CONV HABS_CONV) THEN
    MATCH_MP_TAC CONT_SUB THEN BETA_TAC THEN
    REWRITE_TAC[CONT_CONST] THEN
    CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
    FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2) THEN
    ASM_REWRITE_TAC[], ALL_TAC] THEN
  SUBGOAL_THEN (--`?k. !x. a <= x /\ x <= b ==> (\x. inv(M - (f x))) x <= k`--)
  MP_TAC THENL
   [MATCH_MP_TAC CONT_BOUNDED THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  BETA_TAC THEN DISCH_THEN(X_CHOOSE_TAC (--`k:real`--)) THEN
  SUBGOAL_THEN (--`!x. a <= x /\ x <= b ==> &0 < inv(M - f(x))`--) ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_INV_POS THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  SUBGOAL_THEN (--`!x. a <= x /\ x <= b ==> (\x. inv(M - (f x))) x < (k + &1)`--)
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC (--`k:real`--) THEN REWRITE_TAC[REAL_LT_ADDR, REAL_LT_01] THEN
    BETA_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[], ALL_TAC] THEN
  SUBGOAL_THEN (--`!x. a <= x /\ x <= b ==>
         inv(k + &1) < inv((\x. inv(M - (f x))) x)`--) MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN
    CONJ_TAC THENL
     [BETA_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[],
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]], ALL_TAC] THEN
  BETA_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN (--`!x. a <= x /\ x <= b ==> inv(k + &1) < (M - (f x))`--)
  MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN (--`~(M - f(x:real) = &0)`--)
      (SUBST1_TAC o SYM o MATCH_MP REAL_INVINV) THENL
     [CONV_TAC(RAND_CONV SYM_CONV) THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[],
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]], ALL_TAC] THEN
  REWRITE_TAC[REAL_LT_SUB_LADD] THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  ONCE_REWRITE_TAC[GSYM REAL_LT_SUB_LADD] THEN DISCH_TAC THEN
  UNDISCH_TAC (--`!N. N < M ==> (?x. a <= x /\ x <= b /\ N < (f x))`--) THEN
  DISCH_THEN(MP_TAC o SPEC (--`M - inv(k + &1)`--)) THEN
  REWRITE_TAC[REAL_LT_SUB_RADD, REAL_LT_ADDR] THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INV_POS THEN MATCH_MP_TAC REAL_LT_TRANS THEN
    EXISTS_TAC (--`k:real`--) THEN REWRITE_TAC[REAL_LT_ADDR, REAL_LT_01] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`inv(M - f(a:real))`--) THEN
    CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_LE_REFL],
    DISCH_THEN(X_CHOOSE_THEN (--`x:real`--) MP_TAC) THEN REWRITE_TAC[CONJ_ASSOC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[REAL_NOT_LT] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    ONCE_REWRITE_TAC[GSYM REAL_LT_SUB_LADD] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);

(*---------------------------------------------------------------------------*)
(* Same theorem for lower bound                                              *)
(*---------------------------------------------------------------------------*)

val CONT_ATTAINS2 = store_thm("CONT_ATTAINS2",
  (--`!f a b. (a <= b /\ !x. a <= x /\ x <= b ==> $contl f x)
        ==> ?M. (!x. a <= x /\ x <= b ==> M <= f(x)) /\
                (?x. a <= x /\ x <= b /\ (f(x) = M))`--),
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN (--`!x. a <= x /\ x <= b ==> (\x. ~(f x)) contl x`--) MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CONT_NEG THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJ (ASSUME (--`a <= b`--))) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`M:real`--) MP_TAC o MATCH_MP CONT_ATTAINS) THEN
  BETA_TAC THEN DISCH_TAC THEN EXISTS_TAC (--`~M`--) THEN CONJ_TAC THENL
   [GEN_TAC THEN GEN_REWR_TAC RAND_CONV [GSYM REAL_LE_NEG] THEN
    ASM_REWRITE_TAC[REAL_NEGNEG],
    ASM_REWRITE_TAC[GSYM REAL_NEG_EQ]]);

(*---------------------------------------------------------------------------*)
(* Show it attains *all* values in its range                                 *)
(*---------------------------------------------------------------------------*)

val CONT_ATTAINS_ALL = store_thm("CONT_ATTAINS_ALL",
  (--`!f a b. a <= b /\ (!x. a <= x /\ x <= b ==> f contl x) ==>
     ?L M. L <= M /\
           (!y. L <= y /\ y <= M ==> ?x. a <= x /\ x <= b /\ (f(x) = y)) /\
           (!x. a <= x /\ x <= b ==> L <= f(x) /\ f(x) <= M)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN (--`M:real`--) MP_TAC o MATCH_MP CONT_ATTAINS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC (--`xm:real`--))) THEN
  FIRST_ASSUM(X_CHOOSE_THEN (--`L:real`--) MP_TAC o MATCH_MP CONT_ATTAINS2) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC (--`xl:real`--))) THEN
  MAP_EVERY EXISTS_TAC [(--`L:real`--), (--`M:real`--)] THEN REPEAT CONJ_TAC THENL
   [REPEAT(FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPEC (--`a:real`--))) THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    REPEAT DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC (--`(f:real->real)(a)`--) THEN ASM_REWRITE_TAC[],
    X_GEN_TAC (--`y:real`--) THEN STRIP_TAC THEN
    DISJ_CASES_TAC(SPECL [(--`xl:real`--), (--`xm:real`--)] REAL_LE_TOTAL) THENL
     [MP_TAC(SPECL [(--`f:real->real`--), (--`xl:real`--), (--`xm:real`--), (--`y:real`--)] IVT),
      MP_TAC(SPECL [(--`f:real->real`--), (--`xm:real`--), (--`xl:real`--), (--`y:real`--)] IVT2)] THEN
    ASM_REWRITE_TAC[] THEN
    (W(C SUBGOAL_THEN ASSUME_TAC o funpow 2 (fst o dest_imp) o snd) THENL
      [X_GEN_TAC (--`x:real`--) THEN STRIP_TAC THEN
       FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2),
       ASM_REWRITE_TAC[] THEN
       DISCH_THEN(X_CHOOSE_THEN (--`x:real`--) STRIP_ASSUME_TAC) THEN
       EXISTS_TAC (--`x:real`--) THEN ASM_REWRITE_TAC[]] THEN
     (CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      FIRST [EXISTS_TAC (--`xl:real`--) THEN ASM_REWRITE_TAC[] THEN NO_TAC,
             EXISTS_TAC (--`xm:real`--) THEN ASM_REWRITE_TAC[] THEN NO_TAC])),
    GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);

(*---------------------------------------------------------------------------*)
(* If f'(x) real_gt 0 then x is locally strictly increasing at the right           *)
(*---------------------------------------------------------------------------*)

val DIFF_LINC = store_thm("DIFF_LINC",
  (--`!f x l. (f diffl l)(x) /\ &0 < l ==>
      ?d. &0 < d /\ !h. &0 < h /\ h < d ==> f(x) < f(x + h)`--),
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[diffl, LIM, REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC (--`l:real`--)) THEN ASM_REWRITE_TAC[] THEN BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN (--`d:real`--) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC (--`d:real`--) THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_INV_POS o CONJUNCT1) THEN
  DISCH_THEN(fn th => ONCE_REWRITE_TAC[GSYM(MATCH_MP REAL_LT_RMUL th)]) THEN
  REWRITE_TAC[REAL_MUL_LZERO] THEN REWRITE_TAC[GSYM real_div] THEN
  MATCH_MP_TAC ABS_SIGN THEN EXISTS_TAC (--`l:real`--) THEN
  FIRST_ASSUM MATCH_MP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE o CONJUNCT1) THEN
  ASM_REWRITE_TAC[abs]);

(*---------------------------------------------------------------------------*)
(* If f'(x) < 0 then x is locally strictly increasing at the left            *)
(*---------------------------------------------------------------------------*)

val DIFF_LDEC = store_thm("DIFF_LDEC",
  (--`!f x l. (f diffl l)(x) /\ l < &0 ==>
      ?d. &0 < d /\ !h. &0 < h /\ h < d ==> f(x) < f(x - h)`--),
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[diffl, LIM, REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC (--`~l`--)) THEN
  ONCE_REWRITE_TAC[GSYM REAL_NEG_LT0] THEN ASM_REWRITE_TAC[REAL_NEGNEG] THEN
  REWRITE_TAC[REAL_NEG_LT0] THEN BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN (--`d:real`--) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC (--`d:real`--) THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_INV_POS o CONJUNCT1) THEN
  DISCH_THEN(fn th => ONCE_REWRITE_TAC[GSYM(MATCH_MP REAL_LT_RMUL th)]) THEN
  REWRITE_TAC[REAL_MUL_LZERO] THEN
  REWRITE_TAC[GSYM REAL_NEG_LT0, REAL_NEG_RMUL] THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_NEG_INV
   (GSYM (MATCH_MP REAL_LT_IMP_NE (CONJUNCT1 th)))]) THEN
  MATCH_MP_TAC ABS_SIGN2 THEN EXISTS_TAC (--`l:real`--) THEN
  REWRITE_TAC[GSYM real_div] THEN
  GEN_REWR_TAC (LAND_CONV o RAND_CONV o funpow 3 LAND_CONV o RAND_CONV)
               [real_sub] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE o CONJUNCT1) THEN
  REWRITE_TAC[abs, GSYM REAL_NEG_LE0, REAL_NEGNEG] THEN
  ASM_REWRITE_TAC[GSYM REAL_NOT_LT]);

(*---------------------------------------------------------------------------*)
(* If f is differentiable at a local maximum x, f'(x) = 0                    *)
(*---------------------------------------------------------------------------*)

val DIFF_LMAX = store_thm("DIFF_LMAX",
  (--`!f x l. ($diffl f l)(x) /\
           (?d. &0 < d /\ (!y. abs(x - y) < d ==> f(y) <= f(x))) ==> (l = &0)`--),
  REPEAT GEN_TAC THEN DISCH_THEN
   (CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_THEN (--`k:real`--) STRIP_ASSUME_TAC)) THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (SPECL [(--`l:real`--), (--`&0`--)] REAL_LT_TOTAL) THEN
  ASM_REWRITE_TAC[] THENL
   [DISCH_THEN(MP_TAC o C CONJ(ASSUME (--`l < &0`--))) THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIFF_LDEC) THEN
    DISCH_THEN(X_CHOOSE_THEN (--`e:real`--) MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MP_TAC(SPECL [(--`k:real`--), (--`e:real`--)] REAL_DOWN2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`d:real`--) STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC (--`d:real`--)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPEC (--`x - d`--)) THEN REWRITE_TAC[REAL_SUB_SUB2] THEN
    SUBGOAL_THEN (--`&0 <= d`--) ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
    ASM_REWRITE_TAC[abs] THEN ASM_REWRITE_TAC[GSYM REAL_NOT_LT],
    DISCH_THEN(MP_TAC o C CONJ(ASSUME (--`&0 < l`--))) THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIFF_LINC) THEN
    DISCH_THEN(X_CHOOSE_THEN (--`e:real`--) MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MP_TAC(SPECL [(--`k:real`--), (--`e:real`--)] REAL_DOWN2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`d:real`--) STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC (--`d:real`--)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPEC (--`x + d`--)) THEN REWRITE_TAC[REAL_ADD_SUB2] THEN
    SUBGOAL_THEN (--`&0 <= d`--) ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
    REWRITE_TAC[ABS_NEG] THEN
    ASM_REWRITE_TAC[abs] THEN ASM_REWRITE_TAC[GSYM REAL_NOT_LT]]);

(*---------------------------------------------------------------------------*)
(* Similar theorem for a local minimum                                       *)
(*---------------------------------------------------------------------------*)

val DIFF_LMIN = store_thm("DIFF_LMIN",
  (--`!f x l. ($diffl f l)(x) /\
           (?d. &0 < d /\ (!y. abs(x - y) < d ==> f(x) <= f(y))) ==> (l = &0)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [(--`\x:real. ~(f x)`--), (--`x:real`--), (--`~l`--)] DIFF_LMAX) THEN
  BETA_TAC THEN REWRITE_TAC[REAL_LE_NEG, REAL_NEG_EQ0] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC DIFF_NEG THEN ASM_REWRITE_TAC[]);

(*---------------------------------------------------------------------------*)
(* In particular if a function is locally flat                               *)
(*---------------------------------------------------------------------------*)

val DIFF_LCONST = store_thm("DIFF_LCONST",
  (--`!f x l. ($diffl f l)(x) /\
         (?d. &0 < d /\ (!y. abs(x - y) < d ==> (f(y) = f(x)))) ==> (l = &0)`--),
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`d:real`--) STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC DIFF_LMAX THEN
  MAP_EVERY EXISTS_TAC [(--`f:real->real`--), (--`x:real`--)] THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC (--`d:real`--) THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  DISCH_THEN(fn th => FIRST_ASSUM(SUBST1_TAC o C MATCH_MP th)) THEN
  MATCH_ACCEPT_TAC REAL_LE_REFL);

(*---------------------------------------------------------------------------*)
(* Lemma about introducing open ball in open interval                        *)
(*---------------------------------------------------------------------------*)

val INTERVAL_LEMMA = store_thm("INTERVAL_LEMMA",
  (--`!a b x. a < x /\ x < b ==>
        ?d. &0 < d /\ !y. abs(x - y) < d ==> a <= y /\ y <= b`--),
  REPEAT GEN_TAC THEN DISCH_THEN (fn th =>
    STRIP_ASSUME_TAC th THEN
    MP_TAC (ONCE_REWRITE_RULE[GSYM REAL_SUB_LT] th)) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`d:real`--) MP_TAC o MATCH_MP REAL_DOWN2) THEN
  REWRITE_TAC[REAL_LT_SUB_LADD] THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  EXISTS_TAC (--`d:real`--) THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC (--`y:real`--) THEN
  REWRITE_TAC[abs, REAL_SUB_LE] THEN COND_CASES_TAC THEN
  REWRITE_TAC[REAL_NEG_SUB, REAL_LT_SUB_RADD] THEN DISCH_TAC THEN CONJ_TAC
  THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`x - d`--) THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THENL
     [REWRITE_TAC[REAL_LT_SUB_LADD], REWRITE_TAC[REAL_LT_SUB_RADD]] THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_REWRITE_TAC[],
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`x:real`--) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[],
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_TRANS THEN
    EXISTS_TAC (--`x:real`--) THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[GSYM REAL_NOT_LE],
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_TRANS THEN
    EXISTS_TAC (--`d + x`--) THEN ASM_REWRITE_TAC[]]);

(*---------------------------------------------------------------------------*)
(* Now Rolle's theorem                                                       *)
(*---------------------------------------------------------------------------*)

val ROLLE = store_thm("ROLLE",
  (--`!f a b. a < b /\
           (f(a) = f(b)) /\
           (!x. a <= x /\ x <= b ==> f contl x) /\
           (!x. a < x /\ x < b ==> f differentiable x)
        ==> ?z. a < z /\ z < b /\ (f diffl &0)(z)`--),
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
  MP_TAC(SPECL [(--`f:real->real`--), (--`a:real`--), (--`b:real`--)] CONT_ATTAINS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN (--`M:real`--) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC (--`x1:real`--))) THEN
  MP_TAC(SPECL [(--`f:real->real`--), (--`a:real`--), (--`b:real`--)] CONT_ATTAINS2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN (--`m:real`--) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC (--`x2:real`--))) THEN
  ASM_CASES_TAC (--`a < x1 /\ x1 < b`--) THENL
   [FIRST_ASSUM(X_CHOOSE_THEN (--`d:real`--) MP_TAC o MATCH_MP INTERVAL_LEMMA) THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN EXISTS_TAC (--`x1:real`--) THEN
    ASM_REWRITE_TAC[] THEN SUBGOAL_THEN
     (--`?l. (f diffl l)(x1) /\
          ?d. &0 < d /\ (!y. abs(x1 - y) < d ==> f(y) <= f(x1))`--) MP_TAC THENL
     [CONV_TAC EXISTS_AND_CONV THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM differentiable] THEN FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[],
        EXISTS_TAC (--`d:real`--) THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC (--`y:real`--) THEN
        DISCH_TAC THEN REPEAT(FIRST_ASSUM MATCH_MP_TAC) THEN
        ASM_REWRITE_TAC[]], ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`l:real`--) MP_TAC) THEN
    DISCH_THEN(fn th => ASSUME_TAC th THEN SUBST_ALL_TAC(MATCH_MP DIFF_LMAX th))
    THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  ASM_CASES_TAC (--`a < x2 /\ x2 < b`--) THENL
   [FIRST_ASSUM(X_CHOOSE_THEN (--`d:real`--) MP_TAC o MATCH_MP INTERVAL_LEMMA) THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN EXISTS_TAC (--`x2:real`--) THEN
    ASM_REWRITE_TAC[] THEN SUBGOAL_THEN
     (--`?l. (f diffl l)(x2) /\
          ?d. &0 < d /\ (!y. abs(x2 - y) < d ==> f(x2) <= f(y))`--) MP_TAC THENL
     [CONV_TAC EXISTS_AND_CONV THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM differentiable] THEN FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[],
        EXISTS_TAC (--`d:real`--) THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC (--`y:real`--) THEN
        DISCH_TAC THEN REPEAT(FIRST_ASSUM MATCH_MP_TAC) THEN
        ASM_REWRITE_TAC[]], ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`l:real`--) MP_TAC) THEN
    DISCH_THEN(fn th => ASSUME_TAC th THEN SUBST_ALL_TAC(MATCH_MP DIFF_LMIN th))
    THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  SUBGOAL_THEN (--`!x. a <= x /\ x <= b ==> (f(x):real = f(b))`--) MP_TAC THENL
   [REPEAT(FIRST_ASSUM(UNDISCH_TAC o assert is_neg o concl)) THEN
    ASM_REWRITE_TAC[REAL_LT_LE] THEN REWRITE_TAC[DE_MORGAN_THM] THEN
    REPEAT (DISCH_THEN(DISJ_CASES_THEN2 (MP_TAC o SYM) MP_TAC) THEN
            DISCH_THEN(SUBST_ALL_TAC o AP_TERM (--`f:real->real`--))) THEN
    UNDISCH_TAC (--`(f:real->real) a = f b`--) THEN
    DISCH_THEN(fn th => SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
    (CONJ_TAC THENL
      [SUBGOAL_THEN (--`(f:real->real) b = M`--) SUBST1_TAC THENL
        [FIRST_ASSUM(ACCEPT_TAC o el 3 o CONJUNCTS),
         FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]],
       SUBGOAL_THEN (--`(f:real->real) b = m`--) SUBST1_TAC THENL
        [FIRST_ASSUM(ACCEPT_TAC o el 3 o CONJUNCTS),
         FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]),
    X_CHOOSE_TAC (--`x:real`--) (MATCH_MP REAL_MEAN (ASSUME (--`a < b`--))) THEN
    DISCH_TAC THEN EXISTS_TAC (--`x:real`--) THEN
    REWRITE_TAC[ASSUME (--`a < x /\ x < b`--)] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP INTERVAL_LEMMA) THEN
    DISCH_THEN(X_CHOOSE_THEN (--`d:real`--) STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (--`?l. ($diffl f l)(x) /\
        (?d. &0 < d /\ (!y. abs(x - y) < d ==> (f(y) = f(x))))`--) MP_TAC THENL
     [CONV_TAC(ONCE_DEPTH_CONV EXISTS_AND_CONV) THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM differentiable] THEN FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[],
        EXISTS_TAC (--`d:real`--) THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
        DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
        DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
        DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV THEN
        FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]],
      DISCH_THEN(X_CHOOSE_THEN (--`l:real`--) (fn th =>
       ASSUME_TAC th THEN SUBST_ALL_TAC(MATCH_MP DIFF_LCONST th))) THEN
      ASM_REWRITE_TAC[]]]);

(*---------------------------------------------------------------------------*)
(* Mean value theorem                                                        *)
(*---------------------------------------------------------------------------*)

val gfn = (--`\x. f(x) - (((f(b) - f(a)) / (b - a)) * x)`--);

val MVT_LEMMA = store_thm("MVT_LEMMA",
  (--`!(f:real->real) a b. ^gfn(a) = ^gfn(b)`--),
  REPEAT GEN_TAC THEN BETA_TAC THEN
  ASM_CASES_TAC (--`b:real = a`--) THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM REAL_SUB_0]) THEN
  MP_TAC(GENL [(--`x:real`--), (--`y:real`--)]
   (SPECL [(--`x:real`--), (--`y:real`--), (--`b - a`--)] REAL_EQ_RMUL)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fn th => GEN_REWR_TAC I [GSYM th]) THEN
  REWRITE_TAC[REAL_SUB_RDISTRIB, GSYM REAL_MUL_ASSOC] THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_DIV_RMUL th]) THEN
  GEN_REWR_TAC (RAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
  GEN_REWR_TAC (LAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
  REWRITE_TAC[real_sub, REAL_LDISTRIB, REAL_RDISTRIB] THEN
  REWRITE_TAC[GSYM REAL_NEG_LMUL, GSYM REAL_NEG_RMUL,
              REAL_NEG_ADD, REAL_NEGNEG] THEN
  REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN
  REWRITE_TAC[AC(REAL_ADD_ASSOC,REAL_ADD_SYM)
               (--`w + (x + (y + z)) = (y + w) + (x + z)`--),
              REAL_ADD_LINV, REAL_ADD_LID] THEN
  REWRITE_TAC[REAL_ADD_RID]);

val MVT = store_thm("MVT",
  (--`!f a b. a < b /\
           (!x. a <= x /\ x <= b ==> f contl x) /\
           (!x. a < x /\ x < b ==> f differentiable x)
        ==> ?l z. a < z /\ z < b /\ (f diffl l)(z) /\
            (f(b) - f(a) = (b - a) * l)`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [gfn, (--`a:real`--), (--`b:real`--)] ROLLE) THEN
  W(C SUBGOAL_THEN (fn t =>REWRITE_TAC[t]) o funpow 2 (fst o dest_imp) o snd) THENL
   [ASM_REWRITE_TAC[MVT_LEMMA] THEN BETA_TAC THEN
    CONJ_TAC THEN X_GEN_TAC (--`x:real`--) THENL
     [DISCH_TAC THEN CONV_TAC(ONCE_DEPTH_CONV HABS_CONV) THEN
      MATCH_MP_TAC CONT_SUB THEN CONJ_TAC THENL
       [CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[],
        CONV_TAC(ONCE_DEPTH_CONV HABS_CONV) THEN MATCH_MP_TAC CONT_MUL THEN
        REWRITE_TAC[CONT_CONST] THEN MATCH_MP_TAC DIFF_CONT THEN
        EXISTS_TAC (--`&1`--) THEN MATCH_ACCEPT_TAC DIFF_X],
      DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
      REWRITE_TAC[differentiable] THEN DISCH_THEN(X_CHOOSE_TAC (--`l:real`--)) THEN
      EXISTS_TAC (--`l - ((f(b) - f(a)) / (b - a))`--) THEN
      CONV_TAC(ONCE_DEPTH_CONV HABS_CONV) THEN MATCH_MP_TAC DIFF_SUB THEN
      CONJ_TAC THENL
       [CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN FIRST_ASSUM ACCEPT_TAC,
        CONV_TAC(ONCE_DEPTH_CONV HABS_CONV) THEN REWRITE_TAC[] THEN
        GEN_REWR_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC DIFF_CMUL THEN MATCH_ACCEPT_TAC DIFF_X]],
    ALL_TAC] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN DISCH_THEN(X_CHOOSE_THEN (--`z:real`--) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(curry op THEN (MAP_EVERY EXISTS_TAC
   [(--`((f(b) - f(a)) / (b - a))`--), (--`z:real`--)]) o MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(curry op THEN CONJ_TAC o MP_TAC) THENL
   [ALL_TAC, DISCH_THEN(K ALL_TAC) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC REAL_DIV_LMUL THEN REWRITE_TAC[REAL_SUB_0] THEN
    DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (--`a < a`--) THEN
    REWRITE_TAC[REAL_LT_REFL]] THEN
  SUBGOAL_THEN (--`((\x. ((f(b) - f(a)) / (b - a)) * x ) diffl
                      ((f(b) - f(a)) / (b - a)))(z)`--)
  (fn th => DISCH_THEN(MP_TAC o C CONJ th)) THENL
   [CONV_TAC(ONCE_DEPTH_CONV HABS_CONV) THEN REWRITE_TAC[] THEN
    GEN_REWR_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC DIFF_CMUL THEN REWRITE_TAC[DIFF_X], ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIFF_ADD) THEN BETA_TAC THEN
  REWRITE_TAC[REAL_SUB_ADD] THEN CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
  REWRITE_TAC[REAL_ADD_LID]);

(*---------------------------------------------------------------------------*)
(* Theorem that function is constant if its derivative is 0 over an interval.*)
(*                                                                           *)
(* We could have proved this directly by bisection; consider instantiating   *)
(* BOLZANO_LEMMA with                                                        *)
(*                                                                           *)
(*     fn (x,y) => f(y) - f(x) <= C * (y - x)                                *)
(*                                                                           *)
(* However the Rolle and Mean Value theorems are useful to have anyway       *)
(*---------------------------------------------------------------------------*)

val DIFF_ISCONST_END = store_thm("DIFF_ISCONST_END",
  (--`!f a b. a < b /\
           (!x. a <= x /\ x <= b ==> f contl x) /\
           (!x. a < x /\ x < b ==> (f diffl &0)(x))
        ==> (f b = f a)`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [(--`f:real->real`--), (--`a:real`--), (--`b:real`--)] MVT) THEN
  ASM_REWRITE_TAC[] THEN
  W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
   [GEN_TAC THEN REWRITE_TAC[differentiable] THEN
    DISCH_THEN(curry op THEN (EXISTS_TAC (--`&0`--)) o MP_TAC) THEN
    ASM_REWRITE_TAC[],
    DISCH_THEN(fn th => REWRITE_TAC[th])] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`l:real`--) (X_CHOOSE_THEN (--`x:real`--) MP_TAC)) THEN
  ONCE_REWRITE_TAC[TAUT_CONV (--`a /\ b /\ c /\ d = (a /\ b) /\ (c /\ d)`--)] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  DISCH_THEN(MP_TAC o CONJ (ASSUME (--`(f diffl l)(x)`--))) THEN
  DISCH_THEN(SUBST_ALL_TAC o MATCH_MP DIFF_UNIQ) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_MUL_RZERO, REAL_SUB_0]) THEN
  FIRST_ASSUM ACCEPT_TAC);

val DIFF_ISCONST = store_thm("DIFF_ISCONST",
  (--`!f a b. a < b /\
           (!x. a <= x /\ x <= b ==> f contl x) /\
           (!x. a < x /\ x < b ==> (f diffl &0)(x))
        ==> !x. a <= x /\ x <= b ==> (f x = f a)`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [(--`f:real->real`--), (--`a:real`--), (--`x:real`--)] DIFF_ISCONST_END) THEN
  DISJ_CASES_THEN MP_TAC (REWRITE_RULE[REAL_LE_LT] (ASSUME (--`a <= x`--))) THENL
   [DISCH_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THEN X_GEN_TAC (--`z:real`--) THEN STRIP_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`x:real`--),
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`x:real`--)] THEN
    ASM_REWRITE_TAC[],
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);

val DIFF_ISCONST_ALL = store_thm("DIFF_ISCONST_ALL",
  (--`!f. (!x. (f diffl &0)(x)) ==> (!x y. f(x) = f(y))`--),
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN (--`!x. f contl x`--) ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC DIFF_CONT THEN
    EXISTS_TAC (--`&0`--) THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  REPEAT GEN_TAC THEN REPEAT_TCL DISJ_CASES_THEN MP_TAC
   (SPECL [(--`x:real`--), (--`y:real`--)] REAL_LT_TOTAL) THENL
   [DISCH_THEN SUBST1_TAC THEN REFL_TAC,
    CONV_TAC(RAND_CONV SYM_CONV),
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC DIFF_ISCONST_END THEN
  ASM_REWRITE_TAC[]);

(*---------------------------------------------------------------------------*)
(* Boring lemma about distances                                              *)
(*---------------------------------------------------------------------------*)

val INTERVAL_ABS = store_thm("INTERVAL_ABS",
  (--`!x z d. (x - d) <= z /\ z <= (x + d) = abs(z - x) <= d`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[abs, REAL_LE_SUB_RADD] THEN EQ_TAC THENL
   [STRIP_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_LE_SUB_RADD, REAL_NEG_SUB] THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_REWRITE_TAC[],
    REWRITE_TAC[REAL_SUB_LE] THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_NEG_SUB, REAL_LE_SUB_RADD] THENL
     [ALL_TAC,
      RULE_ASSUM_TAC(MATCH_MP REAL_LT_IMP_LE o REWRITE_RULE[REAL_NOT_LE])] THEN
    DISCH_THEN(ASSUME_TAC o ONCE_REWRITE_RULE[REAL_ADD_SYM]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC (--`x + d`--), EXISTS_TAC (--`z + d`--)] THEN
    ASM_REWRITE_TAC[REAL_LE_RADD] THEN
    MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC (--`z:real`--), EXISTS_TAC (--`x:real`--)] THEN
    ASM_REWRITE_TAC[]]);

(*---------------------------------------------------------------------------*)
(* Continuous injection on an interval can't have a maximum in the middle    *)
(*---------------------------------------------------------------------------*)

val CONT_INJ_LEMMA = store_thm("CONT_INJ_LEMMA",
  (--`!f g x d. &0 < d /\
            (!z. abs(z - x) <= d ==> (g(f(z)) = z)) /\
            (!z. abs(z - x) <= d ==> f contl z) ==>
     ~(!z. abs(z - x) <= d ==> f(z) <= f(x))`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN IMP_RES_TAC REAL_LT_IMP_LE THEN
  DISCH_THEN(fn th => MAP_EVERY (MP_TAC o C SPEC th) [(--`x - d`--), (--`x + d`--)]) THEN
  REWRITE_TAC[REAL_ADD_SUB, REAL_SUB_SUB, ABS_NEG] THEN
  ASM_REWRITE_TAC[abs, REAL_LE_REFL] THEN
  DISCH_TAC THEN DISCH_TAC THEN DISJ_CASES_TAC
    (SPECL [(--`f(x - d):real`--), (--`f(x + d):real`--)] REAL_LE_TOTAL) THENL
   [MP_TAC(SPECL [(--`f:real->real`--), (--`x - d`--), (--`x:real`--), (--`f(x + d):real`--)] IVT) THEN
    ASM_REWRITE_TAC[REAL_LE_SUB_RADD, REAL_LE_ADDR] THEN
    W(C SUBGOAL_THEN MP_TAC o fst o dest_imp o dest_neg o snd) THENL
     [X_GEN_TAC (--`z:real`--) THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ONCE_REWRITE_TAC[GSYM ABS_NEG] THEN
      REWRITE_TAC[abs, REAL_SUB_LE] THEN
      ASM_REWRITE_TAC[REAL_NEG_SUB, REAL_SUB_LE, REAL_LE_SUB_RADD] THEN
      ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_REWRITE_TAC[],
      DISCH_THEN(fn th => REWRITE_TAC[th]) THEN
      DISCH_THEN(X_CHOOSE_THEN (--`z:real`--) STRIP_ASSUME_TAC) THEN
      FIRST_ASSUM(MP_TAC o AP_TERM (--`g:real->real`--)) THEN
      SUBGOAL_THEN (--`g((f:real->real) z) = z`--) SUBST1_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN
        ONCE_REWRITE_TAC[GSYM ABS_NEG] THEN
        REWRITE_TAC[abs, REAL_SUB_LE] THEN
        ASM_REWRITE_TAC[REAL_NEG_SUB, REAL_SUB_LE, REAL_LE_SUB_RADD] THEN
        ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
      SUBGOAL_THEN (--`g(f(x + d):real) = x + d`--) SUBST1_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[REAL_ADD_SUB] THEN
        ASM_REWRITE_TAC[abs, REAL_LE_REFL], ALL_TAC] THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`x:real`--) THEN
      ASM_REWRITE_TAC[REAL_LT_ADDR]],
    MP_TAC(SPECL [(--`f:real->real`--), (--`x:real`--), (--`x + d`--), (--`f(x - d):real`--)] IVT2) THEN
    ASM_REWRITE_TAC[REAL_LE_SUB_RADD, REAL_LE_ADDR] THEN
    W(C SUBGOAL_THEN MP_TAC o fst o dest_imp o dest_neg o snd) THENL
     [X_GEN_TAC (--`z:real`--) THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[abs, REAL_SUB_LE, REAL_LE_SUB_RADD] THEN
      ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_REWRITE_TAC[],
      DISCH_THEN(fn th => REWRITE_TAC[th]) THEN
      DISCH_THEN(X_CHOOSE_THEN (--`z:real`--) STRIP_ASSUME_TAC) THEN
      FIRST_ASSUM(MP_TAC o AP_TERM (--`g:real->real`--)) THEN
      SUBGOAL_THEN (--`g((f:real->real) z) = z`--) SUBST1_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[abs, REAL_SUB_LE, REAL_LE_SUB_RADD] THEN
        ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
      SUBGOAL_THEN (--`g(f(x - d):real) = x - d`--) SUBST1_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[REAL_SUB_SUB, ABS_NEG] THEN
        ASM_REWRITE_TAC[abs, REAL_LE_REFL], ALL_TAC] THEN
      REWRITE_TAC[] THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
      MATCH_MP_TAC REAL_LT_IMP_NE THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (--`x:real`--) THEN
      ASM_REWRITE_TAC[REAL_LT_SUB_RADD, REAL_LT_ADDR]]]);

(*---------------------------------------------------------------------------*)
(* Similar version for lower bound                                           *)
(*---------------------------------------------------------------------------*)

val CONT_INJ_LEMMA2 = store_thm("CONT_INJ_LEMMA2",
  (--`!f g x d. &0 < d /\
            (!z. abs(z - x) <= d ==> (g(f(z)) = z)) /\
            (!z. abs(z - x) <= d ==> f contl z) ==>
     ~(!z. abs(z - x) <= d ==> f(x) <= f(z))`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [(--`\x:real. ~(f x)`--), (--`\y. (g(~y):real)`--), (--`x:real`--), (--`d:real`--)]
    CONT_INJ_LEMMA) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[REAL_NEGNEG, REAL_LE_NEG] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CONT_NEG THEN
  FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC);

(*---------------------------------------------------------------------------*)
(* Show there's an interval surrounding f(x) in                              *)
(*  f[[x - d, x + d]]                                          *)
(*---------------------------------------------------------------------------*)

val CONT_INJ_RANGE = store_thm("CONT_INJ_RANGE",
  (--`!f g x d.  &0 < d /\
            (!z. abs(z - x) <= d ==> (g(f(z)) = z)) /\
            (!z. abs(z - x) <= d ==> f contl z) ==>
        ?e. &0 < e /\
            (!y. abs(y - f(x)) <= e ==> ?z. abs(z - x) <= d /\ (f z = y))`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN IMP_RES_TAC REAL_LT_IMP_LE THEN
  MP_TAC(SPECL [(--`f:real->real`--), (--`x - d`--), (--`x + d`--)] CONT_ATTAINS_ALL) THEN
  ASM_REWRITE_TAC[INTERVAL_ABS, REAL_LE_SUB_RADD] THEN
  ASM_REWRITE_TAC[GSYM REAL_ADD_ASSOC, REAL_LE_ADDR, REAL_LE_DOUBLE] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`L:real`--) (X_CHOOSE_THEN (--`M:real`--) MP_TAC)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN (--`L <= f(x:real) /\ f(x) <= M`--) STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL, ABS_0], ALL_TAC] THEN
  SUBGOAL_THEN (--`L < f(x:real) /\ f(x:real) < M`--) STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_REWRITE_TAC[REAL_LT_LE] THENL
     [DISCH_THEN SUBST_ALL_TAC THEN (MP_TAC o C SPECL CONT_INJ_LEMMA2)
        [(--`f:real->real`--), (--`g:real->real`--), (--`x:real`--), (--`d:real`--)],
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN (MP_TAC o C SPECL CONT_INJ_LEMMA)
        [(--`f:real->real`--), (--`g:real->real`--), (--`x:real`--), (--`d:real`--)]] THEN
    ASM_REWRITE_TAC[] THEN GEN_TAC THEN
    DISCH_THEN(fn t => FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP th t] THEN NO_TAC)),
    MP_TAC(SPECL [(--`f(x:real) - L`--), (--`M - f(x:real)`--)] REAL_DOWN2) THEN
    ASM_REWRITE_TAC[REAL_SUB_LT] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`e:real`--) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (--`e:real`--) THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM INTERVAL_ABS] THEN
    REWRITE_TAC[REAL_LE_SUB_RADD] THEN ONCE_REWRITE_TAC[GSYM CONJ_ASSOC] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC (--`abs(y - f(x:real)) <= e`--) THEN
    REWRITE_TAC[GSYM INTERVAL_ABS] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`f(x:real) - e`--) THEN
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[REAL_LE_SUB_LADD] THEN
      ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
      REWRITE_TAC[GSYM REAL_LE_SUB_LADD],
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC (--`f(x:real) + (M - f(x))`--) THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`f(x:real) + e`--) THEN
        ASM_REWRITE_TAC[REAL_LE_LADD],
        REWRITE_TAC[REAL_SUB_ADD2, REAL_LE_REFL]]] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]]);

(*---------------------------------------------------------------------------*)
(* Continuity of inverse function                                            *)
(*---------------------------------------------------------------------------*)

val CONT_INVERSE = store_thm("CONT_INVERSE",
  (--`!f g x d. &0 < d /\
             (!z. abs(z - x) <= d ==> (g(f(z)) = z)) /\
             (!z. abs(z - x) <= d ==> f contl z)
        ==> g contl (f x)`--),
  REPEAT STRIP_TAC THEN REWRITE_TAC[contl, LIM] THEN
  X_GEN_TAC (--`a:real`--) THEN DISCH_TAC THEN
  MP_TAC(SPECL [(--`a:real`--), (--`d:real`--)] REAL_DOWN2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`e:real`--) STRIP_ASSUME_TAC) THEN
  IMP_RES_TAC REAL_LT_IMP_LE THEN
  SUBGOAL_THEN (--`!z. abs(z - x) <= e ==> (g(f z :real) = z)`--) ASSUME_TAC THENL
   [X_GEN_TAC (--`z:real`--) THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`e:real`--) THEN ASM_REWRITE_TAC[],
    ALL_TAC] THEN
  SUBGOAL_THEN (--`!z. abs(z - x) <= e ==> (f contl z)`--) ASSUME_TAC THENL
   [X_GEN_TAC (--`z:real`--) THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`e:real`--) THEN ASM_REWRITE_TAC[],
    ALL_TAC] THEN
  UNDISCH_TAC (--`!z. abs(z - x) <= d ==> (g(f z :real) = z)`--) THEN
  UNDISCH_TAC (--`!z. abs(z - x) <= d ==> (f contl z)`--) THEN
  DISCH_THEN(K ALL_TAC) THEN DISCH_THEN(K ALL_TAC) THEN
  (MP_TAC o C SPECL CONT_INJ_RANGE)
    [(--`f:real->real`--), (--`g:real->real`--), (--`x:real`--), (--`e:real`--)] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`k:real`--) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC (--`k:real`--) THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC (--`h:real`--) THEN BETA_TAC THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE)) THEN
  REWRITE_TAC[GSYM ABS_NZ] THEN DISCH_TAC THEN
  FIRST_ASSUM(fn th => MP_TAC(SPEC (--`f(x:real) + h`--) th) THEN
    REWRITE_TAC[REAL_ADD_SUB, ASSUME (--`abs(h) <= k`--)] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`z:real`--) STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_eq o concl) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`e:real`--) THEN
  SUBGOAL_THEN (--`(g((f:real->real)(z)) = z) /\ (g(f(x)) = x)`--)
    (fn t => ASM_REWRITE_TAC[t]) THEN CONJ_TAC THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_SUB_REFL, ABS_0]);

(*---------------------------------------------------------------------------*)
(* Differentiability of inverse function                                     *)
(*---------------------------------------------------------------------------*)

val DIFF_INVERSE = store_thm("DIFF_INVERSE",
  (--`!f g l x d. &0 < d /\
               (!z. abs(z - x) <= d ==> (g(f(z)) = z)) /\
               (!z. abs(z - x) <= d ==> f contl z) /\
               (f diffl l)(x) /\
               ~(l = &0)
        ==> (g diffl (inv l))(f x)`--),
  REPEAT STRIP_TAC THEN UNDISCH_TAC (--`(f diffl l)(x)`--) THEN
  DISCH_THEN(fn th => ASSUME_TAC(MATCH_MP DIFF_CONT th) THEN MP_TAC th) THEN
  REWRITE_TAC[DIFF_CARAT] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`h:real->real`--) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC (--`\y. if (y = f(x)) then inv(h(g y))
                     else (g(y) - g(f(x:real))) / (y - f(x))`--) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC (--`z:real`--) THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL, REAL_MUL_RZERO] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    ASM_REWRITE_TAC[REAL_SUB_0],
    ALL_TAC,
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REPEAT AP_TERM_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[REAL_SUB_REFL, ABS_0] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[CONTL_LIM] THEN BETA_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN (--`g((f:real->real)(x)) = x`--) ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[REAL_SUB_REFL, ABS_0] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE, ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LIM_TRANSFORM THEN
  EXISTS_TAC (--`\y:real. inv(h(g(y):real))`--) THEN
  BETA_TAC THEN CONJ_TAC THENL
   [ALL_TAC,
    (SUBST1_TAC o SYM o ONCE_DEPTH_CONV BETA_CONV)
      (--`\y. inv((\y:real. h(g(y):real)) y)`--) THEN
    MATCH_MP_TAC LIM_INV THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN (--`(\y:real. h(g(y):real)) contl (f(x:real))`--) MP_TAC THENL
     [MATCH_MP_TAC CONT_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONT_INVERSE THEN EXISTS_TAC (--`d:real`--),
      REWRITE_TAC[CONTL_LIM] THEN BETA_TAC] THEN
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN (--`?e. &0 < e /\
                    !y. &0 < abs(y - f(x:real)) /\
                        abs(y - f(x:real)) < e ==>
                            (f(g(y)) = y) /\ ~(h(g(y)) = &0)`--)
  STRIP_ASSUME_TAC THENL
   [ALL_TAC,
    REWRITE_TAC[LIM] THEN X_GEN_TAC (--`k:real`--) THEN DISCH_TAC THEN
    EXISTS_TAC (--`e:real`--) THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC (--`y:real`--) THEN
    DISCH_THEN(fn th => FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th) THEN
      ASSUME_TAC(REWRITE_RULE[GSYM ABS_NZ, REAL_SUB_0] (CONJUNCT1 th))) THEN
    BETA_TAC THEN ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
    SUBGOAL_THEN (--`y - f(x) = h(g(y)) * (g(y) - x)`--)
                 SUBST1_TAC
    THENL
     [FIRST_ASSUM(fn th => GEN_REWR_TAC RAND_CONV [GSYM th]) THEN
      REWRITE_TAC[ASSUME (--`f((g:real->real)(y)) = y`--)],
      UNDISCH_TAC (--`&0 < k`--) THEN
      MATCH_MP_TAC(TAUT_CONV (--`(a = b) ==> a ==> b`--)) THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN REWRITE_TAC[ABS_ZERO, REAL_SUB_0]] THEN
    SUBGOAL_THEN (--`~(g(y:real) - x = &0)`--) ASSUME_TAC THENL
     [REWRITE_TAC[REAL_SUB_0] THEN
      DISCH_THEN(MP_TAC o AP_TERM (--`f:real->real`--)) THEN
      ASM_REWRITE_TAC[], REWRITE_TAC[real_div]] THEN
    SUBGOAL_THEN (--`inv((h(g(y))) * (g(y:real) - x)) =
      inv(h(g(y))) * inv(g(y) - x)`--) SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_INV_MUL THEN ASM_REWRITE_TAC[],
      REWRITE_TAC[REAL_MUL_ASSOC] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN
      GEN_REWR_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[]]] THEN
  SUBGOAL_THEN
    (--`?e. &0 < e /\
         !y. &0 < abs(y - f(x:real)) /\
             abs(y - f(x)) < e ==> (f(g(y)) = y)`--)
  (X_CHOOSE_THEN (--`c:real`--) STRIP_ASSUME_TAC) THENL
   [MP_TAC(SPECL [(--`f:real->real`--), (--`g:real->real`--),
                  (--`x:real`--), (--`d:real`--)] CONT_INJ_RANGE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`e:real`--) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (--`e:real`--) THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC (--`y:real`--) THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
    DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN(X_CHOOSE_THEN (--`z:real`--) STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC (--`(f:real->real)(z) = y`--) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  SUBGOAL_THEN
    (--`?e. &0 < e /\
         !y. &0 < abs(y - f(x:real)) /\
             abs(y - f(x)) < e
             ==> ~((h:real->real)(g(y)) = &0)`--)
  (X_CHOOSE_THEN (--`b:real`--) STRIP_ASSUME_TAC) THENL
   [ALL_TAC,
    MP_TAC(SPECL [(--`b:real`--), (--`c:real`--)] REAL_DOWN2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN (--`e:real`--) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (--`e:real`--) THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC (--`y:real`--) THEN STRIP_TAC THEN CONJ_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC (--`e:real`--) THEN
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN (--`(\y. h(g(y:real):real)) contl (f(x:real))`--) MP_TAC THENL
   [MATCH_MP_TAC CONT_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONT_INVERSE THEN EXISTS_TAC (--`d:real`--) THEN
    ASM_REWRITE_TAC[], ALL_TAC] THEN
  REWRITE_TAC[CONTL_LIM, LIM] THEN
  DISCH_THEN(MP_TAC o SPEC (--`abs(l)`--)) THEN
  ASM_REWRITE_TAC[GSYM ABS_NZ] THEN
  (****begin new*****)
  REWRITE_TAC[ABS_NZ] THEN
  (****end new******)
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`e:real`--) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC (--`e:real`--) THEN ASM_REWRITE_TAC[ABS_NZ] THEN
  X_GEN_TAC (--`y:real`--) THEN
  DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  REWRITE_TAC[GSYM ABS_NZ] THEN
  CONV_TAC CONTRAPOS_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_SUB_LZERO, ABS_NEG, REAL_LT_REFL]);


val DIFF_INVERSE_LT = store_thm("DIFF_INVERSE_LT",
  Term`!f g l x d. &0 < d /\
               (!z. abs(z - x) < d ==> (g(f(z)) = z)) /\
               (!z. abs(z - x) < d ==> f contl z) /\
               (f diffl l)(x) /\
               ~(l = &0)
        ==> (g diffl (inv l))(f x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIFF_INVERSE THEN
  EXISTS_TAC (Term `d / &2`) THEN ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (Term `d / &2`) THEN
  ASM_REWRITE_TAC[REAL_LT_HALF2]);;

(*---------------------------------------------------------------------------*)
(* Lemma about introducing a closed ball in an open interval                 *)
(*---------------------------------------------------------------------------*)

val INTERVAL_CLEMMA = store_thm("INTERVAL_CLEMMA",
  (--`!a b x. a < x /\ x < b ==>
        ?d. &0 < d /\ !y. abs(y - x) <= d ==> a < y /\ y < b`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [(--`x - a`--), (--`b - x`--)] REAL_DOWN2) THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN ASM_REWRITE_TAC[REAL_LT_SUB_LADD] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`d:real`--) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC (--`d:real`--) THEN
  ASM_REWRITE_TAC[GSYM INTERVAL_ABS, REAL_LE_SUB_RADD] THEN
  X_GEN_TAC (--`y:real`--) THEN STRIP_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN (--`(d + a) < d + y`--) MP_TAC THENL
     [GEN_REWR_TAC RAND_CONV  [REAL_ADD_SYM] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC (--`x:real`--) THEN ASM_REWRITE_TAC[],
      REWRITE_TAC[REAL_LT_LADD]],
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC (--`x + d`--) THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    ASM_REWRITE_TAC[]]);

(*---------------------------------------------------------------------------*)
(* Alternative version of inverse function theorem                           *)
(*---------------------------------------------------------------------------*)

val DIFF_INVERSE_OPEN = store_thm("DIFF_INVERSE_OPEN",
  (--`!f g l a x b.
        a < x /\
        x < b /\
        (!z. a < z /\ z < b ==> (g(f(z)) = z) /\ f contl z) /\
        (f diffl l)(x) /\
        ~(l = &0)
        ==> (g diffl (inv l))(f x)`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC DIFF_INVERSE THEN
  MP_TAC(SPECL [(--`a:real`--), (--`b:real`--),
                (--`x:real`--)] INTERVAL_CLEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN (--`d:real`--) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC (--`d:real`--) THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN GEN_TAC THEN
  DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  DISCH_THEN(fn th => FIRST_ASSUM(fn t => REWRITE_TAC[MATCH_MP t th])));


val _ = export_theory();


end;
