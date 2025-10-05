(*===========================================================================*)
(* Theory of limits, continuity and differentiation of real->real functions  *)
(*===========================================================================*)
Theory lim
Ancestors
  pair arithmetic num prim_rec real metric nets combin pred_set
  topology real_topology derivative seq
Libs
  numLib reduceLib pairLib jrhUtils realLib mesonLib hurdUtils


val _ = ParseExtras.temp_loose_equality()

val _ = Parse.reveal "B";

val tendsto = netsTheory.tendsto;   (* conflict with real_topologyTheory.tendsto *)
val EXACT_CONV = jrhUtils.EXACT_CONV; (* there's one also in hurdUtils *)

(*---------------------------------------------------------------------------*)
(* Specialize nets theorems to the pointwise limit of real->real functions   *)
(*---------------------------------------------------------------------------*)

Definition tends_real_real :
    (tends_real_real f l)(x0) =
        (f tends l)(mtop(mr1),tendsto(mr1,x0))
End

val _ = add_infix("->", 250, HOLgrammars.RIGHT)
val _ = overload_on ("->", ``tends_real_real``);

Theorem LIM:
   !f y0 x0. (f -> y0)(x0) =
        !e. &0 < e ==>
            ?d. &0 < d /\ !x. &0 < abs(x - x0) /\ abs(x - x0) < d ==>
                abs(f(x) - y0) < e
Proof
  REPEAT GEN_TAC THEN
  REWRITE_TAC[tends_real_real, MATCH_MP LIM_TENDS2 (SPEC “x0:real” MR1_LIMPT)]
  THEN REWRITE_TAC[MR1_DEF] THEN
  GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ABS_SUB] THEN
  REFL_TAC
QED

(* connection to real_topologyTheory *)
Theorem LIM_AT_LIM :
    !f l a. (f --> l) (at a) <=> (f -> l)(a)
Proof
    REWRITE_TAC [LIM_AT, LIM, dist]
QED

Theorem LIM_CONST :
    !k x. ((\x. k) -> k)(x)
Proof
    rw [GSYM LIM_AT_LIM, real_topologyTheory.LIM_CONST]
QED

Theorem LIM_ADD :
   !f g l m x. (f -> l)(x) /\ (g -> m)(x) ==>
      ((\x. f(x) + g(x)) -> (l + m))(x)
Proof
    rw [GSYM LIM_AT_LIM, real_topologyTheory.LIM_ADD]
QED

Theorem LIM_MUL :
   !f g l m x. (f -> l)(x) /\ (g -> m)(x) ==>
      ((\x. f(x) * g(x)) -> (l * m))(x)
Proof
    rw [GSYM LIM_AT_LIM, real_topologyTheory.LIM_MUL]
QED

Theorem LIM_NEG :
   !f l x. (f -> l)(x) = ((\x. ~(f(x))) -> ~l)(x)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_real_real] THEN
  MATCH_MP_TAC NET_NEG THEN MATCH_ACCEPT_TAC DORDER_TENDSTO
QED

Theorem LIM_INV :
   !f l x. (f -> l)(x) /\ ~(l = &0) ==>
        ((\x. inv(f(x))) -> inv l)(x)
Proof
    rw [GSYM LIM_AT_LIM,
        REWRITE_RULE [o_DEF] real_topologyTheory.LIM_INV]
QED

Theorem LIM_SUB :
   !f g l m x. (f -> l)(x) /\ (g -> m)(x) ==>
      ((\x. f(x) - g(x)) -> (l - m))(x)
Proof
    rw [GSYM LIM_AT_LIM, real_topologyTheory.LIM_SUB]
QED

Theorem LIM_DIV :
   !f g l m x. (f -> l)(x) /\ (g -> m)(x) /\ ~(m = &0) ==>
      ((\x. f(x) / g(x)) -> (l / m))(x)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_real_real] THEN
  MATCH_MP_TAC NET_DIV THEN MATCH_ACCEPT_TAC DORDER_TENDSTO
QED

Theorem LIM_NULL :
   !f l x. (f -> l)(x) = ((\x. f(x) - l) -> &0)(x)
Proof
    rw [GSYM LIM_AT_LIM, Once real_topologyTheory.LIM_NULL]
QED

(*---------------------------------------------------------------------------*)
(* One extra theorem is handy                                                *)
(*---------------------------------------------------------------------------*)

Theorem LIM_X:
   !x0. ((\x. x) -> x0)(x0)
Proof
  GEN_TAC THEN REWRITE_TAC[LIM] THEN X_GEN_TAC “e:real” THEN
  DISCH_TAC THEN EXISTS_TAC “e:real” THEN ASM_REWRITE_TAC[] THEN
  BETA_TAC THEN GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
QED

(*---------------------------------------------------------------------------*)
(* Uniqueness of limit                                                       *)
(*---------------------------------------------------------------------------*)

Theorem LIM_UNIQ:
   !f l m x. (f -> l)(x) /\ (f -> m)(x) ==> (l = m)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[tends_real_real] THEN
  MATCH_MP_TAC MTOP_TENDS_UNIQ THEN
  MATCH_ACCEPT_TAC DORDER_TENDSTO
QED

(*---------------------------------------------------------------------------*)
(* Show that limits are equal when functions are equal except at limit point *)
(*---------------------------------------------------------------------------*)

Theorem LIM_EQUAL :
   !f g l x0. (!x. ~(x = x0) ==> (f x = g x)) ==> ((f -> l)(x0) = (g -> l)(x0))
Proof
    rw [GSYM LIM_AT_LIM]
 >> MATCH_MP_TAC (SIMP_RULE std_ss [ETA_THM] LIM_CONG_AT)
 >> rw []
QED

(*---------------------------------------------------------------------------*)
(* A more general theorem about rearranging the body of a limit              *)
(*---------------------------------------------------------------------------*)

Theorem LIM_TRANSFORM :
   !f g x0 l. ((\x. f(x) - g(x)) -> &0)(x0) /\ (g -> l)(x0)
        ==> (f -> l)(x0)
Proof
    rw [GSYM LIM_AT_LIM]
 >> Know ‘(f --> l) (at x0) <=> (g --> l) (at x0)’
 >- (MATCH_MP_TAC LIM_TRANSFORM_EQ >> art [])
 >> rw []
QED

(*---------------------------------------------------------------------------*)
(* Define differentiation and continuity                                     *)
(*---------------------------------------------------------------------------*)

val diffl = new_infixr_definition("diffl",
“($diffl f l)(x) = ((\h. (f(x + h) - f(x)) / h) -> l)(&0)”,
  750);

(* connection with derivativeTheory, added by Chun Tian *)
Theorem diffl_has_vector_derivative :
    !f l x. ($diffl f l)(x) <=> (f has_vector_derivative l) (at x)
Proof
    rpt GEN_TAC
 >> RW_TAC std_ss [diffl, has_vector_derivative, has_derivative_at, LIM_AT_LIM]
 >> ASSUME_TAC (Q.SPEC ‘l’ (ONCE_REWRITE_RULE [REAL_MUL_COMM] LINEAR_SCALING))
 >> EQ_TAC >> RW_TAC real_ss [LIM] (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      Q.PAT_X_ASSUM ‘!e. 0 < e ==> P’ (MP_TAC o (Q.SPEC ‘e’)) >> RW_TAC std_ss [] \\
      Q.EXISTS_TAC ‘d’ >> RW_TAC std_ss [] \\
      Q.PAT_X_ASSUM ‘!h. 0 < abs h /\ abs h < d ==> P’ (MP_TAC o (Q.SPEC ‘y - x’)) \\
      RW_TAC real_ss [] \\
     ‘y - x <> 0’ by (CCONTR_TAC >> fs []) \\
     ‘inv (abs (y - x)) = abs (inv (y - x))’ by PROVE_TAC [ABS_INV] >> POP_ORW \\
      Know ‘abs (abs (inv (y - x)) * (f y - (f x + (y - x) * l))) =
            abs (inv (y - x) * (f y - (f x + (y - x) * l)))’
      >- (RW_TAC real_ss [ABS_MUL, ABS_ABS]) >> Rewr' \\
      Suff ‘inv (y - x) * (f y - (f x + (y - x) * l)) = (f y - f x) / (y - x) - l’
      >- RW_TAC std_ss [] \\
      ONCE_REWRITE_TAC [REAL_MUL_COMM] \\
     ‘f y - (f x + (y - x) * l) = (f y - f x) - l * (y - x)’ by REAL_ARITH_TAC \\
      POP_ORW >> REWRITE_TAC [real_div] \\
      GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [REAL_SUB_RDISTRIB] \\
      rw [],
      (* goal 2 (of 2) *)
      Q.PAT_X_ASSUM ‘!e. 0 < e ==> P’ (MP_TAC o (Q.SPEC ‘e’)) >> RW_TAC std_ss [] \\
      Q.EXISTS_TAC ‘d’ >> RW_TAC std_ss [] \\
      Q.PAT_X_ASSUM ‘!y. 0 < abs (y - x) /\ abs (y - x) < d ==> P’
        (MP_TAC o (Q.SPEC ‘x + h’)) >> RW_TAC real_ss [] \\
     ‘h <> 0’ by PROVE_TAC [ABS_NZ] \\
     ‘inv (abs h) = abs (inv h)’ by PROVE_TAC [ABS_INV] \\
      POP_ASSUM (FULL_SIMP_TAC std_ss o wrap) \\
      Know ‘abs (abs (inv h) * (f (x + h) - (f x + h * l))) =
            abs (inv h * (f (x + h) - (f x + h * l)))’
      >- (RW_TAC real_ss [ABS_MUL, ABS_ABS]) \\
      DISCH_THEN (FULL_SIMP_TAC std_ss o wrap) \\
      Suff ‘(f (x + h) - f x) / h - l = inv h * (f (x + h) - (f x + h * l))’
      >- RW_TAC std_ss [] \\
      ONCE_REWRITE_TAC [REAL_MUL_COMM] \\
     ‘f (x + h) - (f x + h * l) = f (x + h) - f x - l * h’ by REAL_ARITH_TAC \\
      POP_ORW >> REWRITE_TAC [real_div] \\
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [REAL_SUB_RDISTRIB] \\
      rw [] ]
QED

(* |- !f l x. (f diffl l) x <=> (f has_derivative (\x. x * l)) (at x) *)
Theorem diffl_has_derivative =
    REWRITE_RULE [has_vector_derivative] diffl_has_vector_derivative

Theorem diffl_has_derivative' :
    !f l x. (f diffl l) x <=> (f has_derivative ($* l)) (at x)
Proof
    rw [diffl_has_derivative]
 >> Suff ‘(\x. l * x) = $* l’ >- rw []
 >> rw [FUN_EQ_THM, Once REAL_MUL_COMM]
QED

val contl = new_infixr_definition("contl",
  “$contl f x = ((\h. f(x + h)) -> f(x))(&0)”, 750);

(* connection with real_topologyTheory *)
Theorem contl_eq_continuous_at :
    !f x. f contl x <=> f continuous (at x)
Proof
    RW_TAC real_ss [contl, CONTINUOUS_AT, LIM_AT_LIM, LIM]
 >> EQ_TAC >> RW_TAC std_ss []
 >| [ (* goal 1 (of 2) *)
      Q.PAT_X_ASSUM ‘!e. 0 < e ==> P’ (MP_TAC o (Q.SPEC ‘e’)) \\
      RW_TAC std_ss [] \\
      Q.EXISTS_TAC ‘d’ >> RW_TAC std_ss [] \\
      Q.PAT_X_ASSUM ‘!h. 0 < abs h /\ abs h < d ==> P’ (MP_TAC o (Q.SPEC ‘x' - x’)) \\
      RW_TAC real_ss [],
      (* goal 2 (of 2) *)
      Q.PAT_X_ASSUM ‘!e. 0 < e ==> P’ (MP_TAC o (Q.SPEC ‘e’)) \\
      RW_TAC std_ss [] \\
      Q.EXISTS_TAC ‘d’ >> RW_TAC std_ss [] \\
      Q.PAT_X_ASSUM ‘!x'. 0 < abs (x' - x) /\ abs (x' - x) < d ==> P’
        (MP_TAC o (Q.SPEC ‘x + h’)) \\
      RW_TAC real_ss [] ]
QED

val _ = hide "differentiable";

(* cf. derivativeTheory.differentiable *)
val differentiable = new_infixr_definition("differentiable",
  “$differentiable f x = ?l. (f diffl l)(x)”, 750);

Theorem differentiable_has_vector_derivative :
    !f x. f differentiable x <=> ?l. (f has_vector_derivative l) (at x)
Proof
    rw [differentiable, diffl_has_vector_derivative]
QED

(* The equivalence between ‘differentiable’ and ‘derivative$differentiable’ *)
Theorem differentiable_alt :
    !f x. f differentiable x <=> derivative$differentiable f (at x)
Proof
    rw [differentiable, diffl_has_derivative, derivativeTheory.differentiable]
 >> EQ_TAC
 >- (STRIP_TAC \\
     Q.EXISTS_TAC ‘\x. l * x’ >> rw [])
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘g’ ASSUME_TAC)
 >> ‘linear g’ by PROVE_TAC [has_derivative]
 >> ‘?l. g = \x. l * x’ by METIS_TAC [linear_repr]
 >> Q.EXISTS_TAC ‘l’ >> rw []
QED

(*---------------------------------------------------------------------------*)
(* Derivative is unique                                                      *)
(*---------------------------------------------------------------------------*)

Theorem DIFF_UNIQ:
   !f l m x. (f diffl l)(x) /\ (f diffl m)(x) ==> (l = m)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[diffl] THEN
  MATCH_ACCEPT_TAC LIM_UNIQ
QED

(*---------------------------------------------------------------------------*)
(* Differentiability implies continuity                                      *)
(*---------------------------------------------------------------------------*)

Theorem DIFF_CONT :
    !f l x. ($diffl f l)(x) ==> $contl f x
Proof
    rw [contl_eq_continuous_at, diffl_has_derivative]
 >> MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT
 >> rw [derivativeTheory.differentiable]
 >> Q.EXISTS_TAC ‘\x. l * x’ >> art []
QED

(*---------------------------------------------------------------------------*)
(* Alternative definition of continuity                                      *)
(*---------------------------------------------------------------------------*)

Theorem CONTL_LIM :
    !f x. f contl x = (f -> f(x))(x)
Proof
    rw [contl_eq_continuous_at, CONTINUOUS_AT, LIM_AT_LIM]
QED

(*---------------------------------------------------------------------------*)
(* Alternative (Carathe'odory) definition of derivative                      *)
(*---------------------------------------------------------------------------*)

Theorem DIFF_CARAT:
   !f l x. (f diffl l)(x) =
      ?g. (!z. f(z) - f(x) = g(z) * (z - x)) /\ g contl x /\ (g(x) = l)
Proof
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [EXISTS_TAC “\z. if (z = x) then l
                       else (f(z) - f(x)) / (z - x)” THEN
    BETA_TAC THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC “z:real” THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[REAL_SUB_REFL, REAL_MUL_RZERO] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
      ASM_REWRITE_TAC[REAL_SUB_0],
      POP_ASSUM MP_TAC THEN MATCH_MP_TAC(TAUT_CONV “(a = b) ==> a ==> b”) THEN
      REWRITE_TAC[diffl, contl] THEN BETA_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC LIM_EQUAL THEN GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
      ASM_REWRITE_TAC[REAL_ADD_RID_UNIQ, REAL_ADD_SUB]],
    POP_ASSUM(X_CHOOSE_THEN “g:real->real” STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(UNDISCH_TAC o assert is_eq o concl) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN UNDISCH_TAC “g contl x” THEN
    ASM_REWRITE_TAC[contl, diffl, REAL_ADD_SUB] THEN
    MATCH_MP_TAC(TAUT_CONV “(a = b) ==> a ==> b”) THEN
    MATCH_MP_TAC LIM_EQUAL THEN GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN
    REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC] THEN
    FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_MUL_RINV th]) THEN
    REWRITE_TAC[REAL_MUL_RID]]
QED

(*---------------------------------------------------------------------------*)
(* Simple combining theorems for continuity, including composition           *)
(*---------------------------------------------------------------------------*)

Theorem CONT_CONST:
   !k x. $contl (\x. k) x
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTL_LIM] THEN
  MATCH_ACCEPT_TAC LIM_CONST
QED

Theorem CONT_ADD:
   !f g x. $contl f x /\ $contl g x ==> $contl (\x. f(x) + g(x)) x
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTL_LIM] THEN BETA_TAC THEN
  MATCH_ACCEPT_TAC LIM_ADD
QED

Theorem CONT_MUL:
   !f g x. $contl f x /\ $contl g x ==> $contl (\x. f(x) * g(x)) x
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTL_LIM] THEN BETA_TAC THEN
  MATCH_ACCEPT_TAC LIM_MUL
QED

Theorem CONT_NEG:
   !f x. $contl f x ==> $contl (\x. ~(f(x))) x
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTL_LIM] THEN BETA_TAC THEN
  REWRITE_TAC[GSYM LIM_NEG]
QED

Theorem CONT_INV:
   !f x. $contl f x /\ ~(f x = &0) ==> $contl (\x. inv(f(x))) x
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTL_LIM] THEN BETA_TAC THEN
  MATCH_ACCEPT_TAC LIM_INV
QED

Theorem CONT_SUB:
   !f g x. $contl f x /\ $contl g x ==> $contl (\x. f(x) - g(x)) x
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTL_LIM] THEN BETA_TAC THEN
  MATCH_ACCEPT_TAC LIM_SUB
QED

Theorem CONT_DIV:
   !f g x. $contl f x /\ $contl g x /\ ~(g x = &0) ==>
             $contl (\x. f(x) / g(x)) x
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTL_LIM] THEN BETA_TAC THEN
  MATCH_ACCEPT_TAC LIM_DIV
QED

(* ------------------------------------------------------------------------- *)
(* Composition of continuous functions is continuous.                        *)
(* ------------------------------------------------------------------------- *)

Theorem CONT_COMPOSE :
   !f g x. f contl x /\ g contl (f x) ==> (\x. g(f x)) contl x
Proof
    rw [contl_eq_continuous_at]
 >> MATCH_MP_TAC (REWRITE_RULE [o_DEF] CONTINUOUS_AT_COMPOSE) >> art []
QED

(*---------------------------------------------------------------------------*)
(* Intermediate Value Theorem (we prove contrapositive by bisection)         *)
(*---------------------------------------------------------------------------*)

Theorem IVT :
    !f a b y. a <= b /\ (f(a) <= y /\ y <= f(b)) /\
             (!x. a <= x /\ x <= b ==> f contl x)
        ==> (?x. a <= x /\ x <= b /\ (f(x) = y))
Proof
    rw [contl_eq_continuous_at]
 >> fs [CONJ_ASSOC, GSYM IN_INTERVAL]
 >> ‘f continuous_on interval [a,b]’
      by (MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON >> rw [])
 >> MATCH_MP_TAC CONTINUOUS_ON_IVT >> art []
QED

(*---------------------------------------------------------------------------*)
(* Intermediate value theorem where value at the left end is bigger          *)
(*---------------------------------------------------------------------------*)

Theorem IVT2:
  !f a b y. a <= b /\ (f(b) <= y /\ y <= f(a)) /\
            (!x. a <= x /\ x <= b ==> $contl f x) ==>
            ?x. a <= x /\ x <= b /\ (f(x) = y)
Proof
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(Q.SPECL [‘\x:real. ~(f x)’, ‘a’, ‘b:real’, ‘-y’] IVT)
  THEN BETA_TAC THEN ASM_REWRITE_TAC[REAL_LE_NEG, REAL_EQ_NEG, REAL_NEGNEG]
  THEN DISCH_THEN MATCH_MP_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC CONT_NEG THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]
QED

(*---------------------------------------------------------------------------*)
(* Prove the simple combining theorems for differentiation                   *)
(*---------------------------------------------------------------------------*)

Theorem DIFF_CONST:
   !k x. ((\x. k) diffl &0)(x)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[diffl] THEN
  REWRITE_TAC[REAL_SUB_REFL, real_div, REAL_MUL_LZERO] THEN
  MATCH_ACCEPT_TAC LIM_CONST
QED

Theorem DIFF_ADD:
   !f g l m x. (f diffl l)(x) /\ (g diffl m)(x) ==>
                   ((\x. f(x) + g(x)) diffl (l + m))(x)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[diffl] THEN
  DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[REAL_ADD2_SUB2] THEN
  REWRITE_TAC[real_div, REAL_RDISTRIB] THEN
  REWRITE_TAC[GSYM real_div] THEN
  CONV_TAC(EXACT_CONV[X_BETA_CONV “h:real” “(f(x + h) - f(x)) / h”]) THEN
  CONV_TAC(EXACT_CONV[X_BETA_CONV “h:real” “(g(x + h) - g(x)) / h”]) THEN
  MATCH_MP_TAC LIM_ADD THEN ASM_REWRITE_TAC[]
QED

Theorem DIFF_MUL:
   !f g l m x. (f diffl l)(x) /\ (g diffl m)(x) ==>
                  ((\x. f(x) * g(x)) diffl ((l * g(x)) + (m * f(x))))(x)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[diffl] THEN
  DISCH_TAC THEN BETA_TAC THEN SUBGOAL_THEN
    “!a b c d. (a * b) - (c * d) = ((a * b) - (a * d)) + ((a * d) - (c * d))”
  (fn th => ONCE_REWRITE_TAC[hol88Lib.GEN_ALL th]) THENL
   [REWRITE_TAC[real_sub] THEN
    ONCE_REWRITE_TAC[AC(REAL_ADD_ASSOC,REAL_ADD_SYM)
      “(a + b) + (c + d) = (b + c) + (a + d)”] THEN
    REWRITE_TAC[REAL_ADD_LINV, REAL_ADD_LID], ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB, GSYM REAL_SUB_RDISTRIB] THEN SUBGOAL_THEN
    “!a b c d e. ((a * b) + (c * d)) / e = ((b / e) * a) + ((c / e) * d)”
    (fn th => ONCE_REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[real_div] THEN
    REWRITE_TAC[REAL_RDISTRIB] THEN BINOP_TAC THEN
    CONV_TAC(AC_CONV(REAL_MUL_ASSOC,REAL_MUL_SYM)), ALL_TAC] THEN
  GEN_REWR_TAC LAND_CONV [REAL_ADD_SYM] THEN
  CONV_TAC(EXACT_CONV(map (X_BETA_CONV “h:real”)
    [“((g(x + h) - g(x)) / h) * f(x + h)”,
     “((f(x + h) - f(x)) / h) * g(x)”])) THEN
  MATCH_MP_TAC LIM_ADD THEN
  CONV_TAC(EXACT_CONV(map (X_BETA_CONV “h:real”)
    [“(g(x + h) - g(x)) / h”, “f(x + h):real”,
     “(f(x + h) - f(x)) / h”, “g(x:real):real”])) THEN
  CONJ_TAC THEN MATCH_MP_TAC LIM_MUL THEN
  BETA_TAC THEN ASM_REWRITE_TAC[LIM_CONST] THEN
  REWRITE_TAC[GSYM contl] THEN
  MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC “l:real” THEN
  ASM_REWRITE_TAC[diffl]
QED

Theorem DIFF_CMUL:
   !f c l x. (f diffl l)(x) ==> ((\x. c * f(x)) diffl (c * l))(x)
Proof
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o CONJ (SPECL [“c:real”, “x:real”] DIFF_CONST)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIFF_MUL) THEN BETA_TAC THEN
  REWRITE_TAC[REAL_MUL_LZERO, REAL_ADD_LID] THEN
  MATCH_MP_TAC(TAUT_CONV(“(a = b) ==> a ==> b”)) THEN AP_THM_TAC THEN
  GEN_REWR_TAC (RAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
  REWRITE_TAC[]
QED

Theorem DIFF_NEG:
   !f l x. (f diffl l)(x) ==> ((\x. ~(f x)) diffl ~l)(x)
Proof
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_NEG_MINUS1] THEN
  MATCH_ACCEPT_TAC DIFF_CMUL
QED

Theorem DIFF_SUB:
   !f g l m x. (f diffl l)(x) /\ (g diffl m)(x) ==>
                   ((\x. f(x) - g(x)) diffl (l - m))(x)
Proof
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIFF_ADD o (uncurry CONJ) o
              (I ## MATCH_MP DIFF_NEG) o CONJ_PAIR) THEN
  BETA_TAC THEN REWRITE_TAC[real_sub]
QED

(*---------------------------------------------------------------------------*)
(* Now the chain rule                                                        *)
(*---------------------------------------------------------------------------*)

Theorem DIFF_CHAIN:
   !f g l m x.
     (f diffl l)(g x) /\ (g diffl m)(x) ==> ((\x. f(g x)) diffl (l * m))(x)
Proof
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN MP_TAC) THEN
  DISCH_THEN(fn th => MP_TAC th THEN ASSUME_TAC(MATCH_MP DIFF_CONT th)) THEN
  REWRITE_TAC[DIFF_CARAT] THEN
  DISCH_THEN(X_CHOOSE_THEN “g':real->real” STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN “f':real->real” STRIP_ASSUME_TAC) THEN
  EXISTS_TAC “\z. if (z = x) then l * m
                     else (f(g(z):real) - f(g(x))) / (z - x)” THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL, REAL_MUL_RZERO] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    ASM_REWRITE_TAC[REAL_SUB_0],
    MP_TAC(CONJ (ASSUME “g contl x”) (ASSUME “f' contl (g(x:real))”)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP CONT_COMPOSE) THEN
    DISCH_THEN(MP_TAC o C CONJ (ASSUME “g' contl x”)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP CONT_MUL) THEN BETA_TAC THEN
    ASM_REWRITE_TAC[contl] THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT_CONV “(a = b) ==> a ==> b”) THEN
    MATCH_MP_TAC LIM_EQUAL THEN X_GEN_TAC “z:real” THEN
    DISCH_TAC THEN BETA_TAC THEN ASM_REWRITE_TAC[REAL_ADD_RID_UNIQ] THEN
    REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC, REAL_ADD_SUB] THEN
    FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_MUL_RINV th]) THEN
    REWRITE_TAC[REAL_MUL_RID]]
QED

(*---------------------------------------------------------------------------*)
(* Differentiation of natural number powers                                  *)
(*---------------------------------------------------------------------------*)

Theorem DIFF_X:
   !x. ((\x. x) diffl &1)(x)
Proof
  GEN_TAC THEN REWRITE_TAC[diffl] THEN BETA_TAC THEN
  REWRITE_TAC[REAL_ADD_SUB] THEN REWRITE_TAC[LIM, REAL_SUB_RZERO] THEN
  BETA_TAC THEN X_GEN_TAC “e:real” THEN DISCH_TAC THEN
  EXISTS_TAC “&1” THEN REWRITE_TAC[REAL_LT_01] THEN
  GEN_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[GSYM ABS_NZ] THEN
  DISCH_THEN(fn th => REWRITE_TAC[MATCH_MP REAL_DIV_REFL th]) THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL, ABS_0]
QED

Theorem DIFF_POW:
   !n x. ((\x. x pow n) diffl (&n * (x pow (n - 1))))(x)
Proof
  INDUCT_TAC THEN REWRITE_TAC[pow, DIFF_CONST, REAL_MUL_LZERO] THEN
  X_GEN_TAC “x:real” THEN
  POP_ASSUM(MP_TAC o CONJ(SPEC “x:real” DIFF_X) o SPEC “x:real”) THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIFF_MUL) THEN BETA_TAC THEN
  MATCH_MP_TAC(TAUT_CONV “(a = b) ==> a ==> b”) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[REAL_MUL_LID] THEN
  REWRITE_TAC[REAL, REAL_RDISTRIB, REAL_MUL_LID] THEN
  GEN_REWR_TAC RAND_CONV [REAL_ADD_SYM] THEN BINOP_TAC THENL
   [REWRITE_TAC[ADD1, ADD_SUB],
    STRUCT_CASES_TAC (SPEC “n:num” num_CASES) THEN
    REWRITE_TAC[REAL_MUL_LZERO] THEN
    REWRITE_TAC[ADD1, ADD_SUB, POW_ADD] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
    REWRITE_TAC[ONE, pow] THEN
    REWRITE_TAC[SYM ONE, REAL_MUL_RID]]
QED

val lemma = REWRITE_RULE [diffl_has_derivative, Once REAL_MUL_COMM] DIFF_POW;

Theorem HAS_DERIVATIVE_POW' :
    !n x. ((\x. x pow n) has_derivative (\y. &n * x pow (n - 1) * y)) (at x)
Proof
    REWRITE_TAC [lemma]
QED

(* !n x. ((\x. x pow n) has_vector_derivative &n * x pow (n - 1)) (at x) *)
Theorem HAS_VECTOR_DERIVATIVE_POW =
        REWRITE_RULE [diffl_has_vector_derivative] DIFF_POW

(*---------------------------------------------------------------------------*)
(* Now power of -1 (then differentiation of inverses follows from chain rule)*)
(*---------------------------------------------------------------------------*)

Theorem DIFF_XM1:
  !x. x <> 0 ==> ((\x. inv(x)) diffl (-(inv(x) pow 2)))(x)
Proof
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[diffl] THEN BETA_TAC THEN
  MATCH_MP_TAC LIM_TRANSFORM THEN
  EXISTS_TAC “\h. ~(inv(x + h) * inv(x))” THEN
  BETA_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[LIM] THEN X_GEN_TAC “e:real” THEN DISCH_TAC THEN
    EXISTS_TAC “abs(x)” THEN
    EVERY_ASSUM(fn th => REWRITE_TAC[REWRITE_RULE[ABS_NZ] th]) THEN
    X_GEN_TAC “h:real” THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN BETA_TAC THEN
    W(C SUBGOAL_THEN SUBST1_TAC o C (curry mk_eq) “&0” o
      rand o rator o snd) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ABS_ZERO, REAL_SUB_0] THEN
    SUBGOAL_THEN “~(x + h = &0)” ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LNEG_UNIQ] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC “abs(h) < abs(~h)” THEN
      REWRITE_TAC[ABS_NEG, REAL_LT_REFL], ALL_TAC] THEN
    W(fn (asl,w) => MP_TAC(SPECL [“x * (x + h)”, lhs w, rhs w]
                           REAL_EQ_LMUL)) THEN
    ASM_REWRITE_TAC[REAL_ENTIRE] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM REAL_NEG_LMUL, GSYM REAL_NEG_RMUL] THEN
    REWRITE_TAC[real_div, REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB] THEN
    ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
      “(a * b) * (c * d) = (c * b) * (d * a)”] THEN
    REWRITE_TAC(map (MATCH_MP REAL_MUL_LINV o ASSUME)
     [“~(x = &0)”, “~(x + h = &0)”]) THEN REWRITE_TAC[REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC[AC(REAL_MUL_ASSOC,REAL_MUL_SYM)
      “(a * b) * (c * d) = (a * d) * (c * b)”] THEN
    REWRITE_TAC[MATCH_MP REAL_MUL_LINV (ASSUME “~(x = &0)”)] THEN
    REWRITE_TAC[REAL_MUL_LID, GSYM REAL_SUB_LDISTRIB] THEN
    REWRITE_TAC[REWRITE_RULE[REAL_NEG_SUB]
                (AP_TERM “$real_neg” (SPEC_ALL REAL_ADD_SUB))] THEN
    REWRITE_TAC[GSYM REAL_NEG_RMUL] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[ABS_NZ],

    REWRITE_TAC[POW_2] THEN
    CONV_TAC(EXACT_CONV[X_BETA_CONV “h:real” “inv(x + h) * inv(x)”]) THEN
    REWRITE_TAC[GSYM LIM_NEG] THEN
    CONV_TAC(EXACT_CONV(map (X_BETA_CONV “h:real”) [“inv(x + h)”, “inv(x)”]))
    THEN MATCH_MP_TAC LIM_MUL THEN BETA_TAC THEN
    REWRITE_TAC[LIM_CONST] THEN
    CONV_TAC(EXACT_CONV[X_BETA_CONV “h:real” “x + h”]) THEN
    MATCH_MP_TAC LIM_INV THEN ASM_REWRITE_TAC[] THEN
    GEN_REWR_TAC LAND_CONV [GSYM REAL_ADD_RID] THEN
    CONV_TAC(EXACT_CONV(map (X_BETA_CONV “h:real”) [“x:real”, “h:real”])) THEN
    MATCH_MP_TAC LIM_ADD THEN BETA_TAC THEN REWRITE_TAC[LIM_CONST] THEN
    MATCH_ACCEPT_TAC LIM_X]
QED

(*---------------------------------------------------------------------------*)
(* Now differentiation of inverse and quotient                               *)
(*---------------------------------------------------------------------------*)

Theorem DIFF_INV:
   !f l x. (f diffl l)(x) /\ ~(f(x) = &0) ==>
        ((\x. inv(f x)) diffl ~(l / (f(x) pow 2)))(x)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[real_div, REAL_NEG_RMUL] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN DISCH_TAC THEN
  MATCH_MP_TAC DIFF_CHAIN THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP POW_INV (CONJUNCT2 th)]) THEN
  MATCH_MP_TAC(CONV_RULE(ONCE_DEPTH_CONV ETA_CONV) DIFF_XM1) THEN
  ASM_REWRITE_TAC[]
QED

Theorem DIFF_DIV:
   !f g l m x. (f diffl l)(x) /\ (g diffl m)(x) /\ ~(g(x) = &0) ==>
    ((\x. f(x) / g(x)) diffl (((l * g(x)) - (m * f(x))) / (g(x) pow 2)))(x)
Proof
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  REWRITE_TAC[real_div] THEN
  MP_TAC(SPECL [“g:real->real”, “m:real”, “x:real”] DIFF_INV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJ(ASSUME “(f diffl l)(x)”)) THEN
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
    AP_TERM_TAC THEN CONV_TAC(AC_CONV(REAL_MUL_ASSOC,REAL_MUL_SYM))]
QED

(*---------------------------------------------------------------------------*)
(* Differentiation of finite sum                                             *)
(*---------------------------------------------------------------------------*)

Theorem DIFF_SUM:
   !f f' m n x. (!r:num. m <= r /\ r < (m + n)
                 ==> ((\x. f r x) diffl (f' r x))(x))
     ==> ((\x. sum(m,n)(\n. f n x)) diffl (sum(m,n) (\r. f' r x)))(x)
Proof
  REPEAT GEN_TAC THEN SPEC_TAC(“n:num”,“n:num”) THEN
  INDUCT_TAC THEN REWRITE_TAC[sum, DIFF_CONST] THEN DISCH_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV HABS_CONV) THEN MATCH_MP_TAC DIFF_ADD THEN
  BETA_TAC THEN CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LESS_TRANS THEN
    EXISTS_TAC “m + n:num” THEN ASM_REWRITE_TAC[ADD_CLAUSES, LESS_SUC_REFL],
    REWRITE_TAC[LESS_EQ_ADD, ADD_CLAUSES, LESS_SUC_REFL]]
QED

(*---------------------------------------------------------------------------*)
(* By bisection, function continuous on closed interval is bounded above     *)
(*---------------------------------------------------------------------------*)

Theorem CONT_BOUNDED:
   !f a b. (a <= b /\ !x. a <= x /\ x <= b ==> $contl f x)
        ==> ?M. !x. a <= x /\ x <= b ==> f(x) <= M
Proof
  REPEAT STRIP_TAC THEN
  (MP_TAC o C SPEC BOLZANO_LEMMA)
    “\(u,v). a <= u /\ u <= v /\ v <= b ==>
               ?M. !x. u <= x /\ x <= v ==> f x <= M” THEN
  CONV_TAC(ONCE_DEPTH_CONV PAIRED_BETA_CONV) THEN
  W(C SUBGOAL_THEN (fn t => REWRITE_TAC[t]) o funpow 2(fst o dest_imp) o snd) THENL
   [ALL_TAC,
    DISCH_THEN(MP_TAC o SPECL [“a:real”, “b:real”]) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL]] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [“u:real”, “v:real”, “w:real”] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    DISCH_TAC THEN
    REPEAT(FIRST_ASSUM(UNDISCH_TAC o assert is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN “v <= b” ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC “w:real” THEN
      ASM_REWRITE_TAC[], ALL_TAC] THEN
    SUBGOAL_THEN “a <= v” ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC “u:real” THEN
      ASM_REWRITE_TAC[], ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC “M1:real”) THEN
    DISCH_THEN(X_CHOOSE_TAC “M2:real”) THEN
    DISJ_CASES_TAC(SPECL [“M1:real”, “M2:real”] REAL_LE_TOTAL) THENL
     [EXISTS_TAC “M2:real” THEN X_GEN_TAC “x:real” THEN STRIP_TAC THEN
      DISJ_CASES_TAC(SPECL [“x:real”, “v:real”] REAL_LE_TOTAL) THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC “M1:real” THEN
        ASM_REWRITE_TAC[], ALL_TAC] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[],
      EXISTS_TAC “M1:real” THEN X_GEN_TAC “x:real” THEN STRIP_TAC THEN
      DISJ_CASES_TAC(SPECL [“x:real”, “v:real”] REAL_LE_TOTAL) THENL
       [ALL_TAC, MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC “M2:real” THEN ASM_REWRITE_TAC[]] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]],
    ALL_TAC] THEN
  X_GEN_TAC “x:real” THEN ASM_CASES_TAC “a <= x /\ x <= b” THENL
   [ALL_TAC,
    EXISTS_TAC “&1” THEN REWRITE_TAC[REAL_LT_01] THEN
    MAP_EVERY X_GEN_TAC [“u:real”, “v:real”] THEN
    REPEAT STRIP_TAC THEN UNDISCH_TAC “~(a <= x /\ x <= b)” THEN
    CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC “u:real”, EXISTS_TAC “v:real”] THEN
    ASM_REWRITE_TAC[]] THEN
  UNDISCH_TAC “!x. a <= x /\ x <= b ==> f contl x” THEN
  DISCH_THEN(MP_TAC o SPEC “x:real”) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[contl, LIM] THEN
  DISCH_THEN(MP_TAC o SPEC “&1”) THEN REWRITE_TAC[REAL_LT_01] THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN “d:real” STRIP_ASSUME_TAC) THEN
  EXISTS_TAC “d:real” THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [“u:real”, “v:real”] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC “abs(f(x:real)) + &1” THEN
  X_GEN_TAC “z:real” THEN STRIP_TAC THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
  DISCH_THEN(MP_TAC o SPEC “z - x”) THEN
  GEN_REWR_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_ADD_SYM] THEN
  REWRITE_TAC[REAL_SUB_ADD] THEN DISCH_TAC THEN
  MP_TAC(SPECL [“f(z:real) - f(x)”, “(f:real->real) x”] ABS_TRIANGLE) THEN
  REWRITE_TAC[REAL_SUB_ADD] THEN
  DISCH_THEN(ASSUME_TAC o ONCE_REWRITE_RULE[REAL_ADD_SYM]) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC “abs(f(z:real))” THEN
  REWRITE_TAC[ABS_LE] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC “abs(f(x:real)) + (abs(f(z) - f(x)))” THEN
  ASM_REWRITE_TAC[REAL_LE_LADD] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
  ASM_CASES_TAC “z:real = x” THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL, ABS_0, REAL_LT_01],
    FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[GSYM ABS_NZ] THEN
    ASM_REWRITE_TAC[REAL_SUB_0, abs, REAL_SUB_LE] THEN
    REWRITE_TAC[REAL_NEG_SUB] THEN COND_CASES_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC “v - u” THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC “v - x”, EXISTS_TAC “v - z”] THEN
    ASM_REWRITE_TAC[real_sub, REAL_LE_RADD, REAL_LE_LADD, REAL_LE_NEG]]
QED

(*---------------------------------------------------------------------------*)
(* Refine the above to existence of least upper bound                        *)
(*---------------------------------------------------------------------------*)

Theorem CONT_HASSUP:
   !f a b. (a <= b /\ !x. a <= x /\ x <= b ==> $contl f x)
        ==> ?M. (!x. a <= x /\ x <= b ==> f(x) <= M) /\
                (!N. N < M ==> ?x. a <= x /\ x <= b /\ N < f(x))
Proof
  let val tm = “\y:real. ?x. a <= x /\ x <= b /\ (y = f(x))” in
  REPEAT GEN_TAC THEN DISCH_TAC THEN MP_TAC(SPEC tm REAL_SUP_LE) THEN
  BETA_TAC THEN
  W(C SUBGOAL_THEN (fn t => REWRITE_TAC[t]) o funpow 2 (fst o dest_imp) o snd)
  THENL
   [CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [“(f:real->real) a”, “a:real”] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL, REAL_LE_LT],
      POP_ASSUM(X_CHOOSE_TAC “M:real” o MATCH_MP CONT_BOUNDED) THEN
      EXISTS_TAC “M:real” THEN X_GEN_TAC “y:real” THEN
      DISCH_THEN(X_CHOOSE_THEN “x:real” MP_TAC) THEN
      REWRITE_TAC[CONJ_ASSOC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC SUBST1_TAC) THEN
      POP_ASSUM MATCH_ACCEPT_TAC],
    DISCH_TAC THEN EXISTS_TAC “sup ^tm” THEN CONJ_TAC THENL
     [X_GEN_TAC “x:real” THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC “sup ^tm”) THEN
      REWRITE_TAC[REAL_LT_REFL] THEN
      CONV_TAC(ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
      DISCH_THEN(MP_TAC o SPEC “(f:real->real) x”) THEN
      REWRITE_TAC[DE_MORGAN_THM, REAL_NOT_LT] THEN
      CONV_TAC(ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
      DISCH_THEN(DISJ_CASES_THEN MP_TAC) THEN REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC “x:real”) THEN ASM_REWRITE_TAC[],
      GEN_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM o SPEC “N:real”) THEN
      DISCH_THEN(X_CHOOSE_THEN “y:real” MP_TAC) THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN “x:real” MP_TAC) THEN
      REWRITE_TAC[CONJ_ASSOC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC SUBST_ALL_TAC) THEN
      DISCH_TAC THEN EXISTS_TAC “x:real” THEN ASM_REWRITE_TAC[]]] end
QED

(*---------------------------------------------------------------------------*)
(* Now show that it attains its upper bound                                  *)
(*---------------------------------------------------------------------------*)

Theorem CONT_ATTAINS:
   !f a b. (a <= b /\ !x. a <= x /\ x <= b ==> $contl f x)
        ==> ?M. (!x. a <= x /\ x <= b ==> f(x) <= M) /\
                (?x. a <= x /\ x <= b /\ (f(x) = M))
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN “M:real” STRIP_ASSUME_TAC o MATCH_MP CONT_HASSUP)
  THEN EXISTS_TAC “M:real” THEN ASM_REWRITE_TAC[] THEN
  GEN_REWR_TAC I [TAUT_CONV “a:bool = ~~a”] THEN
  CONV_TAC(RAND_CONV NOT_EXISTS_CONV) THEN
  REWRITE_TAC[TAUT_CONV “~(a /\ b /\ c) = a /\ b ==> ~c”] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN “!x. a <= x /\ x <= b ==> f(x) < M” MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_LT_LE] THEN
    CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
  PURE_ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN “!x. a <= x /\ x <= b ==> $contl (\x. inv(M - f(x))) x”
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
  SUBGOAL_THEN “?k. !x. a <= x /\ x <= b ==> (\x. inv(M - (f x))) x <= k”
  MP_TAC THENL
   [MATCH_MP_TAC CONT_BOUNDED THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  BETA_TAC THEN DISCH_THEN(X_CHOOSE_TAC “k:real”) THEN
  SUBGOAL_THEN “!x. a <= x /\ x <= b ==> &0 < inv(M - f(x))” ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_INV_POS THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  SUBGOAL_THEN “!x. a <= x /\ x <= b ==> (\x. inv(M - (f x))) x < (k + &1)”
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC “k:real” THEN REWRITE_TAC[REAL_LT_ADDR, REAL_LT_01] THEN
    BETA_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[], ALL_TAC] THEN
  SUBGOAL_THEN “!x. a <= x /\ x <= b ==>
         inv(k + &1) < inv((\x. inv(M - (f x))) x)” MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN
    CONJ_TAC THENL
     [BETA_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[],
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]], ALL_TAC] THEN
  BETA_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN “!x. a <= x /\ x <= b ==> inv(k + &1) < (M - (f x))”
  MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN “~(M - f(x:real) = &0)”
      (SUBST1_TAC o SYM o MATCH_MP REAL_INVINV) THENL
     [CONV_TAC(RAND_CONV SYM_CONV) THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[],
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]], ALL_TAC] THEN
  REWRITE_TAC[REAL_LT_SUB_LADD] THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  ONCE_REWRITE_TAC[GSYM REAL_LT_SUB_LADD] THEN DISCH_TAC THEN
  UNDISCH_TAC “!N. N < M ==> (?x. a <= x /\ x <= b /\ N < (f x))” THEN
  DISCH_THEN(MP_TAC o SPEC “M - inv(k + &1)”) THEN
  REWRITE_TAC[REAL_LT_SUB_RADD, REAL_LT_ADDR] THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INV_POS THEN MATCH_MP_TAC REAL_LT_TRANS THEN
    EXISTS_TAC “k:real” THEN REWRITE_TAC[REAL_LT_ADDR, REAL_LT_01] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC “inv(M - f(a:real))” THEN
    CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_LE_REFL],
    DISCH_THEN(X_CHOOSE_THEN “x:real” MP_TAC) THEN REWRITE_TAC[CONJ_ASSOC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[REAL_NOT_LT] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    ONCE_REWRITE_TAC[GSYM REAL_LT_SUB_LADD] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]
QED

(*---------------------------------------------------------------------------*)
(* Same theorem for lower bound                                              *)
(*---------------------------------------------------------------------------*)

Theorem CONT_ATTAINS2:
   !f a b. (a <= b /\ !x. a <= x /\ x <= b ==> $contl f x)
        ==> ?M. (!x. a <= x /\ x <= b ==> M <= f(x)) /\
                (?x. a <= x /\ x <= b /\ (f(x) = M))
Proof
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN “!x. a <= x /\ x <= b ==> (\x. ~(f x)) contl x” MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CONT_NEG THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJ (ASSUME “a <= b”)) THEN
  DISCH_THEN(X_CHOOSE_THEN “M:real” MP_TAC o MATCH_MP CONT_ATTAINS) THEN
  BETA_TAC THEN DISCH_TAC THEN Q.EXISTS_TAC ‘~M’ THEN CONJ_TAC THENL
   [GEN_TAC THEN GEN_REWR_TAC RAND_CONV [GSYM REAL_LE_NEG] THEN
    ASM_REWRITE_TAC[REAL_NEGNEG],
    ASM_REWRITE_TAC[GSYM REAL_NEG_EQ]]
QED

(*---------------------------------------------------------------------------*)
(* Show it attains *all* values in its range                                 *)
(*---------------------------------------------------------------------------*)

Theorem CONT_ATTAINS_ALL:
   !f a b. a <= b /\ (!x. a <= x /\ x <= b ==> f contl x) ==>
     ?L M. L <= M /\
           (!y. L <= y /\ y <= M ==> ?x. a <= x /\ x <= b /\ (f(x) = y)) /\
           (!x. a <= x /\ x <= b ==> L <= f(x) /\ f(x) <= M)
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN “M:real” MP_TAC o MATCH_MP CONT_ATTAINS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC “xm:real”)) THEN
  FIRST_ASSUM(X_CHOOSE_THEN “L:real” MP_TAC o MATCH_MP CONT_ATTAINS2) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC “xl:real”)) THEN
  MAP_EVERY EXISTS_TAC [“L:real”, “M:real”] THEN REPEAT CONJ_TAC THENL
   [REPEAT(FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPEC “a:real”)) THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    REPEAT DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC “(f:real->real)(a)” THEN ASM_REWRITE_TAC[],
    X_GEN_TAC “y:real” THEN STRIP_TAC THEN
    DISJ_CASES_TAC(SPECL [“xl:real”, “xm:real”] REAL_LE_TOTAL) THENL
     [MP_TAC(SPECL [“f:real->real”, “xl:real”, “xm:real”, “y:real”] IVT),
      MP_TAC(SPECL [“f:real->real”, “xm:real”, “xl:real”, “y:real”] IVT2)] THEN
    ASM_REWRITE_TAC[] THEN
    (W(C SUBGOAL_THEN ASSUME_TAC o funpow 2 (fst o dest_imp) o snd) THENL
      [X_GEN_TAC “x:real” THEN STRIP_TAC THEN
       FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2),
       ASM_REWRITE_TAC[] THEN
       DISCH_THEN(X_CHOOSE_THEN “x:real” STRIP_ASSUME_TAC) THEN
       EXISTS_TAC “x:real” THEN ASM_REWRITE_TAC[]] THEN
     (CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      FIRST [EXISTS_TAC “xl:real” THEN ASM_REWRITE_TAC[] THEN NO_TAC,
             EXISTS_TAC “xm:real” THEN ASM_REWRITE_TAC[] THEN NO_TAC])),
    GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]
QED

(*---------------------------------------------------------------------------*)
(* If f'(x) real_gt 0 then x is locally strictly increasing at the right           *)
(*---------------------------------------------------------------------------*)

Theorem DIFF_LINC:
   !f x l. (f diffl l)(x) /\ &0 < l ==>
      ?d. &0 < d /\ !h. &0 < h /\ h < d ==> f(x) < f(x + h)
Proof
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[diffl, LIM, REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC “l:real”) THEN ASM_REWRITE_TAC[] THEN BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN “d:real” STRIP_ASSUME_TAC) THEN
  EXISTS_TAC “d:real” THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_INV_POS o CONJUNCT1) THEN
  DISCH_THEN(fn th => ONCE_REWRITE_TAC[GSYM(MATCH_MP REAL_LT_RMUL th)]) THEN
  REWRITE_TAC[REAL_MUL_LZERO] THEN REWRITE_TAC[GSYM real_div] THEN
  MATCH_MP_TAC ABS_SIGN THEN EXISTS_TAC “l:real” THEN
  FIRST_ASSUM MATCH_MP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE o CONJUNCT1) THEN
  ASM_REWRITE_TAC[abs]
QED

(*---------------------------------------------------------------------------*)
(* If f'(x) < 0 then x is locally strictly increasing at the left            *)
(*---------------------------------------------------------------------------*)

Theorem DIFF_LDEC:
   !f x l. (f diffl l)(x) /\ l < &0 ==>
      ?d. &0 < d /\ !h. &0 < h /\ h < d ==> f(x) < f(x - h)
Proof
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[diffl, LIM, REAL_SUB_RZERO] THEN
  DISCH_THEN(Q.SPEC_THEN ‘~l’ MP_TAC) THEN
  ONCE_REWRITE_TAC[GSYM REAL_NEG_LT0] THEN ASM_REWRITE_TAC[REAL_NEGNEG] THEN
  REWRITE_TAC[REAL_NEG_LT0] THEN BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN “d:real” STRIP_ASSUME_TAC) THEN
  EXISTS_TAC “d:real” THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_INV_POS o CONJUNCT1) THEN
  DISCH_THEN(fn th => ONCE_REWRITE_TAC[GSYM(MATCH_MP REAL_LT_RMUL th)]) THEN
  REWRITE_TAC[REAL_MUL_LZERO] THEN
  REWRITE_TAC[GSYM REAL_NEG_LT0, REAL_NEG_RMUL] THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_NEG_INV
   (GSYM (MATCH_MP REAL_LT_IMP_NE (CONJUNCT1 th)))]) THEN
  MATCH_MP_TAC ABS_SIGN2 THEN EXISTS_TAC “l:real” THEN
  REWRITE_TAC[GSYM real_div] THEN
  GEN_REWR_TAC (LAND_CONV o RAND_CONV o funpow 3 LAND_CONV o RAND_CONV)
               [real_sub] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE o CONJUNCT1) THEN
  REWRITE_TAC[abs, GSYM REAL_NEG_LE0, REAL_NEGNEG] THEN
  ASM_REWRITE_TAC[GSYM REAL_NOT_LT]
QED

(*---------------------------------------------------------------------------*)
(* If f is differentiable at a local maximum x, f'(x) = 0                    *)
(*---------------------------------------------------------------------------*)

Theorem DIFF_LMAX:
   !f x l. ($diffl f l)(x) /\
           (?d. &0 < d /\ (!y. abs(x - y) < d ==> f(y) <= f(x))) ==> (l = &0)
Proof
  REPEAT GEN_TAC THEN DISCH_THEN
   (CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_THEN “k:real” STRIP_ASSUME_TAC)) THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (SPECL [“l:real”, “&0”] REAL_LT_TOTAL) THEN
  ASM_REWRITE_TAC[] THENL
   [DISCH_THEN(MP_TAC o C CONJ(ASSUME “l < &0”)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIFF_LDEC) THEN
    DISCH_THEN(X_CHOOSE_THEN “e:real” MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MP_TAC(SPECL [“k:real”, “e:real”] REAL_DOWN2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN “d:real” STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC “d:real”) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPEC “x - d”) THEN REWRITE_TAC[REAL_SUB_SUB2] THEN
    SUBGOAL_THEN “&0 <= d” ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
    ASM_REWRITE_TAC[abs] THEN ASM_REWRITE_TAC[GSYM REAL_NOT_LT],
    DISCH_THEN(MP_TAC o C CONJ(ASSUME “&0 < l”)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIFF_LINC) THEN
    DISCH_THEN(X_CHOOSE_THEN “e:real” MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MP_TAC(SPECL [“k:real”, “e:real”] REAL_DOWN2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN “d:real” STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC “d:real”) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPEC “x + d”) THEN REWRITE_TAC[REAL_ADD_SUB2] THEN
    SUBGOAL_THEN “&0 <= d” ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
    REWRITE_TAC[ABS_NEG] THEN
    ASM_REWRITE_TAC[abs] THEN ASM_REWRITE_TAC[GSYM REAL_NOT_LT]]
QED

(*---------------------------------------------------------------------------*)
(* Similar theorem for a local minimum                                       *)
(*---------------------------------------------------------------------------*)

Theorem DIFF_LMIN:
   !f x l. ($diffl f l)(x) /\
           (?d. &0 < d /\ (!y. abs(x - y) < d ==> f(x) <= f(y))) ==> (l = &0)
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(Q.SPECL [‘\x:real. ~(f x)’, ‘x:real’, ‘~l’] DIFF_LMAX) THEN
  BETA_TAC THEN REWRITE_TAC[REAL_LE_NEG, REAL_NEG_EQ0] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC DIFF_NEG THEN ASM_REWRITE_TAC[]
QED

(*---------------------------------------------------------------------------*)
(* In particular if a function is locally flat                               *)
(*---------------------------------------------------------------------------*)

Theorem DIFF_LCONST:
   !f x l. ($diffl f l)(x) /\
         (?d. &0 < d /\ (!y. abs(x - y) < d ==> (f(y) = f(x)))) ==> (l = &0)
Proof
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN “d:real” STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC DIFF_LMAX THEN
  MAP_EVERY EXISTS_TAC [“f:real->real”, “x:real”] THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC “d:real” THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  DISCH_THEN(fn th => FIRST_ASSUM(SUBST1_TAC o C MATCH_MP th)) THEN
  MATCH_ACCEPT_TAC REAL_LE_REFL
QED

(*---------------------------------------------------------------------------*)
(* Lemma about introducing open ball in open interval                        *)
(*---------------------------------------------------------------------------*)

Theorem INTERVAL_LEMMA_LT :
   !a b x. a < x /\ x < b ==>
        ?d. &0 < d /\ !y. abs(x - y) < d ==> a < y /\ y < b
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM ABS_BETWEEN] THEN
  DISJ_CASES_TAC(Q.SPECL [`x - a`, `b - x`] REAL_LE_TOTAL) THENL
  [ Q.EXISTS_TAC `x - a`, Q.EXISTS_TAC `b - x` ] THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN GEN_TAC THEN
  REWRITE_TAC[REAL_LT_SUB_LADD, REAL_LT_SUB_RADD] THEN
  REWRITE_TAC[real_sub, REAL_ADD_ASSOC] THEN
  REWRITE_TAC[GSYM real_sub, REAL_LT_SUB_LADD, REAL_LT_SUB_RADD] THEN
  FREEZE_THEN(fn th => ONCE_REWRITE_TAC[th]) (Q.SPEC `x` REAL_ADD_SYM) THEN
  REWRITE_TAC[REAL_LT_RADD] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  (MATCH_MP_TAC o hol88Lib.GEN_ALL o fst o EQ_IMP_RULE o SPEC_ALL) REAL_LT_RADD THENL
  [ (* goal 1 (of 2) *)
    Q.EXISTS_TAC `a:real` THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    Q.EXISTS_TAC `x + x` THEN ASM_REWRITE_TAC[] THEN
    Q.UNDISCH_TAC `(x - a) <= (b - x)`,
    (* goal 2 (of 2) *)
    Q.EXISTS_TAC `b:real` THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    Q.EXISTS_TAC `x + x` THEN ASM_REWRITE_TAC[] THEN
    Q.UNDISCH_TAC `(b - x) <= (x - a)`] THEN
  REWRITE_TAC[REAL_LE_SUB_LADD, GSYM REAL_LE_SUB_RADD] THEN
  MATCH_MP_TAC(TAUT_CONV ``(a = b) ==> a ==> b``) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[real_sub] THEN
  REAL_ARITH_TAC
QED

Theorem INTERVAL_LEMMA :
   !a b x. a < x /\ x < b ==>
        ?d. &0 < d /\ !y. abs(x - y) < d ==> a <= y /\ y <= b
Proof
  REPEAT GEN_TAC THEN
  DISCH_THEN(Q.X_CHOOSE_TAC `d` o MATCH_MP INTERVAL_LEMMA_LT) THEN
  Q.EXISTS_TAC `d` THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th o CONJUNCT2)) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]
QED

(*---------------------------------------------------------------------------*)
(* Now Rolle's theorem                                                       *)
(*---------------------------------------------------------------------------*)

(* cf. derivativeTheory.ROLLE *)
Theorem ROLLE :
   !f a b. a < b /\
           (f(a) = f(b)) /\
           (!x. a <= x /\ x <= b ==> f contl x) /\
           (!x. a < x /\ x < b ==> f differentiable x)
        ==> ?z. a < z /\ z < b /\ (f diffl &0)(z)
Proof
    rw [differentiable, diffl_has_derivative', contl_eq_continuous_at]
 >> fs [GSYM IN_INTERVAL, EXT_SKOLEM_THM]
 >> MP_TAC (Q.SPECL [‘f’, ‘$* o f'’, ‘a’, ‘b’] derivativeTheory.ROLLE)
 >> Know ‘f continuous_on interval [a,b]’
 >- (MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON >> rw [])
 >> rw [o_DEF, FUN_EQ_THM]
 >> Q.PAT_X_ASSUM ‘!x. x IN interval (a,b) ==> P’ (MP_TAC o (Q.SPEC ‘x’))
 >> RW_TAC std_ss []
 >> Q.EXISTS_TAC ‘x’
 >> fs [IN_INTERVAL] >> METIS_TAC []
QED

(*---------------------------------------------------------------------------*)
(* Mean value theorem                                                        *)
(*---------------------------------------------------------------------------*)

val gfn = “\x. f(x) - (((f(b) - f(a)) / (b - a)) * x)”;

Theorem MVT_LEMMA:
   !(f:real->real) a b. ^gfn(a) = ^gfn(b)
Proof
  REPEAT GEN_TAC THEN BETA_TAC THEN
  ASM_CASES_TAC “b:real = a” THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM REAL_SUB_0]) THEN
  MP_TAC(GENL [“x:real”, “y:real”]
   (SPECL [“x:real”, “y:real”, “b - a”] REAL_EQ_RMUL)) THEN
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
               “w + (x + (y + z)) = (y + w) + (x + z)”,
              REAL_ADD_LINV, REAL_ADD_LID] THEN
  REWRITE_TAC[REAL_ADD_RID]
QED

(* cf. derivativeTheory.MVT (One-dimensional mean value theorem) *)
Theorem MVT :
   !f a b. a < b /\
           (!x. a <= x /\ x <= b ==> f contl x) /\
           (!x. a < x /\ x < b ==> f differentiable x)
        ==> ?l z. a < z /\ z < b /\ (f diffl l)(z) /\
            (f(b) - f(a) = (b - a) * l)
Proof
    rw [differentiable, diffl_has_derivative', contl_eq_continuous_at]
 >> fs [GSYM IN_INTERVAL, EXT_SKOLEM_THM]
 >> MP_TAC (Q.SPECL [‘f’, ‘$* o f'’, ‘a’, ‘b’] derivativeTheory.MVT)
 >> Know ‘f continuous_on interval [a,b]’
 >- (MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON >> rw [])
 >> rw [o_DEF, FUN_EQ_THM]
 >> fs [IN_INTERVAL]
 >> qexistsl_tac [‘f' x’, ‘x’] >> rw []
QED

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

Theorem DIFF_ISCONST_END:
   !f a b. a < b /\
           (!x. a <= x /\ x <= b ==> f contl x) /\
           (!x. a < x /\ x < b ==> (f diffl &0)(x))
        ==> (f b = f a)
Proof
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [“f:real->real”, “a:real”, “b:real”] MVT) THEN
  ASM_REWRITE_TAC[] THEN
  W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
   [GEN_TAC THEN REWRITE_TAC[differentiable] THEN
    DISCH_THEN(curry op THEN (EXISTS_TAC “&0”) o MP_TAC) THEN
    ASM_REWRITE_TAC[],
    DISCH_THEN(fn th => REWRITE_TAC[th])] THEN
  DISCH_THEN(X_CHOOSE_THEN “l:real” (X_CHOOSE_THEN “x:real” MP_TAC)) THEN
  ONCE_REWRITE_TAC[TAUT_CONV “a /\ b /\ c /\ d = (a /\ b) /\ (c /\ d)”] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  DISCH_THEN(MP_TAC o CONJ (ASSUME “(f diffl l)(x)”)) THEN
  DISCH_THEN(SUBST_ALL_TAC o MATCH_MP DIFF_UNIQ) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_MUL_RZERO, REAL_SUB_0]) THEN
  FIRST_ASSUM ACCEPT_TAC
QED

Theorem DIFF_ISCONST:
   !f a b. a < b /\
           (!x. a <= x /\ x <= b ==> f contl x) /\
           (!x. a < x /\ x < b ==> (f diffl &0)(x))
        ==> !x. a <= x /\ x <= b ==> (f x = f a)
Proof
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [“f:real->real”, “a:real”, “x:real”] DIFF_ISCONST_END) THEN
  DISJ_CASES_THEN MP_TAC (REWRITE_RULE[REAL_LE_LT] (ASSUME “a <= x”)) THENL
   [DISCH_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THEN X_GEN_TAC “z:real” THEN STRIP_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC “x:real”,
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC “x:real”] THEN
    ASM_REWRITE_TAC[],
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]
QED

Theorem DIFF_ISCONST_ALL:
   !f. (!x. (f diffl &0)(x)) ==> (!x y. f(x) = f(y))
Proof
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN “!x. f contl x” ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC DIFF_CONT THEN
    EXISTS_TAC “&0” THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  REPEAT GEN_TAC THEN REPEAT_TCL DISJ_CASES_THEN MP_TAC
   (SPECL [“x:real”, “y:real”] REAL_LT_TOTAL) THENL
   [DISCH_THEN SUBST1_TAC THEN REFL_TAC,
    CONV_TAC(RAND_CONV SYM_CONV),
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC DIFF_ISCONST_END THEN
  ASM_REWRITE_TAC[]
QED

(*---------------------------------------------------------------------------*)
(* Boring lemma about distances                                              *)
(*---------------------------------------------------------------------------*)

Theorem INTERVAL_ABS:
   !x z d. (x - d) <= z /\ z <= (x + d) = abs(z - x) <= d
Proof
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
     [EXISTS_TAC “x + d”, EXISTS_TAC “z + d”] THEN
    ASM_REWRITE_TAC[REAL_LE_RADD] THEN
    MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC “z:real”, EXISTS_TAC “x:real”] THEN
    ASM_REWRITE_TAC[]]
QED

(*---------------------------------------------------------------------------*)
(* Continuous injection on an interval can't have a maximum in the middle    *)
(*---------------------------------------------------------------------------*)

Theorem CONT_INJ_LEMMA:
   !f g x d. &0 < d /\
            (!z. abs(z - x) <= d ==> (g(f(z)) = z)) /\
            (!z. abs(z - x) <= d ==> f contl z) ==>
     ~(!z. abs(z - x) <= d ==> f(z) <= f(x))
Proof
  REPEAT GEN_TAC THEN STRIP_TAC THEN IMP_RES_TAC REAL_LT_IMP_LE THEN
  DISCH_THEN(fn th => MAP_EVERY (MP_TAC o C SPEC th) [“x - d”, “x + d”]) THEN
  REWRITE_TAC[REAL_ADD_SUB, REAL_SUB_SUB, ABS_NEG] THEN
  ASM_REWRITE_TAC[abs, REAL_LE_REFL] THEN
  DISCH_TAC THEN DISCH_TAC THEN DISJ_CASES_TAC
    (SPECL [“f(x - d):real”, “f(x + d):real”] REAL_LE_TOTAL) THENL
   [MP_TAC(SPECL [“f:real->real”, “x - d”, “x:real”, “f(x + d):real”] IVT) THEN
    ASM_REWRITE_TAC[REAL_LE_SUB_RADD, REAL_LE_ADDR] THEN
    W(C SUBGOAL_THEN MP_TAC o fst o dest_imp o dest_neg o snd) THENL
     [X_GEN_TAC “z:real” THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ONCE_REWRITE_TAC[GSYM ABS_NEG] THEN
      REWRITE_TAC[abs, REAL_SUB_LE] THEN
      ASM_REWRITE_TAC[REAL_NEG_SUB, REAL_SUB_LE, REAL_LE_SUB_RADD] THEN
      ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_REWRITE_TAC[],
      DISCH_THEN(fn th => REWRITE_TAC[th]) THEN
      DISCH_THEN(X_CHOOSE_THEN “z:real” STRIP_ASSUME_TAC) THEN
      FIRST_ASSUM(MP_TAC o AP_TERM “g:real->real”) THEN
      SUBGOAL_THEN “g((f:real->real) z) = z” SUBST1_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN
        ONCE_REWRITE_TAC[GSYM ABS_NEG] THEN
        REWRITE_TAC[abs, REAL_SUB_LE] THEN
        ASM_REWRITE_TAC[REAL_NEG_SUB, REAL_SUB_LE, REAL_LE_SUB_RADD] THEN
        ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
      SUBGOAL_THEN “g(f(x + d):real) = x + d” SUBST1_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[REAL_ADD_SUB] THEN
        ASM_REWRITE_TAC[abs, REAL_LE_REFL], ALL_TAC] THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_NE THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC “x:real” THEN
      ASM_REWRITE_TAC[REAL_LT_ADDR]],
    MP_TAC(SPECL [“f:real->real”, “x:real”, “x + d”, “f(x - d):real”] IVT2) THEN
    ASM_REWRITE_TAC[REAL_LE_SUB_RADD, REAL_LE_ADDR] THEN
    W(C SUBGOAL_THEN MP_TAC o fst o dest_imp o dest_neg o snd) THENL
     [X_GEN_TAC “z:real” THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[abs, REAL_SUB_LE, REAL_LE_SUB_RADD] THEN
      ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_REWRITE_TAC[],
      DISCH_THEN(fn th => REWRITE_TAC[th]) THEN
      DISCH_THEN(X_CHOOSE_THEN “z:real” STRIP_ASSUME_TAC) THEN
      FIRST_ASSUM(MP_TAC o AP_TERM “g:real->real”) THEN
      SUBGOAL_THEN “g((f:real->real) z) = z” SUBST1_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[abs, REAL_SUB_LE, REAL_LE_SUB_RADD] THEN
        ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
      SUBGOAL_THEN “g(f(x - d):real) = x - d” SUBST1_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[REAL_SUB_SUB, ABS_NEG] THEN
        ASM_REWRITE_TAC[abs, REAL_LE_REFL], ALL_TAC] THEN
      REWRITE_TAC[] THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
      MATCH_MP_TAC REAL_LT_IMP_NE THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC “x:real” THEN
      ASM_REWRITE_TAC[REAL_LT_SUB_RADD, REAL_LT_ADDR]]]
QED

(*---------------------------------------------------------------------------*)
(* Similar version for lower bound                                           *)
(*---------------------------------------------------------------------------*)

Theorem CONT_INJ_LEMMA2:
   !f g x d. &0 < d /\
            (!z. abs(z - x) <= d ==> (g(f(z)) = z)) /\
            (!z. abs(z - x) <= d ==> f contl z) ==>
     ~(!z. abs(z - x) <= d ==> f(x) <= f(z))
Proof
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(Q.SPECL [‘\x:real. ~(f x)’, ‘\y. (g(~y):real)’, ‘x:real’, ‘d:real’]
    CONT_INJ_LEMMA) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[REAL_NEGNEG, REAL_LE_NEG] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CONT_NEG THEN
  FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC
QED

(*---------------------------------------------------------------------------*)
(* Show there's an interval surrounding f(x) in f[[x - d, x + d]]            *)
(*---------------------------------------------------------------------------*)

Theorem CONT_INJ_RANGE:
   !f g x d.  &0 < d /\
            (!z. abs(z - x) <= d ==> (g(f(z)) = z)) /\
            (!z. abs(z - x) <= d ==> f contl z) ==>
        ?e. &0 < e /\
            (!y. abs(y - f(x)) <= e ==> ?z. abs(z - x) <= d /\ (f z = y))
Proof
  REPEAT GEN_TAC THEN STRIP_TAC THEN IMP_RES_TAC REAL_LT_IMP_LE THEN
  MP_TAC(SPECL [“f:real->real”, “x - d”, “x + d”] CONT_ATTAINS_ALL) THEN
  ASM_REWRITE_TAC[INTERVAL_ABS, REAL_LE_SUB_RADD] THEN
  ASM_REWRITE_TAC[GSYM REAL_ADD_ASSOC, REAL_LE_ADDR, REAL_LE_DOUBLE] THEN
  DISCH_THEN(X_CHOOSE_THEN “L:real” (X_CHOOSE_THEN “M:real” MP_TAC)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN “L <= f(x:real) /\ f(x) <= M” STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL, ABS_0], ALL_TAC] THEN
  SUBGOAL_THEN “L < f(x:real) /\ f(x:real) < M” STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_REWRITE_TAC[REAL_LT_LE] THENL
     [DISCH_THEN SUBST_ALL_TAC THEN (MP_TAC o C SPECL CONT_INJ_LEMMA2)
        [“f:real->real”, “g:real->real”, “x:real”, “d:real”],
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN (MP_TAC o C SPECL CONT_INJ_LEMMA)
        [“f:real->real”, “g:real->real”, “x:real”, “d:real”]] THEN
    ASM_REWRITE_TAC[] THEN GEN_TAC THEN
    DISCH_THEN(fn t => FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP th t] THEN NO_TAC)),
    MP_TAC(SPECL [“f(x:real) - L”, “M - f(x:real)”] REAL_DOWN2) THEN
    ASM_REWRITE_TAC[REAL_SUB_LT] THEN
    DISCH_THEN(X_CHOOSE_THEN “e:real” STRIP_ASSUME_TAC) THEN
    EXISTS_TAC “e:real” THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM INTERVAL_ABS] THEN
    REWRITE_TAC[REAL_LE_SUB_RADD] THEN ONCE_REWRITE_TAC[GSYM CONJ_ASSOC] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC “abs(y - f(x:real)) <= e” THEN
    REWRITE_TAC[GSYM INTERVAL_ABS] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC “f(x:real) - e” THEN
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[REAL_LE_SUB_LADD] THEN
      ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
      REWRITE_TAC[GSYM REAL_LE_SUB_LADD],
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC “f(x:real) + (M - f(x))” THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC “f(x:real) + e” THEN
        ASM_REWRITE_TAC[REAL_LE_LADD],
        REWRITE_TAC[REAL_SUB_ADD2, REAL_LE_REFL]]] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]]
QED

(*---------------------------------------------------------------------------*)
(* Continuity of inverse function                                            *)
(*---------------------------------------------------------------------------*)

Theorem CONT_INVERSE:
   !f g x d. &0 < d /\
             (!z. abs(z - x) <= d ==> (g(f(z)) = z)) /\
             (!z. abs(z - x) <= d ==> f contl z)
        ==> g contl (f x)
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[contl, LIM] THEN
  X_GEN_TAC “a:real” THEN DISCH_TAC THEN
  MP_TAC(SPECL [“a:real”, “d:real”] REAL_DOWN2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN “e:real” STRIP_ASSUME_TAC) THEN
  IMP_RES_TAC REAL_LT_IMP_LE THEN
  SUBGOAL_THEN “!z. abs(z - x) <= e ==> (g(f z :real) = z)” ASSUME_TAC THENL
   [X_GEN_TAC “z:real” THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC “e:real” THEN ASM_REWRITE_TAC[],
    ALL_TAC] THEN
  SUBGOAL_THEN “!z. abs(z - x) <= e ==> (f contl z)” ASSUME_TAC THENL
   [X_GEN_TAC “z:real” THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC “e:real” THEN ASM_REWRITE_TAC[],
    ALL_TAC] THEN
  UNDISCH_TAC “!z. abs(z - x) <= d ==> (g(f z :real) = z)” THEN
  UNDISCH_TAC “!z. abs(z - x) <= d ==> (f contl z)” THEN
  DISCH_THEN(K ALL_TAC) THEN DISCH_THEN(K ALL_TAC) THEN
  (MP_TAC o C SPECL CONT_INJ_RANGE)
    [“f:real->real”, “g:real->real”, “x:real”, “e:real”] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN “k:real” STRIP_ASSUME_TAC) THEN
  EXISTS_TAC “k:real” THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC “h:real” THEN BETA_TAC THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE)) THEN
  REWRITE_TAC[GSYM ABS_NZ] THEN DISCH_TAC THEN
  FIRST_ASSUM(fn th => MP_TAC(SPEC “f(x:real) + h” th) THEN
    REWRITE_TAC[REAL_ADD_SUB, ASSUME “abs(h) <= k”] THEN
    DISCH_THEN(X_CHOOSE_THEN “z:real” STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(UNDISCH_TAC o assert is_eq o concl) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC “e:real” THEN
  SUBGOAL_THEN “(g((f:real->real)(z)) = z) /\ (g(f(x)) = x)”
    (fn t => ASM_REWRITE_TAC[t]) THEN CONJ_TAC THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_SUB_REFL, ABS_0]
QED

(*---------------------------------------------------------------------------*)
(* Differentiability of inverse function                                     *)
(*---------------------------------------------------------------------------*)

Theorem DIFF_INVERSE:
   !f g l x d. &0 < d /\
               (!z. abs(z - x) <= d ==> (g(f(z)) = z)) /\
               (!z. abs(z - x) <= d ==> f contl z) /\
               (f diffl l)(x) /\
               ~(l = &0)
        ==> (g diffl (inv l))(f x)
Proof
  REPEAT STRIP_TAC THEN UNDISCH_TAC “(f diffl l)(x)” THEN
  DISCH_THEN(fn th => ASSUME_TAC(MATCH_MP DIFF_CONT th) THEN MP_TAC th) THEN
  REWRITE_TAC[DIFF_CARAT] THEN
  DISCH_THEN(X_CHOOSE_THEN “h:real->real” STRIP_ASSUME_TAC) THEN
  EXISTS_TAC “\y. if (y = f(x)) then inv(h(g y))
                     else (g(y) - g(f(x:real))) / (y - f(x))” THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC “z:real” THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL, REAL_MUL_RZERO] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    ASM_REWRITE_TAC[REAL_SUB_0],
    ALL_TAC,
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN REPEAT AP_TERM_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[REAL_SUB_REFL, ABS_0] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[CONTL_LIM] THEN BETA_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN “g((f:real->real)(x)) = x” ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[REAL_SUB_REFL, ABS_0] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE, ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LIM_TRANSFORM THEN
  EXISTS_TAC “\y:real. inv(h(g(y):real))” THEN
  BETA_TAC THEN CONJ_TAC THENL
   [ALL_TAC,
    (SUBST1_TAC o SYM o ONCE_DEPTH_CONV BETA_CONV)
      “\y. inv((\y:real. h(g(y):real)) y)” THEN
    MATCH_MP_TAC LIM_INV THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN “(\y:real. h(g(y):real)) contl (f(x:real))” MP_TAC THENL
     [MATCH_MP_TAC CONT_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONT_INVERSE THEN EXISTS_TAC “d:real”,
      REWRITE_TAC[CONTL_LIM] THEN BETA_TAC] THEN
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN “?e. &0 < e /\
                    !y. &0 < abs(y - f(x:real)) /\
                        abs(y - f(x:real)) < e ==>
                            (f(g(y)) = y) /\ ~(h(g(y)) = &0)”
  STRIP_ASSUME_TAC THENL
   [ALL_TAC,
    REWRITE_TAC[LIM] THEN X_GEN_TAC “k:real” THEN DISCH_TAC THEN
    EXISTS_TAC “e:real” THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC “y:real” THEN
    DISCH_THEN(fn th => FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th) THEN
      ASSUME_TAC(REWRITE_RULE[GSYM ABS_NZ, REAL_SUB_0] (CONJUNCT1 th))) THEN
    BETA_TAC THEN ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
    SUBGOAL_THEN “y - f(x) = h(g(y)) * (g(y) - x)”
                 SUBST1_TAC
    THENL
     [FIRST_ASSUM(fn th => GEN_REWR_TAC RAND_CONV [GSYM th]) THEN
      REWRITE_TAC[ASSUME “f((g:real->real)(y)) = y”],
      UNDISCH_TAC “&0 < k” THEN
      MATCH_MP_TAC(TAUT_CONV “(a = b) ==> a ==> b”) THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN REWRITE_TAC[ABS_ZERO, REAL_SUB_0]] THEN
    SUBGOAL_THEN “~(g(y:real) - x = &0)” ASSUME_TAC THENL
     [REWRITE_TAC[REAL_SUB_0] THEN
      DISCH_THEN(MP_TAC o AP_TERM “f:real->real”) THEN
      ASM_REWRITE_TAC[], REWRITE_TAC[real_div]] THEN
    SUBGOAL_THEN “inv((h(g(y))) * (g(y:real) - x)) =
      inv(h(g(y))) * inv(g(y) - x)” SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_INV_MUL THEN ASM_REWRITE_TAC[],
      REWRITE_TAC[REAL_MUL_ASSOC] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN
      GEN_REWR_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[]]] THEN
  SUBGOAL_THEN
    “?e. &0 < e /\
         !y. &0 < abs(y - f(x:real)) /\
             abs(y - f(x)) < e ==> (f(g(y)) = y)”
  (X_CHOOSE_THEN “c:real” STRIP_ASSUME_TAC) THENL
   [MP_TAC(SPECL [“f:real->real”, “g:real->real”,
                  “x:real”, “d:real”] CONT_INJ_RANGE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN “e:real” STRIP_ASSUME_TAC) THEN
    EXISTS_TAC “e:real” THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC “y:real” THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
    DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN(X_CHOOSE_THEN “z:real” STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC “(f:real->real)(z) = y” THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
  SUBGOAL_THEN
    “?e. &0 < e /\
         !y. &0 < abs(y - f(x:real)) /\
             abs(y - f(x)) < e
             ==> ~((h:real->real)(g(y)) = &0)”
  (X_CHOOSE_THEN “b:real” STRIP_ASSUME_TAC) THENL
   [ALL_TAC,
    MP_TAC(SPECL [“b:real”, “c:real”] REAL_DOWN2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN “e:real” STRIP_ASSUME_TAC) THEN
    EXISTS_TAC “e:real” THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC “y:real” THEN STRIP_TAC THEN CONJ_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC “e:real” THEN
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN “(\y. h(g(y:real):real)) contl (f(x:real))” MP_TAC THENL
   [MATCH_MP_TAC CONT_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONT_INVERSE THEN EXISTS_TAC “d:real” THEN
    ASM_REWRITE_TAC[], ALL_TAC] THEN
  REWRITE_TAC[CONTL_LIM, LIM] THEN
  DISCH_THEN(MP_TAC o SPEC “abs(l)”) THEN
  ASM_REWRITE_TAC[GSYM ABS_NZ] THEN
  (****begin new*****)
  REWRITE_TAC[ABS_NZ] THEN
  (****end new******)
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN “e:real” STRIP_ASSUME_TAC) THEN
  EXISTS_TAC “e:real” THEN ASM_REWRITE_TAC[ABS_NZ] THEN
  X_GEN_TAC “y:real” THEN
  DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  REWRITE_TAC[GSYM ABS_NZ] THEN
  CONV_TAC CONTRAPOS_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_SUB_LZERO, ABS_NEG, REAL_LT_REFL]
QED


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

Theorem INTERVAL_CLEMMA:
   !a b x. a < x /\ x < b ==>
        ?d. &0 < d /\ !y. abs(y - x) <= d ==> a < y /\ y < b
Proof
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [“x - a”, “b - x”] REAL_DOWN2) THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN ASM_REWRITE_TAC[REAL_LT_SUB_LADD] THEN
  DISCH_THEN(X_CHOOSE_THEN “d:real” STRIP_ASSUME_TAC) THEN
  EXISTS_TAC “d:real” THEN
  ASM_REWRITE_TAC[GSYM INTERVAL_ABS, REAL_LE_SUB_RADD] THEN
  X_GEN_TAC “y:real” THEN STRIP_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN “(d + a) < d + y” MP_TAC THENL
     [GEN_REWR_TAC RAND_CONV  [REAL_ADD_SYM] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC “x:real” THEN ASM_REWRITE_TAC[],
      REWRITE_TAC[REAL_LT_LADD]],
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC “x + d” THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    ASM_REWRITE_TAC[]]
QED

(*---------------------------------------------------------------------------*)
(* Alternative version of inverse function theorem                           *)
(*---------------------------------------------------------------------------*)

Theorem DIFF_INVERSE_OPEN:
   !f g l a x b.
        a < x /\
        x < b /\
        (!z. a < z /\ z < b ==> (g(f(z)) = z) /\ f contl z) /\
        (f diffl l)(x) /\
        ~(l = &0)
        ==> (g diffl (inv l))(f x)
Proof
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC DIFF_INVERSE THEN
  MP_TAC(SPECL [“a:real”, “b:real”,
                “x:real”] INTERVAL_CLEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN “d:real” STRIP_ASSUME_TAC) THEN
  EXISTS_TAC “d:real” THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN GEN_TAC THEN
  DISCH_THEN(fn th => FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  DISCH_THEN(fn th => FIRST_ASSUM(fn t => REWRITE_TAC[MATCH_MP t th]))
QED

(* ------------------------------------------------------------------------- *)
(* Every derivative is Darboux continuous.                                   *)
(* ------------------------------------------------------------------------- *)

Theorem IVT_DERIVATIVE_0 :
    !f f' a b.
        a <= b /\
        (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x)) /\
        f'(a) > &0 /\ f'(b) < &0
        ==> ?z. a < z /\ z < b /\ (f'(z) = &0)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[real_gt] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) empty_rewrites [REAL_LE_LT] THEN
  STRIP_TAC THENL [ALL_TAC, ASM_MESON_TAC[REAL_LT_ANTISYM]] THEN
  Q.SUBGOAL_THEN `?w. (!x. a <= x /\ x <= b ==> f x <= w) /\
                      (?x. a <= x /\ x <= b /\ (f x = w))`
  MP_TAC THENL
  [ MATCH_MP_TAC CONT_ATTAINS THEN
    ASM_MESON_TAC[REAL_LT_IMP_LE, DIFF_CONT], ALL_TAC] THEN
  DISCH_THEN(CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(Q.X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC) THEN

  Q.EXISTS_TAC `z:real` >> Cases_on `z:real = a` >-
  ( Q.UNDISCH_THEN `z:real = a` SUBST_ALL_TAC THEN
    MP_TAC(Q.SPECL[`f:real->real`, `a:real`, `(f':real->real) a`] DIFF_LINC) THEN
    ASM_SIMP_TAC std_ss [REAL_LE_REFL, REAL_LT_IMP_LE] THEN
    DISCH_THEN(Q.X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(Q.SPECL [`d:real`, `b - a`] REAL_DOWN2) THEN
    ASM_REWRITE_TAC[REAL_LT_SUB_LADD, REAL_ADD_LID] THEN
    DISCH_THEN(Q.X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    Q.UNDISCH_TAC `!h. &0 < h /\ h < d ==> w < f (a + h)` THEN
    DISCH_THEN(MP_TAC o Q.SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[REAL_NOT_LT] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    ASM_SIMP_TAC std_ss [REAL_LE_ADDL, REAL_LT_IMP_LE] ) \\

  Cases_on `z:real = b` >-
  ( Q.UNDISCH_THEN `z:real = b` SUBST_ALL_TAC THEN
    MP_TAC(Q.SPECL[`f:real->real`, `b:real`, `(f':real->real) b`] DIFF_LDEC) THEN
    ASM_SIMP_TAC std_ss [REAL_LE_REFL, REAL_LT_IMP_LE] THEN
    DISCH_THEN(Q.X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(Q.SPECL [`d:real`, `b - a`] REAL_DOWN2) THEN
    ASM_REWRITE_TAC[REAL_LT_SUB_LADD, REAL_ADD_LID] THEN
    DISCH_THEN(Q.X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    Q.UNDISCH_TAC `!h. &0 < h /\ h < d ==> w < f (b - h)` THEN
    DISCH_THEN(MP_TAC o Q.SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[REAL_NOT_LT] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[REAL_LE_SUB_LADD, REAL_LE_SUB_RADD] THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    ASM_SIMP_TAC std_ss [REAL_LE_ADDL, REAL_LT_IMP_LE] ) \\
  Q.SUBGOAL_THEN `a < z /\ z < b` STRIP_ASSUME_TAC THENL
  [ ASM_SIMP_TAC std_ss [REAL_LT_LE], ALL_TAC ] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIFF_LMAX THEN
  MP_TAC(Q.SPECL [`z - a`, `b - z`] REAL_DOWN2) THEN
  ASM_REWRITE_TAC[REAL_LT_SUB_LADD, REAL_ADD_LID] THEN
  DISCH_THEN(Q.X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  qexistsl_tac [`f:real->real`, `z:real`] THEN
  ASM_SIMP_TAC std_ss [REAL_LT_IMP_LE] THEN
  Q.EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  DISCH_THEN(fn th => FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
  MAP_EVERY Q.UNDISCH_TAC [`e + z < b`, `e + a < z`] THEN
  REAL_ARITH_TAC
QED

Theorem IVT_DERIVATIVE_POS :
   !f f' a b y.
        a <= b /\
        (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x)) /\
        f'(a) > y /\ f'(b) < y
        ==> ?z. a < z /\ z < b /\ (f'(z) = y)
Proof
  REWRITE_TAC[real_gt] THEN REPEAT STRIP_TAC THEN
  MP_TAC(Q.SPECL [`\x. f(x) - y * x`, `\x:real. f'(x) - y`,
                  `a:real`, `b:real`] IVT_DERIVATIVE_0) THEN
  ASM_SIMP_TAC std_ss [real_gt] THEN
  ASM_REWRITE_TAC[REAL_LT_SUB_LADD, REAL_LT_SUB_RADD] THEN
  ASM_REWRITE_TAC[REAL_EQ_SUB_RADD, REAL_ADD_LID] THEN
  GEN_REWRITE_TAC (funpow 2 LAND_CONV o BINDER_CONV o RAND_CONV o
                   LAND_CONV o RAND_CONV) empty_rewrites [GSYM REAL_MUL_RID] THEN
  ASM_SIMP_TAC std_ss [DIFF_SUB, DIFF_X, DIFF_CMUL]
QED

Theorem IVT_DERIVATIVE_NEG :
   !f f' a b y.
        a <= b /\
        (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x)) /\
        f'(a) < y /\ f'(b) > y
        ==> ?z. a < z /\ z < b /\ (f'(z) = y)
Proof
  REWRITE_TAC[real_gt] THEN REPEAT STRIP_TAC THEN
  MP_TAC(Q.SPECL [`\x:real. ~(f x)`, `\x:real. ~(f' x)`,
                  `a:real`, `b:real`, `~y`] IVT_DERIVATIVE_POS) THEN
  ASM_SIMP_TAC std_ss [real_gt, REAL_LT_NEG, REAL_EQ_NEG] THEN
  ASM_SIMP_TAC std_ss [DIFF_NEG]
QED

(*---------------------------------------------------------------------------*)
(* Miscellaneous Results (for use in hyperbolic trigonemtry library)         *)
(*---------------------------------------------------------------------------*)

Theorem DIFF_CONG:
    !f g l m x y. (?a b. a < y /\ y < b /\ !z. a < z /\ z < b ==> (f z = g z)) /\
        (l = m) /\ (x = y) ==> ((f diffl l) x <=> (g diffl m) y)
Proof
    simp[] >>
    ‘!f g m y. (?a b. a < y /\ y < b /\ !z. a < z /\ z < b ==> (f z = g z)) /\
        (f diffl m) y ==> (g diffl m) y’ suffices_by metis_tac[] >>
    rw[] >> pop_assum mp_tac >> simp[diffl,LIM] >> rw[] >>
    first_x_assum $ drule_then assume_tac >> gs[] >>
    qexists ‘min d (min (y - a) (b - y))’ >> simp[REAL_LT_MIN,REAL_SUB_LT] >> rw[] >>
    first_x_assum $ drule_all_then mp_tac >>
    ‘f (y + h) = g (y + h)’ suffices_by simp[] >> first_x_assum irule >>
    gs[ABS_BOUNDS_LT,REAL_NEG_SUB,REAL_LT_SUB_LADD,REAL_LT_SUB_RADD] >>
    simp[REAL_ADD_COMM]
QED

Theorem DIFF_CONG_IMP :
    !f g y x. (!x. f x = g x) /\ (g diffl y) x ==> (f diffl y) x
Proof
    rw [diffl]
QED

Theorem DIFF_POS_MONO_LT_INTERVAL:
    !f s. is_interval s /\ (!z. z IN s ==> f contl z) /\
        (!z. z IN interior s ==> ?l. 0 < l /\ (f diffl l) z) ==>
        !x y. x IN s /\ y IN s /\ x < y ==> f x < f y
Proof
    rw[] >>
    ‘!z. x < z /\ z < y ==> z IN interior s’ by (
        rw[interior] >> qexists ‘interval (x,y)’ >> simp[OPEN_INTERVAL] >>
        gs[SUBSET_DEF,OPEN_interval,IS_INTERVAL] >> metis_tac[REAL_LE_LT]) >>
    qspecl_then [‘f’,‘x’,‘y’] mp_tac MVT >> impl_tac
    >- (gs[IS_INTERVAL] >> metis_tac[differentiable]) >>
    rw[] >> pop_assum mp_tac >> simp[REAL_EQ_SUB_RADD] >> disch_then kall_tac >>
    irule REAL_LT_MUL >> simp[REAL_SUB_LT] >>
    ntac 2 $ first_x_assum $ dxrule_all_then assume_tac >> metis_tac[DIFF_UNIQ]
QED

Theorem DIFF_NEG_ANTIMONO_LT_INTERVAL:
    !f s. is_interval s /\ (!z. z IN s ==> f contl z) /\
        (!z. z IN interior s ==> ?l. l < 0 /\ (f diffl l) z) ==>
        !x y. x IN s /\ y IN s /\ x < y ==> f y < f x
Proof
    rw[] >> qspecl_then [‘λw. -f w’,‘s’] mp_tac DIFF_POS_MONO_LT_INTERVAL >>
    simp[] >> disch_then irule >> simp[CONT_NEG] >> rw[] >>
    first_x_assum $ dxrule_then assume_tac >> gs[] >>
    qexists ‘-l’ >> simp[DIFF_NEG]
QED

Theorem DIFF_POS_MONO_LT_UU:
    !f. (!z. ?l. 0 < l /\ (f diffl l) z) ==>
        !x y. x < y ==> f x < f y
Proof
    rw[] >> irule DIFF_POS_MONO_LT_INTERVAL >> simp[] >>
    qexists ‘univ(:real)’ >> simp[IS_INTERVAL_POSSIBILITIES] >>
    metis_tac[DIFF_CONT]
QED

Theorem DIFF_POS_MONO_LT_OU:
    !f a. (!z. a < z ==> ?l. 0 < l /\ (f diffl l) z) ==>
        !x y. a < x /\ x < y ==> f x < f y
Proof
    rw[] >> irule DIFF_POS_MONO_LT_INTERVAL >> simp[] >>
    qexists ‘{x | a < x}’ >>
    simp[INTERIOR_INTERVAL_CASES,IS_INTERVAL_POSSIBILITIES,REAL_LT_TRANS,SF SFY_ss] >>
    metis_tac[DIFF_CONT]
QED

Theorem DIFF_POS_MONO_LT_UO:
    !f b. (!z. z < b ==> ?l. 0 < l /\ (f diffl l) z) ==>
        !x y. y < b /\ x < y ==> f x < f y
Proof
    rw[] >> irule DIFF_POS_MONO_LT_INTERVAL >> simp[] >>
    qexists ‘{x | x < b}’ >>
    simp[INTERIOR_INTERVAL_CASES,IS_INTERVAL_POSSIBILITIES,REAL_LT_TRANS,SF SFY_ss] >>
    metis_tac[DIFF_CONT]
QED

Theorem DIFF_POS_MONO_LT_CU:
    !f a. f contl a /\ (!z. a < z ==> ?l. 0 < l /\ (f diffl l) z) ==>
        !x y. a <= x /\ x < y ==> f x < f y
Proof
    rw[] >> irule DIFF_POS_MONO_LT_INTERVAL >> simp[] >>
    qexists ‘{x | a <= x}’ >>
    simp[INTERIOR_INTERVAL_CASES,IS_INTERVAL_POSSIBILITIES,REAL_LT_IMP_LE,REAL_LET_TRANS,SF SFY_ss] >>
    metis_tac[DIFF_CONT,REAL_LE_LT]
QED

Theorem DIFF_POS_MONO_LT_UC:
    !f b. f contl b /\ (!z. z < b ==> ?l. 0 < l /\ (f diffl l) z) ==>
        !x y. y <= b /\ x < y ==> f x < f y
Proof
    rw[] >> irule DIFF_POS_MONO_LT_INTERVAL >> simp[] >>
    qexists ‘{x | x <= b}’ >>
    simp[INTERIOR_INTERVAL_CASES,IS_INTERVAL_POSSIBILITIES,REAL_LT_IMP_LE,REAL_LTE_TRANS,SF SFY_ss] >>
    metis_tac[DIFF_CONT,REAL_LE_LT]
QED

Theorem DIFF_POS_MONO_LT_OO:
    !f a b. (!z. a < z /\ z < b ==> ?l. 0 < l /\ (f diffl l) z) ==>
        !x y. a < x /\ y < b /\ x < y ==> f x < f y
Proof
    rw[] >> irule DIFF_POS_MONO_LT_INTERVAL >> simp[] >>
    qexists ‘{x | a < x /\ x < b}’ >>
    simp[INTERIOR_INTERVAL_CASES,IS_INTERVAL_POSSIBILITIES,REAL_LT_TRANS,SF SFY_ss] >>
    metis_tac[DIFF_CONT]
QED

Theorem DIFF_POS_MONO_LT_CO:
    !f a b. f contl a /\ (!z. a < z /\ z < b ==> ?l. 0 < l /\ (f diffl l) z) ==>
        !x y. a <= x /\ y < b /\ x < y ==> f x < f y
Proof
    rw[] >> irule DIFF_POS_MONO_LT_INTERVAL >> simp[] >>
    qexists ‘{x | a <= x /\ x < b}’ >>
    simp[INTERIOR_INTERVAL_CASES,IS_INTERVAL_POSSIBILITIES,
        REAL_LT_TRANS,REAL_LT_IMP_LE,REAL_LET_TRANS,SF SFY_ss] >>
    metis_tac[DIFF_CONT,REAL_LE_LT]
QED

Theorem DIFF_POS_MONO_LT_OC:
    !f a b. f contl b /\ (!z. a < z /\ z < b ==> ?l. 0 < l /\ (f diffl l) z) ==>
        !x y. a < x /\ y <= b /\ x < y ==> f x < f y
Proof
    rw[] >> irule DIFF_POS_MONO_LT_INTERVAL >> simp[] >>
    qexists ‘{x | a < x /\ x <= b}’ >>
    simp[INTERIOR_INTERVAL_CASES,IS_INTERVAL_POSSIBILITIES,
        REAL_LT_TRANS,REAL_LT_IMP_LE,REAL_LTE_TRANS,SF SFY_ss] >>
    metis_tac[DIFF_CONT,REAL_LE_LT]
QED

Theorem DIFF_POS_MONO_LT_CC:
    !f a b. f contl a /\ f contl b /\
        (!z. a < z /\ z < b ==> ?l. 0 < l /\ (f diffl l) z) ==>
        !x y. a <= x /\ y <= b /\ x < y ==> f x < f y
Proof
    rw[] >> irule DIFF_POS_MONO_LT_INTERVAL >> simp[] >>
    qexists ‘{x | a <= x /\ x <= b}’ >>
    simp[INTERIOR_INTERVAL_CASES,IS_INTERVAL_POSSIBILITIES,
        REAL_LT_IMP_LE,REAL_LET_TRANS,REAL_LTE_TRANS,SF SFY_ss] >>
    metis_tac[DIFF_CONT,REAL_LE_LT]
QED

Theorem DIFF_NEG_ANTIMONO_LT_UU:
    !f. (!z. ?l. l < 0 /\ (f diffl l) z) ==>
        !x y. x < y ==> f y < f x
Proof
    rw[] >> irule DIFF_NEG_ANTIMONO_LT_INTERVAL >> simp[] >>
    qexists ‘univ(:real)’ >> simp[IS_INTERVAL_POSSIBILITIES] >>
    metis_tac[DIFF_CONT]
QED

Theorem DIFF_NEG_ANTIMONO_LT_OU:
    !f a. (!z. a < z ==> ?l. l < 0 /\ (f diffl l) z) ==>
        !x y. a < x /\ x < y ==> f y < f x
Proof
    rw[] >> irule DIFF_NEG_ANTIMONO_LT_INTERVAL >> simp[] >>
    qexists ‘{x | a < x}’ >>
    simp[INTERIOR_INTERVAL_CASES,IS_INTERVAL_POSSIBILITIES,REAL_LT_TRANS,SF SFY_ss] >>
    metis_tac[DIFF_CONT]
QED

Theorem DIFF_NEG_ANTIMONO_LT_UO:
    !f b. (!z. z < b ==> ?l. l < 0 /\ (f diffl l) z) ==>
        !x y. y < b /\ x < y ==> f y < f x
Proof
    rw[] >> irule DIFF_NEG_ANTIMONO_LT_INTERVAL >> simp[] >>
    qexists ‘{x | x < b}’ >>
    simp[INTERIOR_INTERVAL_CASES,IS_INTERVAL_POSSIBILITIES,REAL_LT_TRANS,SF SFY_ss] >>
    metis_tac[DIFF_CONT]
QED

Theorem DIFF_NEG_ANTIMONO_LT_CU:
    !f a. f contl a /\ (!z. a < z ==> ?l. l < 0 /\ (f diffl l) z) ==>
        !x y. a <= x /\ x < y ==> f y < f x
Proof
    rw[] >> irule DIFF_NEG_ANTIMONO_LT_INTERVAL >> simp[] >>
    qexists ‘{x | a <= x}’ >>
    simp[INTERIOR_INTERVAL_CASES,IS_INTERVAL_POSSIBILITIES,REAL_LT_IMP_LE,REAL_LET_TRANS,SF SFY_ss] >>
    metis_tac[DIFF_CONT,REAL_LE_LT]
QED

Theorem DIFF_NEG_ANTIMONO_LT_UC:
    !f b. f contl b /\ (!z. z < b ==> ?l. l < 0 /\ (f diffl l) z) ==>
        !x y. y <= b /\ x < y ==> f y < f x
Proof
    rw[] >> irule DIFF_NEG_ANTIMONO_LT_INTERVAL >> simp[] >>
    qexists ‘{x | x <= b}’ >>
    simp[INTERIOR_INTERVAL_CASES,IS_INTERVAL_POSSIBILITIES,REAL_LT_IMP_LE,REAL_LTE_TRANS,SF SFY_ss] >>
    metis_tac[DIFF_CONT,REAL_LE_LT]
QED

Theorem DIFF_NEG_ANTIMONO_LT_OO:
    !f a b. (!z. a < z /\ z < b ==> ?l. l < 0 /\ (f diffl l) z) ==>
        !x y. a < x /\ y < b /\ x < y ==> f y < f x
Proof
    rw[] >> irule DIFF_NEG_ANTIMONO_LT_INTERVAL >> simp[] >>
    qexists ‘{x | a < x /\ x < b}’ >>
    simp[INTERIOR_INTERVAL_CASES,IS_INTERVAL_POSSIBILITIES,REAL_LT_TRANS,SF SFY_ss] >>
    metis_tac[DIFF_CONT]
QED

Theorem DIFF_NEG_ANTIMONO_LT_CO:
    !f a b. f contl a /\ (!z. a < z /\ z < b ==> ?l. l < 0 /\ (f diffl l) z) ==>
        !x y. a <= x /\ y < b /\ x < y ==> f y < f x
Proof
    rw[] >> irule DIFF_NEG_ANTIMONO_LT_INTERVAL >> simp[] >>
    qexists ‘{x | a <= x /\ x < b}’ >>
    simp[INTERIOR_INTERVAL_CASES,IS_INTERVAL_POSSIBILITIES,
        REAL_LT_TRANS,REAL_LT_IMP_LE,REAL_LET_TRANS,SF SFY_ss] >>
    metis_tac[DIFF_CONT,REAL_LE_LT]
QED

Theorem DIFF_NEG_ANTIMONO_LT_OC:
    !f a b. f contl b /\ (!z. a < z /\ z < b ==> ?l. l < 0 /\ (f diffl l) z) ==>
        !x y. a < x /\ y <= b /\ x < y ==> f y < f x
Proof
    rw[] >> irule DIFF_NEG_ANTIMONO_LT_INTERVAL >> simp[] >>
    qexists ‘{x | a < x /\ x <= b}’ >>
    simp[INTERIOR_INTERVAL_CASES,IS_INTERVAL_POSSIBILITIES,
        REAL_LT_TRANS,REAL_LT_IMP_LE,REAL_LTE_TRANS,SF SFY_ss] >>
    metis_tac[DIFF_CONT,REAL_LE_LT]
QED

Theorem DIFF_NEG_ANTIMONO_LT_CC:
    !f a b. f contl a /\ f contl b /\
        (!z. a < z /\ z < b ==> ?l. l < 0 /\ (f diffl l) z) ==>
        !x y. a <= x /\ y <= b /\ x < y ==> f y < f x
Proof
    rw[] >> irule DIFF_NEG_ANTIMONO_LT_INTERVAL >> simp[] >>
    qexists ‘{x | a <= x /\ x <= b}’ >>
    simp[INTERIOR_INTERVAL_CASES,IS_INTERVAL_POSSIBILITIES,
        REAL_LT_IMP_LE,REAL_LET_TRANS,REAL_LTE_TRANS,SF SFY_ss] >>
    metis_tac[DIFF_CONT,REAL_LE_LT]
QED

Theorem DIFF_EQ_FUN_EQ:
    !f g s. is_interval s /\ (!z. z IN s ==> f contl z) /\ (!z. z IN s ==> g contl z) /\
        (!z. z IN interior s ==> ?l. (f diffl l) z /\ (g diffl l) z) ==>
        ?c. !x. x IN s ==> (f x = g x + c)
Proof
    rw[] >> Cases_on ‘s = {} ’ >- simp[] >>
    gs[GSYM MEMBER_NOT_EMPTY] >> rename [‘w IN s’] >>
    qexists ‘f w - g w’ >> rw[] >>
    ‘f x - g x = f w - g w’ suffices_by (
        simp[REAL_EQ_SUB_RADD,real_sub,REAL_ADD_ASSOC] >>
        disch_then kall_tac >> metis_tac[REAL_ADD_COMM,REAL_ADD_ASSOC]) >>
    Cases_on ‘x = w’ >- simp[] >> wlog_tac ‘w < x’ [‘x’,‘w’]
    >- (first_x_assum $ qspecl_then [‘w’,‘x’] mp_tac >> simp[] >>
        ‘x < w’ suffices_by simp[] >> gs[REAL_NOT_LT,REAL_LE_LT]) >>
    ‘!z. z IN s ==> (λx. f x - g x) contl z’ by simp[CONT_SUB] >>
    ‘!z. z IN interior s ==> ((λx. f x - g x) diffl 0) z’ by (
        rw[] >> qpat_x_assum ‘!z. z IN interior s ==> _’ $ dxrule_then assume_tac >>
        gs[] >> qspecl_then [‘f’,‘g’,‘l’,‘l’,‘z’] mp_tac DIFF_SUB >> simp[]) >>
    ‘!z. w < z /\ z < x ==> z IN interior s’ by (rw[interior] >>
        qexists ‘interval (w,x)’ >> simp[OPEN_INTERVAL,OPEN_interval,SUBSET_DEF] >>
        metis_tac[REAL_LE_LT,IS_INTERVAL]) >>
    qspecl_then [‘λx. f x - g x’,‘w’,‘x’] mp_tac MVT >> simp[] >> impl_tac
    >- (conj_tac >- metis_tac[IS_INTERVAL] >> qx_gen_tac ‘y’ >> strip_tac >>
        simp[differentiable] >> first_x_assum $ irule_at Any >> simp[]) >>
    rw[] >> ntac 2 $ first_x_assum $ dxrule_all_then assume_tac >>
    dxrule_all_then assume_tac DIFF_UNIQ >> rw[] >> gs[REAL_MUL_LZERO]
QED

(*---------------------------------------------------------------------------*)
(* Higher Order Derivatives and Differentiability (Kai Phan and Chun Tian)   *)
(*---------------------------------------------------------------------------*)
(*
   NOTE: This work is inspired by the anntecedents of transcTheory.MCLAURIN :

   (diff(0) = f) /\
   (!m t. m < n /\ &0 <= t /\ t <= h ==>
         (diff(m) diffl diff(SUC m)(t)) (t))

   When eliminating the SELECT operator, by DIFF_UNIQ we have:

   ((diffn m f) diffl y) (x) /\
   ((diffn m f) diffl (diffn (SUC m) t)) (x)) ==> y = diffn (SUC m) t)

   NOTE: It's named "diffn" instead of “diff” because: 1) “diff ”is already a
   constant defined in polyTheory; 2) “diff” looks like a common symbol used in
   unknown user code as either variables or user-defined constants.
 *)
Definition diffn_def :
   (diffn 0       f x = f x) /\
   (diffn (SUC m) f x = @y. ((diffn m f) diffl y)(x))
End

(* NOTE: It's recommended for users to copy this overload to their theories:
Overload D[local] = “diffn”
 *)

Theorem diffn_thm :
    !f. (!m t. ?x. (diffn m f diffl x) t) ==>
        (diffn 0 f = f) /\
        (!m t. ((diffn m f) diffl (diffn (SUC m) f t))(t))
Proof
    rw [diffn_def, FUN_EQ_THM]
 >> SELECT_ELIM_TAC >> simp []
QED

Theorem diffn_0[simp] :
    diffn 0 f = f
Proof
    rw [FUN_EQ_THM, diffn_def]
QED

Theorem diffn_1 : (* was: diff1_def *)
    !f x. diffn 1 f x = @y. (f diffl y) x
Proof
    EVAL_TAC >> simp []
QED

Theorem SELECT_EQ_THM[local] :
    !P Q. (!x. P x <=> Q x) ==> ((@x. P x) = (@x. Q x))
Proof
    rw []
QED

Theorem diffn_cong :
    !n f g x. (!x. f x = g x) ==> (diffn n f x = diffn n g x)
Proof
    Induct_on ‘n’ >- gs []
 >> rw [diffn_def]
 >> HO_MATCH_MP_TAC SELECT_EQ_THM
 >> rw [] >> EQ_TAC >> rw []
 >> METIS_TAC []
QED

Definition higher_differentiable_def :
    (higher_differentiable 0 f x <=> T) /\
    (higher_differentiable (SUC m) f x <=> (?y. (diffn m f diffl y) x) /\
                                           higher_differentiable m f x)
End

Theorem higher_differentiable_thm :
    !f. (diffn 0 f = f) /\
        (!m t. (higher_differentiable (SUC m) f t ==>
               (diffn m f diffl (diffn (SUC m) f t)) t))
Proof
    rw [higher_differentiable_def, diffn_def, FUN_EQ_THM]
 >> SELECT_ELIM_TAC >> simp []
 >> qexists ‘y’ >> simp []
QED

Theorem higher_differentiable_mono :
    !f n m t. m <= n /\ higher_differentiable n f t ==>
              higher_differentiable m f t
Proof
    rpt STRIP_TAC
 >> Cases_on ‘m = n’ >- fs []
 >> Induct_on ‘n’ >- rw [higher_differentiable_def]
 >> rw []
 >> Cases_on ‘m’
 >- simp [higher_differentiable_def]
 >> ‘n < SUC n’ by rw [LESS_SUC_REFL]
 >> ‘n < SUC n ==> higher_differentiable (SUC n) f t ==>
     higher_differentiable n f t’ by METIS_TAC [higher_differentiable_def]
 >> rw []
 >> Cases_on ‘SUC n' = n’ >- (rw [])
 >> Suff ‘SUC n' < n’ >- (fs [])
 >> MATCH_MP_TAC LESS_NOT_SUC >> simp []
QED

Theorem higher_differentiable_1:
    !f x. higher_differentiable 1 f x <=> ?y. (f diffl y) x
Proof
    rpt STRIP_TAC
 >> MP_TAC ( Q.SPECL [‘0’, ‘f’, ‘x’] (cj 2 higher_differentiable_def))
 >> simp [cj 1 higher_differentiable_def]
QED

Theorem higher_differentiable_imp_continuous:
    !f x. higher_differentiable 1 f x ==> f continuous (at x)
Proof
    rw [higher_differentiable_1, GSYM contl_eq_continuous_at]
 >> METIS_TAC [DIFF_CONT]
QED

Theorem higher_differentiable_1_eq_differentiable:
    !f x. higher_differentiable 1 f x <=> derivative$differentiable f (at x)
Proof
    rpt GEN_TAC
 >> fs [higher_differentiable_1, diffl_has_vector_derivative,
        GSYM differentiable_alt, differentiable_has_vector_derivative]
QED

Theorem higher_differentiable_1_eq_differentiable_on:
    !f. (!x. higher_differentiable 1 f x) <=> f differentiable_on univ(:real)
Proof
    rw [higher_differentiable_1_eq_differentiable, differentiable_on]
 >> METIS_TAC [netsTheory.WITHIN_UNIV]
QED

Theorem diffn_SUC :
    !m f. (!x. higher_differentiable (SUC m) f x) ==>
          (diffn m (diffn 1 f) = diffn (SUC m) f)
Proof
    Induct_on ‘m’ >- gs []
 >> rw [diffn_def, FUN_EQ_THM]
 >> HO_MATCH_MP_TAC SELECT_EQ_THM
 >> rw [] >> EQ_TAC >> rw []
 >> (Know ‘!x. higher_differentiable (SUC m) f x’
     >- (Q.X_GEN_TAC ‘z’ \\
         MATCH_MP_TAC higher_differentiable_mono \\
         qexists ‘SUC (SUC m)’ \\
         simp [LESS_EQ_SUC_REFL]) \\
     Q.PAT_X_ASSUM ‘!f. _ ==> _’ (STRIP_ASSUME_TAC o Q.SPEC ‘f’) \\
     DISCH_THEN (fs o wrap))
QED

Theorem diffn_SUC' :
    !m f. (!x. higher_differentiable (SUC m) f x) ==>
          (diffn 1 (diffn m f) = diffn (SUC m) f)
Proof
    rpt STRIP_TAC
  >> ‘1 = SUC 0’ by simp[] >> POP_ORW
  >> rw [diffn_def, FUN_EQ_THM]
QED

Theorem higher_differentiable_imp_11 :
    !n f x. 1 < n /\ higher_differentiable n f x ==>
            higher_differentiable 1 (diffn 1 f) x
Proof
    Induct_on ‘n’ >- gs []
 >> rw [higher_differentiable_def]
 >> FIRST_X_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [‘f’, ‘x’])
 >> fs [LESS_THM]  >> gs []
 >> ‘1 = SUC 0’ by simp []
 >> POP_ORW
 >> rw [higher_differentiable_def] >> qexists ‘y’ >> simp []
QED

Theorem higher_differentiable_imp_n1 :
    !n f. (!x. higher_differentiable (SUC n) f x) ==>
          (!x. higher_differentiable n (diffn 1 f) x)
Proof
    STRIP_TAC
 >> Induct_on ‘n’ >> fs [higher_differentiable_def]
 >> rw []
 >> MP_TAC (Q.SPECL [‘n’, ‘f’] diffn_SUC)
 >> impl_tac
 >- (rw [higher_differentiable_def] \\
     POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
     qexists ‘y'’ >> simp [])
 >> Rewr
 >> Know ‘!x. ?y. (diffn n f diffl y) x /\ higher_differentiable n f x’
 >- (rw [] \\
     POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
     qexists ‘y'’ >> simp [])
 >> DISCH_THEN (fs o wrap)
QED

Theorem higher_differentiable_imp_1n :
    !n f. (!x. higher_differentiable (SUC n) f x) ==>
          (!x. higher_differentiable 1 (diffn n f) x)
Proof
    STRIP_TAC
 >> Induct_on ‘n’
 >- (‘1 = SUC 0’ by simp [] >> POP_ORW >> fs [])
 >> rw []
 >> MP_TAC (Q.SPECL [‘n’, ‘f’] diffn_SUC)
 >> impl_tac >- (rw [] \\
                 MATCH_MP_TAC higher_differentiable_mono \\
                 qexists ‘SUC (SUC n)’ >> fs [])
 >> DISCH_THEN (rw o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘!f. (!x. _) ==> _’ (STRIP_ASSUME_TAC o Q.SPEC ‘diffn 1 f’)
 >> Know ‘!x. higher_differentiable (SUC n) (diffn 1 f) x’
 >- (rw [] \\
     MATCH_MP_TAC higher_differentiable_imp_n1 >> fs [])
 >> gs []
QED

Theorem diffn_chain :
    !f g. (!t. higher_differentiable 1 f t) /\ (!t. higher_differentiable 1 g t) ==>
          (diffn 1 (λx. f (g x)) = λx. diffn 1 f (g x) * diffn 1 g x)
Proof
    rpt STRIP_TAC
 >> ‘1 = SUC 0’ by simp [] >> POP_ORW
 >> fs [diffn_def, higher_differentiable_1, FUN_EQ_THM] >> rw []
 >> SELECT_ELIM_TAC
 >> STRONG_CONJ_TAC
 >- (POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o Q.SPEC ‘g (x :real)’) \\
     rename1 ‘(f diffl z) (g x)’ \\
     qexists ‘z * y’ \\
     MATCH_MP_TAC DIFF_CHAIN >> simp [])
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘y’ ASSUME_TAC)
 >> Q.X_GEN_TAC ‘z’
 >> DISCH_TAC
 >> ‘y = z’ by METIS_TAC [DIFF_UNIQ]
 >> NTAC 2 (SELECT_ELIM_TAC >> rw [] >> fs [])
 >> rename1 ‘y = l * m’
 >> MP_TAC (Q.SPECL [‘f’, ‘g’, ‘l’, ‘m’, ‘(x :real)’] DIFF_CHAIN)
 >> simp []
 >> METIS_TAC [DIFF_UNIQ]
QED

Theorem diffn_const :
    !k. diffn 1 (λx. k) = λx. 0
Proof
    rw [diffn_1, FUN_EQ_THM]
 >> SELECT_ELIM_TAC >> rw []
 >- (qexists ‘0’ >> irule DIFF_CONST)
 >> MP_TAC (Q.SPECL [‘k’, ‘x’] DIFF_CONST)
 >> METIS_TAC [DIFF_UNIQ]
QED

Theorem diffn_cmul :
    !f c. (!x. higher_differentiable 1 f x) ==>
          (diffn 1 (λx. c * f x) = λx. c * diffn 1 f x)
Proof
    rw [diffn_1, higher_differentiable_1, FUN_EQ_THM]
 >> SELECT_ELIM_TAC >> rw []
 >- (POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
     qexists ‘c * y’ >> METIS_TAC [DIFF_CMUL])
 >> SELECT_ELIM_TAC >> rw [] >> fs []
 >> rename1 ‘y = c * z’
 >> MP_TAC (Q.SPECL [‘f’, ‘c’, ‘z’, ‘x’] DIFF_CMUL)
 >> simp []
 >> METIS_TAC [DIFF_UNIQ]
QED

Theorem diffl_imp_diffn :
    !m f x y. (diffn m f diffl y) x ==> (diffn (SUC m) f x = y)
Proof
    rw [diffn_def]
 >> SELECT_ELIM_TAC >> rw []
 >- (qexists ‘y’ >> fs [])
 >> irule DIFF_UNIQ
 >> qexistsl [‘diffn m f’, ‘x’] >> fs []
QED

Theorem diffn_imp_diffl :
    !f x y n. higher_differentiable (SUC n) f x /\ (diffn (SUC n) f x = y) ==>
             (diffn n f diffl y) x
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘f’] higher_differentiable_thm)
 >> rw []
QED

Theorem diffn_mul :
    !f g. (!t. higher_differentiable 1 f t) /\ (!t. higher_differentiable 1 g t) ==>
          (diffn 1 (λx. f x * g x) = (λx. diffn 1 f x * g x + diffn 1 g x * f x))
Proof
    rw [FUN_EQ_THM, diffn_1]
 >> SELECT_ELIM_TAC
 >> STRONG_CONJ_TAC
 >- (fs [higher_differentiable_1] \\
     POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
     rename1 ‘(f diffl l) x’ >> rename1 ‘(g diffl m) x’ \\
     qexists ‘l * g x + m * f x’ \\
     MATCH_MP_TAC DIFF_MUL >> simp [])
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘y’ ASSUME_TAC)
 >> Q.X_GEN_TAC ‘z’
 >> DISCH_TAC
 >> ‘y = z’ by METIS_TAC [DIFF_UNIQ]
 >> SELECT_ELIM_TAC >> rw []
 >- (Q.PAT_X_ASSUM ‘!t. higher_differentiable 1 f t’
        (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
     fs [higher_differentiable_1] \\
     qexists ‘y'’ >> fs [])
 >> SELECT_ELIM_TAC >> rw []
 >- (Q.PAT_X_ASSUM ‘!t. higher_differentiable 1 g t’
        (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
     fs [higher_differentiable_1] \\
     qexists ‘y'’ >> fs [])
 >> qmatch_abbrev_tac ‘y = l * g x + m * f x’
 >> MP_TAC (Q.SPECL [‘f’, ‘g’, ‘l’, ‘m’, ‘x’] DIFF_MUL) >> rw []
 >> METIS_TAC [DIFF_UNIQ]
QED

Theorem diffn_add :
    !f g. (!t. higher_differentiable 1 f t) /\ (!t. higher_differentiable 1 g t) ==>
          (diffn 1 (λx. f x + g x) = (λx. diffn 1 f x + diffn 1 g x))
Proof
    rw [FUN_EQ_THM, diffn_1]
 >> SELECT_ELIM_TAC
 >> STRONG_CONJ_TAC
 >- (fs [higher_differentiable_1] \\
     POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
     rename1 ‘(f diffl l) x’ >> rename1 ‘(g diffl m) x’ \\
     qexists ‘l + m’ \\
     MATCH_MP_TAC DIFF_ADD >> simp [])
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘y’ ASSUME_TAC)
 >> Q.X_GEN_TAC ‘z’
 >> DISCH_TAC
 >> ‘y = z’ by METIS_TAC [DIFF_UNIQ]
 >> SELECT_ELIM_TAC >> rw []
 >- (Q.PAT_X_ASSUM ‘!t. higher_differentiable 1 f t’
        (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
     fs [higher_differentiable_1] \\
     qexists ‘y'’ >> fs [])
 >> SELECT_ELIM_TAC >> rw []
 >- (Q.PAT_X_ASSUM ‘!t. higher_differentiable 1 g t’
        (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
     fs [higher_differentiable_1] \\
     qexists ‘y'’ >> fs [])
 >> qmatch_abbrev_tac ‘y = l + m’
 >> MP_TAC (Q.SPECL [‘f’, ‘g’, ‘l’, ‘m’, ‘x’] DIFF_ADD) >> rw []
 >> METIS_TAC [DIFF_UNIQ]
QED

Theorem diffn_sub :
    !f g. (!t. higher_differentiable 1 f t) /\ (!t. higher_differentiable 1 g t) ==>
          (diffn 1 (λx. f x - g x) = (λx. diffn 1 f x - diffn 1 g x))
Proof
    rw [FUN_EQ_THM, diffn_1]
 >> SELECT_ELIM_TAC
 >> STRONG_CONJ_TAC
 >- (fs [higher_differentiable_1] \\
     POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
     rename1 ‘(f diffl l) x’ >> rename1 ‘(g diffl m) x’ \\
     qexists ‘l - m’ \\
     MATCH_MP_TAC DIFF_SUB >> simp [])
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘y’ ASSUME_TAC)
 >> Q.X_GEN_TAC ‘z’
 >> DISCH_TAC
 >> ‘y = z’ by METIS_TAC [DIFF_UNIQ]
 >> SELECT_ELIM_TAC >> rw []
 >- (Q.PAT_X_ASSUM ‘!t. higher_differentiable 1 f t’
        (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
     fs [higher_differentiable_1] \\
     qexists ‘y'’ >> fs [])
 >> SELECT_ELIM_TAC >> rw []
 >- (Q.PAT_X_ASSUM ‘!t. higher_differentiable 1 g t’
        (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
     fs [higher_differentiable_1] \\
     qexists ‘y'’ >> fs [])
 >> qmatch_abbrev_tac ‘y = l - m’
 >> MP_TAC (Q.SPECL [‘f’, ‘g’, ‘l’, ‘m’, ‘x’] DIFF_SUB) >> rw []
 >> METIS_TAC [DIFF_UNIQ]
QED

val higher_differentiable_n_imp_1_tactic =
    rw []
    >- (Q.PAT_X_ASSUM ‘!x. higher_differentiable (SUC n') f x’
         (STRIP_ASSUME_TAC o Q.SPEC ‘t’) \\
        MATCH_MP_TAC higher_differentiable_mono \\
        qexists ‘SUC n'’ >> simp []) \\
    Q.PAT_X_ASSUM ‘!x. higher_differentiable (SUC n') g x’
     (STRIP_ASSUME_TAC o Q.SPEC ‘t’) \\
    MATCH_MP_TAC higher_differentiable_mono \\
    qexists ‘SUC n'’ >> simp [];

Theorem higher_differentiable_add :
    !f g n. (!x. higher_differentiable n f x) /\
            (!x. higher_differentiable n g x) ==>
            (!x. higher_differentiable n (λx. f x + g x) x)
Proof
    Induct_on ‘n’ >- gs [higher_differentiable_def]
 >> rw [higher_differentiable_def, FORALL_AND_THM]
 >> Cases_on ‘n’
 >- (fs [diffn_0] \\
     Q.PAT_X_ASSUM ‘!x. ?y. (g diffl y) x’ (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
     Q.PAT_X_ASSUM ‘!x. ?y. (f diffl y) (x :real)’ (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
     rename1 ‘(f diffl l) x’ >> rename1 ‘(g diffl m) x’ \\
     qexists ‘l + m’ \\
     MATCH_MP_TAC DIFF_ADD >> simp [])
 >> gs [GSYM diffn_SUC]
 >> MP_TAC (Q.SPECL [‘f’, ‘g’] diffn_add)
 >> impl_tac >- higher_differentiable_n_imp_1_tactic >> Rewr
 >> Q.ABBREV_TAC ‘df = diffn 1 f’
 >> Q.ABBREV_TAC ‘dg = diffn 1 g’
 >> Q.PAT_X_ASSUM ‘!f g. _’ (STRIP_ASSUME_TAC o Q.SPECL [‘df’, ‘dg’])
 >> rename1 ‘?y. (diffn m (\x. df x + dg x) diffl y) x’
 >> Know ‘(!x. higher_differentiable (SUC m) df x) /\
          (!x. higher_differentiable (SUC m) dg x)’
 >- (rw [Abbr ‘df’, Abbr ‘dg’, higher_differentiable_def] \\
     MATCH_MP_TAC higher_differentiable_imp_n1 >> gs [])
 >> DISCH_THEN (fs o wrap)
 >> fs [higher_differentiable_def]
QED

Theorem higher_differentiable_sub :
    !f g n. (!x. higher_differentiable n f x) /\
            (!x. higher_differentiable n g x) ==>
            (!x. higher_differentiable n (λx. f x - g x) x)
Proof
    Induct_on ‘n’ >- gs [higher_differentiable_def]
 >> rw [higher_differentiable_def, FORALL_AND_THM]
 >> Cases_on ‘n’
 >- (fs [diffn_0] \\
     Q.PAT_X_ASSUM ‘!x. ?y. (g diffl y) x’ (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
     Q.PAT_X_ASSUM ‘!x. ?y. (f diffl y) (x :real)’ (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
     rename1 ‘(f diffl l) x’ \\
     rename1 ‘(g diffl m) x’ \\
     qexists ‘l - m’ \\
     MATCH_MP_TAC DIFF_SUB >> simp [])
 >> gs [GSYM diffn_SUC]
 >> MP_TAC (Q.SPECL [‘f’, ‘g’] diffn_sub)
 >> impl_tac >- higher_differentiable_n_imp_1_tactic >> Rewr
 >> Q.ABBREV_TAC ‘df = diffn 1 f’
 >> Q.ABBREV_TAC ‘dg = diffn 1 g’
 >> Q.PAT_X_ASSUM ‘!f g. _’ (STRIP_ASSUME_TAC o Q.SPECL [‘df’, ‘dg’])
 >> rename1 ‘?y. (diffn m (\x. df x - dg x) diffl y) x’
 >> Know ‘(!x. higher_differentiable (SUC m) df x) /\
          (!x. higher_differentiable (SUC m) dg x)’
 >- (rw [Abbr ‘df’, Abbr ‘dg’, higher_differentiable_def] \\
     MATCH_MP_TAC higher_differentiable_imp_n1 >> gs [])
 >> DISCH_THEN (fs o wrap)
 >> fs [higher_differentiable_def]
QED

Theorem higher_differentiable_mul :
    !f g n. (!x. higher_differentiable n f x) /\
            (!x. higher_differentiable n g x) ==>
            (!x. higher_differentiable n (λx. f x * g x) x)
Proof
    Induct_on ‘n’ >- (gs [higher_differentiable_def])
 >> rw [higher_differentiable_def, FORALL_AND_THM]
 >> Cases_on ‘n’
 >- (fs [diffn_0] \\
     Q.PAT_X_ASSUM ‘!x. ?y. (g diffl y) x’ (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
     Q.PAT_X_ASSUM ‘!x. ?y. (f diffl y) (x :real)’ (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
     rename1 ‘(f diffl l) x’ >> rename1 ‘(g diffl m) x’ \\
     qexists ‘l * g x + m * f x’ \\
     MATCH_MP_TAC DIFF_MUL >> simp [])
 >> gs [GSYM diffn_SUC]
 >> MP_TAC (Q.SPECL [‘f’, ‘g’] diffn_mul)
 >> impl_tac >- higher_differentiable_n_imp_1_tactic >> Rewr
 >> Q.ABBREV_TAC ‘df = diffn 1 f’
 >> Q.ABBREV_TAC ‘dg = diffn 1 g’
 >> rename1 ‘!x. ?y. (diffn m df diffl y) x’
 >> Know ‘!x. higher_differentiable (SUC m) (λx. df x * g x) x’
 >- (Q.PAT_X_ASSUM ‘!f g. _’ (MP_TAC o Q.SPECL [‘df’, ‘g’]) \\
     Know ‘(!x. higher_differentiable (SUC m) df x) /\
           (!x. higher_differentiable (SUC m) g x)’
     >- (rw [Abbr ‘df’, higher_differentiable_def] \\
         MATCH_MP_TAC higher_differentiable_imp_n1 >> gs []) >> Rewr)
 >> DISCH_TAC
 >> Know ‘!x. higher_differentiable (SUC m) (λx. f x * dg x) x’
 >- (Q.PAT_X_ASSUM ‘!f g. _’ (MP_TAC o Q.SPECL [‘f’, ‘dg’]) \\
     Know ‘(!x. higher_differentiable (SUC m) f x) /\
           (!x. higher_differentiable (SUC m) dg x)’
     >- (rw [Abbr ‘dg’, higher_differentiable_def] \\
         MATCH_MP_TAC higher_differentiable_imp_n1 >> gs []) >> Rewr)
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘λx. df x * g x’, ‘λx. dg x * f x’, ‘SUC m’]
                    higher_differentiable_add)
 >> Suff ‘(!x. higher_differentiable (SUC m) (λx. df x * g x) x) /\
          (!x. higher_differentiable (SUC m) (λx. dg x * f x) x)’
 >- (rw [higher_differentiable_def])
 >> rw [Abbr ‘df’, Abbr ‘dg’]
QED

Theorem higher_differentiable_chain :
    !n f g. (!x. higher_differentiable n f x) /\
            (!x. higher_differentiable n g x) ==>
            (!x. higher_differentiable n (λx. f (g x)) x)
Proof
    Induct_on ‘n’ >- gs [higher_differentiable_def]
 >> rw [higher_differentiable_def, FORALL_AND_THM]
 >> Cases_on ‘n’
 >- (fs [diffn_0] \\
     Q.PAT_X_ASSUM ‘!x. ?y. (g diffl y) x’ (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
     Q.PAT_X_ASSUM ‘!x. ?y. (f diffl y) (x :real)’
        (STRIP_ASSUME_TAC o Q.SPEC ‘g (x :real)’) \\
     rename1 ‘(f diffl z) (g x)’ \\
     qexists ‘z * y’ \\
     MATCH_MP_TAC DIFF_CHAIN >> simp [])
 >> gs [GSYM diffn_SUC]
 >> rename1 ‘?y. (diffn m (diffn 1 (\x. f (g x))) diffl y) x’
 >> Know ‘diffn 1 (λx. f (g x)) = λx. diffn 1 f (g x) * diffn 1 g x’
 >- (MATCH_MP_TAC diffn_chain >> rw [] \\
     Q.PAT_X_ASSUM ‘!x. higher_differentiable (SUC m) f x’
       (STRIP_ASSUME_TAC o Q.SPEC ‘t’) \\
     MATCH_MP_TAC higher_differentiable_mono \\
     qexists ‘SUC m’ >> simp [])
 >> Rewr
 >> Q.ABBREV_TAC ‘df = diffn 1 f’
 >> Q.ABBREV_TAC ‘dg = diffn 1 g’
 >> Q.ABBREV_TAC ‘dfg = λx. df (g x)’ >> simp []
 >> MP_TAC (Q.SPECL [‘dfg’, ‘dg’, ‘SUC m’] higher_differentiable_mul)
 >> impl_tac
 >- (rw [Abbr ‘dfg’, Abbr ‘dg’, higher_differentiable_def] \\
     Q.PAT_X_ASSUM ‘!f g. _’ (MP_TAC o Q.SPECL [‘df’, ‘g’]) \\
     simp [] \\
     Suff ‘(!x. higher_differentiable (SUC m) df x)’
     >- (rw [higher_differentiable_def]) \\
     rw [Abbr ‘df’, higher_differentiable_def] \\
     MATCH_MP_TAC higher_differentiable_imp_n1 >> gs [])
 >> rw [higher_differentiable_def]
QED

Theorem diffn_linear :
    !a b. diffn 1 (λx. a * x + b) = λx. a
Proof
    rw [diffn_1, FUN_EQ_THM]
 >> SELECT_ELIM_TAC >> rw []
 >- (qexists ‘a’ \\
     MP_TAC (Q.SPECL [‘λx. a * x’, ‘λx. b’, ‘a’, ‘0’, ‘x’] DIFF_ADD) \\
     impl_tac
     >- (reverse CONJ_TAC >- (METIS_TAC [DIFF_CONST]) \\
         MP_TAC (Q.SPECL [‘λx. x’, ‘a’, ‘1’, ‘x’] DIFF_CMUL) \\
         impl_tac >- (METIS_TAC [DIFF_X]) >> gs []) \\
     gs [])
 >> rename1 ‘y = a’
 >> MP_TAC (Q.SPECL [‘λx. a * x’, ‘λx. b’, ‘a’, ‘0’, ‘x’] DIFF_ADD)
 >> impl_tac
 >- (reverse CONJ_TAC >- (METIS_TAC [DIFF_CONST]) \\
     MP_TAC (Q.SPECL [‘λx. x’, ‘a’, ‘1’, ‘x’] DIFF_CMUL) \\
     impl_tac >- (METIS_TAC [DIFF_X]) >> gs [])
 >> rw []
 >> METIS_TAC [DIFF_UNIQ]
QED

Theorem diffn_linear' :
    !a b n. 2 <= n /\ (!t. higher_differentiable n (λx. a * x + b) t) ==>
            (diffn n (λx. a * x + b) = λx. 0)
Proof
    Induct_on ‘n’ >- gs [diffn_def]
 >> rw [diffn_def, FUN_EQ_THM]
 >> SELECT_ELIM_TAC >> rw []
 >- (Cases_on ‘n = 0’ >- (gs [diffn_def]) \\
     Cases_on ‘n = 1’ >- (gs [diffn_1, diffn_linear] \\
                          qexists ‘0’ >> simp [DIFF_CONST]) \\
     Q.PAT_X_ASSUM ‘!a b. _’ (MP_TAC o Q.SPECL [‘a’, ‘b’]) \\
     Suff ‘2 <= n /\ (!t. higher_differentiable n (λx. a * x + b) t)’
     >- (rw [] >> qexists ‘0’ >> simp [DIFF_CONST]) \\
     rw [] \\
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o Q.SPEC ‘t’) \\
     MATCH_MP_TAC higher_differentiable_mono \\
     qexists ‘SUC n’ >> gs [])
 >> Cases_on ‘n = 0’ >- (gs [diffn_def])
 >> Cases_on ‘n = 1’ >- (gs [diffn_1, diffn_linear] \\
                         METIS_TAC [DIFF_CONST, DIFF_UNIQ])
 >> Q.PAT_X_ASSUM ‘!a b. _’ (MP_TAC o Q.SPECL [‘a’, ‘b’])
 >> Suff ‘2 <= n /\ (!t. higher_differentiable n (λx. a * x + b) t)’
 >- (rw [] >> gs [] \\
     METIS_TAC [DIFF_CONST, DIFF_UNIQ])
 >> rw []
 >> FIRST_X_ASSUM (STRIP_ASSUME_TAC o Q.SPEC ‘t’)
 >> MATCH_MP_TAC higher_differentiable_mono
 >> qexists ‘SUC n’ >> gs []
QED

Theorem higher_differentiable_sub_linear :
    !a k x. higher_differentiable k (λx. a - x) x
Proof
    STRIP_TAC
 >> Induct_on ‘k’ >- gs [higher_differentiable_def]
 >> rw [higher_differentiable_def]
 >> Know ‘!x. ((λx. a - x) diffl -1) x’
 >- (rw [diffl] \\
     ‘!h. a - (x + h) - (a - x) = -h’ by REAL_ARITH_TAC >> POP_ORW \\
     MP_TAC (Q.SPECL [‘λh. -h / h’, ‘λx. -1’, ‘-1’, ‘0’] LIM_EQUAL) \\
     rw [] \\
     METIS_TAC [LIM_CONST])
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘-1’, ‘a’, ‘k’] diffn_linear') >> rw []
 >> ‘!x. -x + a = a - x’ by (rw [] >> REAL_ARITH_TAC)
 >> POP_ASSUM (fs o wrap)
 >> Cases_on ‘k = 0’
 >- (qexists ‘-1’ \\
     rw [diffl] \\
     ‘!h. a - (x + h) - (a - x) = -h’ by REAL_ARITH_TAC \\
     POP_ORW \\
     MP_TAC (Q.SPECL [‘λh. -h / h’, ‘λx. -1’, ‘-1’, ‘0’] LIM_EQUAL) \\
     rw [] \\
     METIS_TAC [LIM_CONST])
 >> Cases_on ‘k = 1’
 >- (qexists ‘0’ >> gs [] \\
     MP_TAC (Q.SPECL [‘λx. a’, ‘λx. x’, ‘0’, ‘1’, ‘x’] DIFF_SUB) \\
     impl_tac >- (METIS_TAC [DIFF_CONST, DIFF_X]) \\
     rw [] \\
     Know ‘diffn 1 (λx. a - x) = λx. -1’
     >- (rw [FUN_EQ_THM] \\
         POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
         ‘1 = SUC 0’ by simp [] >> POP_ORW \\
         irule diffl_imp_diffn >> fs [diffn_def]) >> Rewr \\
     METIS_TAC [DIFF_CONST])
 >> gs []
 >> qexists ‘0’
 >> METIS_TAC [DIFF_CONST]
QED

Theorem pow_neg_1[local] :
  -(1 :real) pow 1 = -1
Proof
  REAL_ARITH_TAC
QED

Theorem diffn_neg_sub :
    !n f a. (!x. higher_differentiable n f x) ==>
            (diffn n (λx. f (a - x)) = λx. (-1) pow n * diffn n f (a - x))
Proof
    Induct_on ‘n’ >- gs [diffn_def]
 >> rw [FUN_EQ_THM]
 >> Q.ABBREV_TAC ‘g = λx. f (a - x)’
 >> MP_TAC (Q.SPECL [‘n’, ‘g’] diffn_SUC')
 >> impl_tac
 >- (rw [Abbr ‘g’] \\
     irule higher_differentiable_chain >> simp [] \\
     METIS_TAC [higher_differentiable_sub_linear])
 >> DISCH_THEN (rw o wrap o SYM)
 >> Q.PAT_X_ASSUM ‘!f a. _’ (STRIP_ASSUME_TAC o Q.SPECL [‘f’, ‘a’])
 >> Know ‘!x. higher_differentiable n f x’
 >- (rw [] \\
     MATCH_MP_TAC higher_differentiable_mono \\
     qexists ‘SUC n’ >> gs [])
 >> DISCH_THEN (fs o wrap) >> gs []
 >> POP_ORW
 >> rw [Abbr ‘g’]
 >> Know ‘!x. higher_differentiable 1 f x’
 >- (rw [] \\
     MATCH_MP_TAC higher_differentiable_mono \\
     qexists ‘SUC n’ >> fs [])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘g = λx. diffn n f (a - x)’
 >> Know ‘!x. higher_differentiable 1 g x’
 >- (rw [Abbr ‘g’] \\
     irule higher_differentiable_chain >> rw []
     >- (METIS_TAC [higher_differentiable_imp_1n]) \\
     METIS_TAC [higher_differentiable_sub_linear])
 >> DISCH_TAC
 >> ASM_SIMP_TAC std_ss [diffn_cmul]
 >> ‘-(1 :real) pow SUC n = -1 pow n * -1’ by rw [ADD1, POW_ADD, pow_neg_1]
 >> POP_ORW
 >> rw [REAL_MUL_COMM, Abbr ‘g’]
 >> Q.ABBREV_TAC ‘dfn = diffn n f’
  >> MP_TAC (Q.SPECL [‘dfn’, ‘λx. a - x’] diffn_chain)
 >> impl_tac >- (rw [Abbr ‘dfn’]
                 >- (METIS_TAC [higher_differentiable_imp_1n]) \\
                 METIS_TAC [higher_differentiable_sub_linear])
 >> rw []
 >> Know ‘diffn 1 (λx. a - x) x = -1’
 >- (MP_TAC (Q.SPECL [‘-1’, ‘a’] diffn_linear) \\
    ‘!x. a - x = -x + a’ by (rw [] >> REAL_ARITH_TAC) \\
     rw [FUN_EQ_THM])
 >> Rewr
 >> rw [Abbr ‘dfn’, REAL_MUL_COMM]
 >> METIS_TAC [diffn_SUC']
QED

Theorem higher_differentiable_continuous_on :
    !m n f. (!x. higher_differentiable n f x) /\ m < n /\ 0 < n ==>
            diffn m f continuous_on univ(:real)
Proof
    Induct_on ‘m’
 >- (rw [] \\
     ‘1 <= n’ by fs [] \\
     MP_TAC (Q.SPECL [‘f’, ‘n’, ‘1’] higher_differentiable_mono) >> fs [] \\
     STRIP_TAC \\
     MP_TAC (Q.SPECL [‘f’] higher_differentiable_imp_continuous) >> gs [] \\
     fs [continuous_at, continuous_on, IN_UNIV])
 >> rpt STRIP_TAC
 >> Know ‘!x. higher_differentiable (SUC m) f x’
 >- (rw [] \\
     HO_MATCH_MP_TAC higher_differentiable_mono \\
     qexists ‘n’ \\
     METIS_TAC [LT_IMP_LE])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘g = diffn 1 f’
 >> Know ‘diffn m g = diffn (SUC m) f’
 >- (rw [Abbr ‘g’] \\
     HO_MATCH_MP_TAC diffn_SUC \\
     simp [])
 >> DISCH_TAC >> gs []
 >> Cases_on ‘m = 0’
 >- (rw [diffn_0, Abbr ‘g’, continuous_on_def] \\
     MATCH_MP_TAC CONTINUOUS_AT_WITHIN \\
     MATCH_MP_TAC higher_differentiable_imp_continuous \\
     HO_MATCH_MP_TAC higher_differentiable_imp_11 \\
     qexists ‘n’ >> gs [])
 >> Cases_on ‘n’ >> fs []
 >> Q.PAT_X_ASSUM ‘diffn m g = _’ (rw o wrap o SYM)
 >> FIRST_X_ASSUM (MATCH_MP_TAC)
 >> qexists ‘n'’ >> rw [Abbr ‘g’]
 >> MATCH_MP_TAC higher_differentiable_imp_n1 >> simp []
QED

Theorem higher_differentiable_0 :
    !n x. higher_differentiable n (λx. 0) x
Proof
    Induct_on ‘n’ >- (gs [higher_differentiable_def])
 >> rw [higher_differentiable_def, FORALL_AND_THM]
 >> qexists ‘0’ >> rw []
 >> Induct_on ‘n’ >- (gs [higher_differentiable_def, DIFF_CONST])
 >> rw [GSYM diffn_SUC, diffn_const]
 >> ‘!x. higher_differentiable n (λx. 0) x’
   by (rw [] >> MATCH_MP_TAC higher_differentiable_mono >> qexists ‘SUC n’ >> gs [])
 >> gs [higher_differentiable_def]
QED

Theorem diffn_const_0 :
    !n x. (diffn n (λx. 0) diffl 0) x
Proof
    Induct_on ‘n’ >> rw [DIFF_CONST]
 >> MATCH_MP_TAC diffn_imp_diffl
 >> MP_TAC (Q.SPECL [‘SUC (SUC n)’] higher_differentiable_0) >> rw []
 >> MP_TAC (Q.SPECL [‘SUC n’] higher_differentiable_0) >> rw []
 >> MP_TAC (Q.SPECL [‘n’, ‘λx. 0’] diffl_imp_diffn) >> rw []
 >> rw [diffn_def] >> SELECT_ELIM_TAC
 >> CONJ_TAC >- (fs [higher_differentiable_def])
 >> ‘diffn (SUC n) (λx. 0) = λx. 0’ by METIS_TAC [FUN_EQ_THM, ETA_AX]
 >> POP_ORW >> rw []
 >> MP_TAC (Q.SPECL [‘0’, ‘x’] DIFF_CONST) >> rw []
 >> METIS_TAC [DIFF_UNIQ]
QED

Theorem higher_differentiable_const :
    !n k x. higher_differentiable n (λx. k) x
Proof
    Induct_on ‘n’ >- (gs [higher_differentiable_def])
 >> rw [higher_differentiable_def, FORALL_AND_THM]
 >> qexists ‘0’ >> rw []
 >> Induct_on ‘n’ >- (gs [higher_differentiable_def, DIFF_CONST])
 >> rw [GSYM diffn_SUC, diffn_const]
 >> METIS_TAC [diffn_const_0]
QED

Theorem higher_differentiable_neg_sub :
    !n f a.
      (!x. higher_differentiable n f x) ==>
      !x. higher_differentiable n (λx. f (a - x)) x
Proof
    Induct_on ‘n’ >- (gs [higher_differentiable_def])
 >> rw [FORALL_AND_THM]
 >> MATCH_MP_TAC higher_differentiable_chain
 >> rw [higher_differentiable_def]
 >- (Cases_on ‘n = 0’ >> gs []
     >- (qexists ‘-1’ >> rw [diffl] \\
         ‘!h. a - (x + h) - (a - x) = -h’ by REAL_ARITH_TAC >> POP_ORW \\
         MP_TAC (Q.SPECL [‘λh. -h / h’, ‘λx. -1’, ‘-1’, ‘0’] LIM_EQUAL) \\
         rw [] >> METIS_TAC [LIM_CONST]) \\
     MP_TAC (Q.SPECL [‘a’, ‘SUC n’] higher_differentiable_sub_linear) >> rw [] \\
     fs [higher_differentiable_def, FORALL_AND_THM] \\
     Q.PAT_X_ASSUM ‘!x. ?y. (diffn n (λx. a - x) diffl y) x’ (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
     qexists ‘y’ >> METIS_TAC [])
 >> METIS_TAC [higher_differentiable_sub_linear]
QED
