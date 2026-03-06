(* ========================================================================= *)
(* Properties of real polynomials (not canonically represented).             *)
(* ========================================================================= *)
Theory poly
Ancestors
  pair num prim_rec arithmetic list real lim list pred_set
Libs
  hol88Lib reduceLib pairLib numLib mesonLib tautLib simpLib
  boolSimps numSimps realSimps Ho_Rewrite jrhUtils Canon_Port AC
  realLib


val _ = ParseExtras.temp_loose_equality()

(* ------------------------------------------------------------------------- *)
(* Extras needed to port polyTheory to hol98.                                *)
(* ------------------------------------------------------------------------- *)

fun LIST_INDUCT_TAC g =
  let
    val v = (fst o dest_forall o snd) g
    val v' = mk_var ("t", type_of v)
    val tac =
      CONV_TAC (GEN_ALPHA_CONV v')
      THEN INDUCT_THEN list_INDUCT ASSUME_TAC
      THENL [ALL_TAC,GEN_TAC]
  in
    tac g
  end;

val ARITH_TAC = CONV_TAC ARITH_CONV;
fun ARITH_RULE tm = prove (tm, ARITH_TAC);

val FORALL = LIST_CONJ (map SPEC_ALL (CONJUNCTS EVERY_DEF));

(* Basic extra theorems *)

Theorem FUN_EQ_THM[local]:
   !f g.  (f = g) = (!x. f x = g x)
Proof
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN GEN_TAC THEN REFL_TAC,
    MATCH_ACCEPT_TAC EQ_EXT]
QED

Theorem RIGHT_IMP_EXISTS_THM[local]:
   !P Q. P ==> (?x. Q x) = (?x. P ==> Q x)
Proof
  MESON_TAC []
QED

Theorem LEFT_IMP_EXISTS_THM[local]:
   !P Q. (?x. P x) ==> Q = (!x. P x ==> Q)
Proof
  MESON_TAC []
QED

(* Extra theorems needed about the naturals *)

val NOT_LE = arithmeticTheory.NOT_LESS_EQUAL;
val SUC_INJ = prim_recTheory.INV_SUC_EQ

val LE_EXISTS = arithmeticTheory.LESS_EQ_EXISTS;

Theorem LE_SUC_LT[local]:
   !m n. SUC m <= n = m < n
Proof
  ARITH_TAC
QED

Theorem LT_CASES[local]:
   !m n:num. m < n \/ n < m \/ (m = n)
Proof
  ARITH_TAC
QED

Theorem LE_REFL[local]:
   !n:num. n <= n
Proof ARITH_TAC
QED

(* Extra theorems needed about sets *)

Theorem FINITE_SUBSET[local]:
   !s t. FINITE t /\ s SUBSET t ==> FINITE s
Proof
  MESON_TAC [SUBSET_FINITE]
QED

Theorem FINITE_RULES[local]:
   FINITE {} /\ (!x s. FINITE s ==> FINITE (x INSERT s))
Proof
  MESON_TAC [FINITE_EMPTY, FINITE_INSERT]
QED

Theorem GSPEC_DEF[local]:
   !f. GSPEC f = \v. ?z. f z = (v,T)
Proof
GEN_TAC THEN CONV_TAC FUN_EQ_CONV THEN BETA_TAC THEN GEN_TAC
  THEN ONCE_REWRITE_TAC[BETA_RULE
        (ONCE_REWRITE_CONV[GSYM SPECIFICATION](Term`(\x. GSPEC f x) x`))]
  THEN CONV_TAC (ONCE_DEPTH_CONV ETA_CONV)
  THEN REWRITE_TAC[GSPECIFICATION]
  THEN MESON_TAC[]
QED

(* ------------------------------------------------------------------------- *)
(* Application of polynomial as a real function.                             *)
(* ------------------------------------------------------------------------- *)

Definition poly_def[nocompute]:
  (poly [] x = 0r) /\
  (poly (h::t) x = h + x * poly t x)
End


(* ------------------------------------------------------------------------- *)
(* Arithmetic operations on polynomials. Overloaded (not sure this is wise). *)
(* ------------------------------------------------------------------------- *)

Definition poly_add_def[nocompute]:
  (poly_add [] l2 = l2) /\
  (poly_add (h::t) l2 = if (l2 = []) then h::t
                        else  ((h:real) + HD l2)::poly_add t (TL l2))
End

Overload "+" = Term`poly_add`

val _ = Parse.hide "##";

Definition poly_cmul_def[nocompute]:
  ($## c [] = []) /\
  ($## c (h::t) = (c:real * h) :: ($## c t))
End
val _ = set_fixity "##" (Infixl 600);

Definition poly_neg_def[nocompute]: poly_neg = $## (~(&1))
End

Overload "~" = Term`poly_neg`

Definition poly_mul_def[nocompute]:
  (poly_mul [] l2     = []) /\
  (poly_mul (h::t) l2 = if (t = []) then h ## l2
                        else (h ## l2) + (0r :: poly_mul t l2))
End
Overload "*" = “poly_mul”

Definition poly_exp_def[nocompute]:
  (poly_exp p 0       = [1r]) /\
  (poly_exp p (SUC n) = poly_mul p (poly_exp p n))
End
val _ = set_fixity "poly_exp" (Infixr 700) ;


(* ------------------------------------------------------------------------- *)
(* Differentiation of polynomials (needs an auxiliary function).             *)
(* ------------------------------------------------------------------------- *)

Definition poly_diff_aux_def[nocompute]:
  (poly_diff_aux n [] = []) /\
  (poly_diff_aux n (h::t) = (&n * h) :: poly_diff_aux (SUC n) t)
End

Definition poly_diff_def[nocompute]:
  diff l = if l = [] then [] else poly_diff_aux 1 (TL l)
End

(* ------------------------------------------------------------------------- *)
(* Useful clausifications.                                                   *)
(* ------------------------------------------------------------------------- *)

Theorem POLY_ADD_CLAUSES:
 ([] + p2 = p2) /\
      (p1 + [] = p1) /\
   ((h1::t1) + (h2::t2) = (h1 + h2) :: (t1 + t2))
Proof
  REWRITE_TAC[poly_add_def, NOT_CONS_NIL, HD, TL] THEN
  SPEC_TAC(Term`p1:real list`,Term`p1:real list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[poly_add_def]
QED

Theorem POLY_CMUL_CLAUSES:
 (c ## [] = []) /\
      (c ## (h::t) = (c * h) :: (c ## t))
Proof
  REWRITE_TAC[poly_cmul_def]
QED

Theorem POLY_NEG_CLAUSES:
 (poly_neg [] = []) /\
      (poly_neg (h::t) = ~h::poly_neg t)
Proof
  REWRITE_TAC[poly_neg_def, POLY_CMUL_CLAUSES, REAL_MUL_LNEG, REAL_MUL_LID]
QED

Theorem POLY_MUL_CLAUSES:
 ([] * p2 = []) /\
    ([h1] * p2 = h1 ## p2) /\
   ((h1::k1::t1) * p2 = (h1 ## p2) + (&0 :: ((k1::t1) * p2)))
Proof
  REWRITE_TAC[poly_mul_def, NOT_CONS_NIL]
QED

Theorem POLY_DIFF_CLAUSES:
 (diff [] = []) /\
   (diff [c] = []) /\
   (diff (h::t) = poly_diff_aux 1 t)
Proof
  REWRITE_TAC[poly_diff_def, NOT_CONS_NIL, HD, TL, poly_diff_aux_def]
QED

(* ------------------------------------------------------------------------- *)
(* Various natural consequences of syntactic definitions.                    *)
(* ------------------------------------------------------------------------- *)

Theorem POLY_ADD:
 !p1 p2 x. poly (p1 + p2) x = poly p1 x + poly p2 x
Proof
  LIST_INDUCT_TAC THEN REWRITE_TAC[poly_add_def, poly_def, REAL_ADD_LID] THEN
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[NOT_CONS_NIL, HD, TL, poly_def, REAL_ADD_RID] THEN
  REAL_ARITH_TAC
QED

Theorem POLY_CMUL:
 !p c x. poly (c ## p) x = c * poly p x
Proof
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[poly_def, poly_cmul_def] THEN
  REAL_ARITH_TAC
QED

Theorem POLY_NEG:
 !p x. poly (poly_neg p) x = ~(poly p x)
Proof
  REWRITE_TAC[poly_neg_def, POLY_CMUL] THEN
  REAL_ARITH_TAC
QED

Theorem POLY_MUL:
 !x p1 p2. poly (p1 * p2) x = poly p1 x * poly p2 x
Proof
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[poly_mul_def, poly_def, REAL_MUL_LZERO, POLY_CMUL, POLY_ADD] THEN
  SPEC_TAC(Term`h:real`,Term`h:real`) THEN
  SPEC_TAC(Term`t:real list`,Term`t:real list`) THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[poly_mul_def, POLY_CMUL, POLY_ADD, poly_def, POLY_CMUL,
    REAL_MUL_RZERO, REAL_ADD_RID, NOT_CONS_NIL] THEN
  ASM_REWRITE_TAC[POLY_ADD, POLY_CMUL, poly_def] THEN
  REAL_ARITH_TAC
QED

Theorem POLY_EXP:
 !p n (x:real). poly (p poly_exp n) x = (poly p x) pow n
Proof
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[poly_exp_def, pow, POLY_MUL] THEN
  REWRITE_TAC[poly_def] THEN REAL_ARITH_TAC
QED

(* ------------------------------------------------------------------------- *)
(* The derivative is a bit more complicated.                                 *)
(* ------------------------------------------------------------------------- *)

Theorem POLY_DIFF_LEMMA:
 !l n x. ((\x. (x pow (SUC n)) * poly l x) diffl
                   ((x pow n) * poly (poly_diff_aux (SUC n) l) x))(x)
Proof
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[poly_def, poly_diff_aux_def, REAL_MUL_RZERO, DIFF_CONST] THEN
  MAP_EVERY X_GEN_TAC [(Term`n:num`), (Term`x:real`)] THEN
  REWRITE_TAC[REAL_LDISTRIB, REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[REAL_MUL_SYM] (CONJUNCT2 pow))] THEN
  POP_ASSUM(MP_TAC o SPECL [(Term`SUC n`), (Term`x:real`)]) THEN
  SUBGOAL_THEN ((Term`(((\x. (x pow (SUC n)) * h)) diffl
                        ((x pow n) * &(SUC n) * h))(x)`))
  (fn th => DISCH_THEN(MP_TAC o CONJ th)) THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    MP_TAC(SPEC ((Term`\x. x pow (SUC n)`)) DIFF_CMUL) THEN BETA_TAC THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(SPEC ((Term`SUC n`)) DIFF_POW) THEN REWRITE_TAC[SUC_SUB1] THEN
    DISCH_THEN(MATCH_ACCEPT_TAC o ONCE_REWRITE_RULE[REAL_MUL_SYM]),
    DISCH_THEN(MP_TAC o MATCH_MP DIFF_ADD) THEN BETA_TAC THEN
    REWRITE_TAC[REAL_MUL_ASSOC]]
QED

Theorem POLY_DIFF:
 !l x. ((\x. poly l x) diffl (poly (diff l) x))(x)
Proof
  LIST_INDUCT_TAC THEN REWRITE_TAC[POLY_DIFF_CLAUSES] THEN
  ONCE_REWRITE_TAC[SYM(ETA_CONV (Term`\x. poly l x`))] THEN
  REWRITE_TAC[poly_def, DIFF_CONST] THEN
  MAP_EVERY X_GEN_TAC [(Term`x:real`)] THEN
  MP_TAC(SPECL [(Term`t:real list`), (Term`0:num`), (Term`x:real`)]
         POLY_DIFF_LEMMA) THEN
  REWRITE_TAC[SYM ONE] THEN REWRITE_TAC[pow, REAL_MUL_LID] THEN
  REWRITE_TAC[POW_1] THEN
  DISCH_THEN(MP_TAC o CONJ (SPECL [(Term`h:real`), (Term`x:real`)] DIFF_CONST))
  THEN DISCH_THEN(MP_TAC o MATCH_MP DIFF_ADD) THEN BETA_TAC THEN
  REWRITE_TAC[REAL_ADD_LID]
QED

(* ------------------------------------------------------------------------- *)
(* Trivial consequences.                                                     *)
(* ------------------------------------------------------------------------- *)

Theorem POLY_DIFFERENTIABLE:
 !l x. (\x. poly l x) differentiable x
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[differentiable] THEN
  EXISTS_TAC (Term`poly (diff l) x`) THEN
  REWRITE_TAC[POLY_DIFF]
QED

Theorem POLY_CONT:
 !l x. (\x. poly l x) contl x
Proof
  REPEAT GEN_TAC THEN MATCH_MP_TAC DIFF_CONT THEN
  EXISTS_TAC (Term`poly (diff l) x`) THEN
  MATCH_ACCEPT_TAC POLY_DIFF
QED

Theorem POLY_IVT_POS:
 !p a b. a < b /\ poly p a < &0 /\ poly p b > &0
           ==> ?x. a < x /\ x < b /\ (poly p x = &0)
Proof
  REWRITE_TAC[real_gt] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [(Term`\x. poly p x`), (Term`a:real`), (Term`b:real`), (Term`&0`)] IVT) THEN
  SIMP_TAC bool_ss [POLY_CONT] THEN
  EVERY_ASSUM(fn th => REWRITE_TAC[MATCH_MP REAL_LT_IMP_LE th]) THEN
  DISCH_THEN(X_CHOOSE_THEN (Term`x:real`) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC (Term`x:real`) THEN ASM_REWRITE_TAC[REAL_LT_LE] THEN
  CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_LT_REFL]) THEN
  FIRST_ASSUM CONTR_TAC
QED

Theorem POLY_IVT_NEG:
 !p a b. a < b /\ poly p a > &0 /\ poly p b < &0
           ==> ?x. a < x /\ x < b /\ (poly p x = &0)
Proof
  REPEAT STRIP_TAC THEN MP_TAC(SPEC (Term`poly_neg p`) POLY_IVT_POS) THEN
  REWRITE_TAC[POLY_NEG,
              REAL_ARITH (Term`(~x < &0 = x > &0) /\ (~x > &0 = x < &0)`)] THEN
  DISCH_THEN(MP_TAC o SPECL [(Term`a:real`), (Term`b:real`)]) THEN
  ASM_REWRITE_TAC[REAL_ARITH (Term`(~x = &0) = (x = &0)`)]
QED

Theorem POLY_MVT:
 !p a b. a < b ==>
           ?x. a < x /\ x < b /\
              (poly p b - poly p a = (b - a) * poly (diff p) x)
Proof
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [(Term`poly p`), (Term`a:real`), (Term`b:real`)] MVT) THEN
  ASM_REWRITE_TAC[CONV_RULE(DEPTH_CONV ETA_CONV) (SPEC_ALL POLY_CONT),
    CONV_RULE(DEPTH_CONV ETA_CONV) (SPEC_ALL POLY_DIFFERENTIABLE)] THEN
  DISCH_THEN(X_CHOOSE_THEN (Term`l:real`) MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN (Term`x:real`) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC (Term`x:real`) THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC DIFF_UNIQ THEN
  EXISTS_TAC (Term`poly p`) THEN EXISTS_TAC (Term`x:real`) THEN
  ASM_REWRITE_TAC[CONV_RULE(DEPTH_CONV ETA_CONV) (SPEC_ALL POLY_DIFF)]
QED

(* ------------------------------------------------------------------------- *)
(* Lemmas.                                                                   *)
(* ------------------------------------------------------------------------- *)

Theorem POLY_ADD_RZERO:
 !p. poly (p + []) = poly p
Proof
  REWRITE_TAC[FUN_EQ_THM, POLY_ADD, poly_def, REAL_ADD_RID]
QED

Theorem POLY_MUL_ASSOC:
 !p q r. poly (p * (q * r)) = poly ((p * q) * r)
Proof
  REWRITE_TAC[FUN_EQ_THM, POLY_MUL, REAL_MUL_ASSOC]
QED

Theorem POLY_EXP_ADD:
 !d n p. poly(p poly_exp (n + d)) = poly(p poly_exp n * p poly_exp d)
Proof
  REWRITE_TAC[FUN_EQ_THM, POLY_MUL] THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[POLY_MUL, ADD_CLAUSES, poly_exp_def, poly_def] THEN
  REAL_ARITH_TAC
QED

(* ------------------------------------------------------------------------- *)
(* Lemmas for derivatives.                                                   *)
(* ------------------------------------------------------------------------- *)

Theorem POLY_DIFF_AUX_ADD:
!p1 p2 n. poly (poly_diff_aux n (p1 + p2)) =
             poly (poly_diff_aux n p1 + poly_diff_aux n p2)
Proof
  REPEAT(LIST_INDUCT_TAC THEN REWRITE_TAC[poly_diff_aux_def, poly_add_def]) THEN
  ASM_REWRITE_TAC[poly_diff_aux_def, FUN_EQ_THM, poly_def, NOT_CONS_NIL, HD, TL] THEN
  REAL_ARITH_TAC
QED

Theorem POLY_DIFF_AUX_CMUL:
 !p c n. poly (poly_diff_aux n (c ## p)) =
           poly (c ## poly_diff_aux n p)
Proof
  LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC real_ac_ss [FUN_EQ_THM, poly_def, poly_diff_aux_def, poly_cmul_def]
QED

Theorem POLY_DIFF_AUX_NEG:
 !p n.  poly (poly_diff_aux n (poly_neg p)) =
          poly (poly_neg (poly_diff_aux n p))
Proof
  REWRITE_TAC[poly_neg_def, POLY_DIFF_AUX_CMUL]
QED

Theorem POLY_DIFF_AUX_MUL_LEMMA:
 !p n. poly (poly_diff_aux (SUC n) p) = poly (poly_diff_aux n p + p)
Proof
  LIST_INDUCT_TAC THEN REWRITE_TAC[poly_diff_aux_def, poly_add_def, NOT_CONS_NIL] THEN
  ASM_REWRITE_TAC[HD, TL, poly_def, FUN_EQ_THM] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC, REAL_ADD_RDISTRIB, REAL_MUL_LID]
QED

(* ------------------------------------------------------------------------- *)
(* Final results for derivatives.                                            *)
(* ------------------------------------------------------------------------- *)

Theorem POLY_DIFF_ADD:
 !p1 p2. poly (diff (p1 + p2)) =
           poly (diff p1  + diff p2)
Proof
  REPEAT LIST_INDUCT_TAC THEN
  REWRITE_TAC[poly_add_def, poly_diff_def, NOT_CONS_NIL, POLY_ADD_RZERO] THEN
  ASM_REWRITE_TAC[HD, TL, POLY_DIFF_AUX_ADD]
QED

Theorem POLY_DIFF_CMUL:
 !p c. poly (diff (c ## p)) = poly (c ## diff p)
Proof
  LIST_INDUCT_TAC THEN REWRITE_TAC[poly_diff_def, poly_cmul_def] THEN
  REWRITE_TAC[NOT_CONS_NIL, HD, TL, POLY_DIFF_AUX_CMUL]
QED

Theorem POLY_DIFF_NEG:
 !p. poly (diff (poly_neg p)) = poly (poly_neg (diff p))
Proof
  REWRITE_TAC[poly_neg_def, POLY_DIFF_CMUL]
QED

Theorem POLY_DIFF_MUL_LEMMA:
 !t h. poly (diff (CONS h t)) =
         poly (CONS (&0) (diff t) + t)
Proof
  REWRITE_TAC[poly_diff_def, NOT_CONS_NIL] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[poly_diff_aux_def, NOT_CONS_NIL, HD, TL] THENL
   [REWRITE_TAC[FUN_EQ_THM, poly_def, poly_add_def, REAL_MUL_RZERO, REAL_ADD_LID],
    REWRITE_TAC[FUN_EQ_THM, poly_def, POLY_DIFF_AUX_MUL_LEMMA, POLY_ADD] THEN
    REAL_ARITH_TAC]
QED

Theorem POLY_DIFF_MUL:
 !p1 p2. poly (diff (p1 * p2)) =
           poly (p1 * diff p2 + diff p1 * p2)
Proof
  LIST_INDUCT_TAC THEN REWRITE_TAC[poly_mul_def] THENL
   [REWRITE_TAC[poly_diff_def, poly_add_def, poly_mul_def], ALL_TAC] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[POLY_DIFF_CLAUSES] THEN
    REWRITE_TAC[poly_add_def, poly_mul_def, POLY_ADD_RZERO, POLY_DIFF_CMUL],
    ALL_TAC] THEN
  REWRITE_TAC[FUN_EQ_THM, POLY_DIFF_ADD, POLY_ADD] THEN
  REWRITE_TAC[poly_def, POLY_ADD, POLY_DIFF_MUL_LEMMA, POLY_MUL] THEN
  ASM_REWRITE_TAC[POLY_DIFF_CMUL, POLY_ADD, POLY_MUL] THEN
  REAL_ARITH_TAC
QED

Theorem POLY_DIFF_EXP:
 !p n. poly (diff (p poly_exp (SUC n))) =
         poly (&(SUC n) ## (p poly_exp n) * diff p)
Proof
  GEN_TAC THEN INDUCT_TAC THEN ONCE_REWRITE_TAC[poly_exp_def] THENL
   [REWRITE_TAC[poly_exp_def, POLY_DIFF_MUL] THEN
    REWRITE_TAC[FUN_EQ_THM, POLY_MUL, POLY_ADD, POLY_CMUL] THEN
    REWRITE_TAC[poly_def, POLY_DIFF_CLAUSES, ADD1, ADD_CLAUSES] THEN
    REAL_ARITH_TAC,
    REWRITE_TAC[POLY_DIFF_MUL] THEN
    ASM_REWRITE_TAC[POLY_MUL, POLY_ADD, FUN_EQ_THM, POLY_CMUL] THEN
    REWRITE_TAC[poly_exp_def, POLY_MUL] THEN
    REWRITE_TAC[ADD1, GSYM REAL_OF_NUM_ADD] THEN
    REAL_ARITH_TAC]
QED

Theorem POLY_DIFF_EXP_PRIME:
 !n a. poly (diff ([~a; &1] poly_exp (SUC n))) =
         poly (&(SUC n) ## ([~a; &1] poly_exp n))
Proof
  REPEAT GEN_TAC THEN SIMP_TAC real_ac_ss [POLY_DIFF_EXP] THEN
  SIMP_TAC real_ac_ss [FUN_EQ_THM, POLY_CMUL, POLY_MUL] THEN
  SIMP_TAC real_ac_ss [poly_diff_def, poly_diff_aux_def, TL, NOT_CONS_NIL] THEN
  SIMP_TAC real_ac_ss [poly_def] THEN REAL_ARITH_TAC
QED

(* ------------------------------------------------------------------------- *)
(* Key property that f(a) = 0 ==> (x - a) divides p(x). Very delicate!       *)
(* ------------------------------------------------------------------------- *)

Theorem POLY_LINEAR_REM:
 !t h. ?q r. h::t = [r] + [~a; &1] * q
Proof
  LIST_INDUCT_TAC THEN REWRITE_TAC[] THENL
   [GEN_TAC THEN EXISTS_TAC (Term`[]:real list`) THEN
    EXISTS_TAC (Term`h:real`) THEN
    REWRITE_TAC[poly_add_def, poly_mul_def, poly_cmul_def, NOT_CONS_NIL] THEN
    REWRITE_TAC[HD, TL, REAL_ADD_RID],
    X_GEN_TAC (Term`k:real`) THEN
    POP_ASSUM(STRIP_ASSUME_TAC o SPEC (Term`h:real`)) THEN
    EXISTS_TAC (Term`CONS (r:real) q`) THEN
    EXISTS_TAC (Term`r * a + k:real`) THEN
    ASM_REWRITE_TAC[POLY_ADD_CLAUSES, POLY_MUL_CLAUSES, poly_cmul_def] THEN
    REWRITE_TAC[CONS_11] THEN CONJ_TAC THENL
     [REAL_ARITH_TAC, ALL_TAC] THEN
    SPEC_TAC((Term`q:real list`),(Term`q:real list`)) THEN
    LIST_INDUCT_TAC THEN
    REWRITE_TAC[POLY_ADD_CLAUSES, POLY_MUL_CLAUSES, poly_cmul_def] THEN
    REWRITE_TAC[REAL_ADD_RID, REAL_MUL_LID] THEN
    SIMP_TAC real_ac_ss []]
QED

Theorem POLY_LINEAR_DIVIDES:
 !a p. (poly p a = &0) = (p = []) \/ ?q. p = [~a; &1] * q
Proof
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[poly_def], ALL_TAC] THEN
  EQ_TAC THEN STRIP_TAC THENL
   [DISJ2_TAC THEN STRIP_ASSUME_TAC(SPEC_ALL POLY_LINEAR_REM) THEN
    EXISTS_TAC (Term`q:real list`) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN (Term`r = &0`) SUBST_ALL_TAC THENL
     [UNDISCH_TAC (Term`poly (CONS h t) a = &0`) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[POLY_ADD, POLY_MUL] THEN
      REWRITE_TAC[poly_def, REAL_MUL_RZERO, REAL_ADD_RID, REAL_MUL_RID] THEN
      REWRITE_TAC[REAL_ARITH (Term`~a + a = &0`)] THEN REAL_ARITH_TAC,
      REWRITE_TAC[poly_mul_def] THEN REWRITE_TAC[NOT_CONS_NIL] THEN
      SPEC_TAC((Term`q:real list`),(Term`q:real list`)) THEN LIST_INDUCT_TAC THENL
       [REWRITE_TAC[poly_cmul_def, poly_add_def, NOT_CONS_NIL, HD, TL, REAL_ADD_LID],
        REWRITE_TAC[poly_cmul_def, poly_add_def, NOT_CONS_NIL, HD, TL, REAL_ADD_LID]]],
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[poly_def],
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[poly_def] THEN
    REWRITE_TAC[POLY_MUL] THEN REWRITE_TAC[poly_def] THEN
    REWRITE_TAC[poly_def, REAL_MUL_RZERO, REAL_ADD_RID, REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_ARITH (Term`~a + a = &0`)] THEN REAL_ARITH_TAC]
QED

(* ------------------------------------------------------------------------- *)
(* Thanks to the finesse of the above, we can use length rather than degree. *)
(* ------------------------------------------------------------------------- *)

Theorem POLY_LENGTH_MUL:
 !q. LENGTH([~a; &1] * q) = SUC(LENGTH q)
Proof
  let
    val lemma = prove
   ((Term`!p h k a. LENGTH (k ## p + CONS h (a ## p)) = SUC(LENGTH p)`),
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[poly_cmul_def, POLY_ADD_CLAUSES, LENGTH])
  in
    REWRITE_TAC[poly_mul_def, NOT_CONS_NIL, lemma]
  end
QED

(* ------------------------------------------------------------------------- *)
(* Thus a nontrivial polynomial of degree n has no more than n roots.        *)
(* ------------------------------------------------------------------------- *)

Theorem POLY_ROOTS_INDEX_LEMMA:
 !n. !p. ~(poly p = poly []) /\ (LENGTH p = n)
           ==> ?i. !x. (poly p (x) = &0) ==> ?m. m <= n /\ (x = i m)
Proof
  INDUCT_TAC THENL
   [SIMP_TAC real_ac_ss [LENGTH_NIL],
    REPEAT STRIP_TAC THEN ASM_CASES_TAC (Term`?a. poly p a = &0`) THENL
     [UNDISCH_TAC (Term`?a. poly p a = &0`) THEN DISCH_THEN(CHOOSE_THEN MP_TAC) THEN
      GEN_REWRITE_TAC LAND_CONV [POLY_LINEAR_DIVIDES] THEN
      DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL [ASM_MESON_TAC[], ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN (Term`q:real list`) SUBST_ALL_TAC) THEN
      FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
      UNDISCH_TAC (Term`~(poly ([~a; &1] * q) = poly [])`) THEN
      POP_ASSUM MP_TAC THEN REWRITE_TAC[POLY_LENGTH_MUL, SUC_INJ] THEN
      DISCH_TAC THEN ASM_CASES_TAC (Term`poly q = poly []`) THENL
       [ASM_REWRITE_TAC[POLY_MUL, poly_def, REAL_MUL_RZERO, FUN_EQ_THM],
        DISCH_THEN(K ALL_TAC)] THEN
      DISCH_THEN(MP_TAC o SPEC (Term`q:real list`)) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_TAC (Term`i:num->real`)) THEN
      EXISTS_TAC (Term`\m. if m = SUC n then (a:real) else i m`) THEN
      REWRITE_TAC[POLY_MUL, LE, REAL_ENTIRE] THEN
      X_GEN_TAC (Term`x:real`) THEN DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
       [DISCH_THEN(fn th => EXISTS_TAC (Term`SUC n`) THEN MP_TAC th) THEN
        SIMP_TAC real_ac_ss [] THEN REWRITE_TAC[poly_def] THEN REAL_ARITH_TAC,
        DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
        DISCH_THEN(X_CHOOSE_THEN (Term`m:num`) STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (Term`m:num`) THEN ASM_SIMP_TAC real_ac_ss [] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC (Term`m:num <= n`) THEN ASM_SIMP_TAC real_ac_ss []],
      UNDISCH_TAC (Term`~(?a. poly p a = &0)`) THEN
      REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_TAC
      THEN ASM_SIMP_TAC bool_ss []]]
QED

Theorem POLY_ROOTS_INDEX_LENGTH:
 !p. ~(poly p = poly [])
       ==> ?i. !x. (poly p(x) = &0) ==> ?n. n <= LENGTH p /\ (x = i n)
Proof
  MESON_TAC[POLY_ROOTS_INDEX_LEMMA]
QED

Theorem POLY_ROOTS_FINITE_LEMMA:
 !p. ~(poly p = poly [])
       ==> ?N i. !x. (poly p(x) = &0) ==> ?n:num. n < N /\ (x = i n)
Proof
  MESON_TAC[POLY_ROOTS_INDEX_LENGTH, LT_SUC_LE]
QED

Theorem FINITE_LEMMA:
 !i N P. (!x. P x ==> ?n:num. n < N /\ (x = i n))
           ==> ?a. !x. P x ==> x < a
Proof
  GEN_TAC THEN ONCE_REWRITE_TAC[RIGHT_IMP_EXISTS_THM] THEN INDUCT_TAC THENL
   [REWRITE_TAC[LT] THEN MESON_TAC[], ALL_TAC] THEN
  X_GEN_TAC (Term`P:real->bool`) THEN
  POP_ASSUM(MP_TAC o SPEC (Term`\z. P z /\ ~(z = (i:num->real) N)`)) THEN
  DISCH_THEN(X_CHOOSE_TAC (Term`a:real`)) THEN
  EXISTS_TAC (Term`abs(a) + abs(i(N:num)) + &1`) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[LT] THEN
  MP_TAC(REAL_ARITH (Term`!x v. x < abs(v) + abs(x) + &1`)) THEN
  MP_TAC(REAL_ARITH (Term`!u v x. x < v ==> x < abs(v) + abs(u) + &1`)) THEN
  MESON_TAC[]
QED

Theorem POLY_ROOTS_FINITE:
 !p. ~(poly p = poly []) =
       ?N i. !x. (poly p(x) = &0) ==> ?n:num. n < N /\ (x = i n)
Proof
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[POLY_ROOTS_FINITE_LEMMA] THEN
  REWRITE_TAC[FUN_EQ_THM, LEFT_IMP_EXISTS_THM, NOT_FORALL_THM, poly_def] THEN
  MP_TAC(GENL [(Term`i:num->real`), (Term`N:num`)]
   (SPECL [(Term`i:num->real`), (Term`N:num`), (Term`\x. poly p x = &0`)] FINITE_LEMMA)) THEN
  REWRITE_TAC[] THEN MESON_TAC[REAL_LT_REFL]
QED

(* ------------------------------------------------------------------------- *)
(* Hence get entirety and cancellation for polynomials.                      *)
(* ------------------------------------------------------------------------- *)

Theorem POLY_ENTIRE_LEMMA:
 !p q. ~(poly p = poly []) /\ ~(poly q = poly [])
         ==> ~(poly (p * q) = poly [])
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[POLY_ROOTS_FINITE] THEN
  DISCH_THEN(CONJUNCTS_THEN MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN (Term`N2:num`) (X_CHOOSE_TAC (Term`i2:num->real`))) THEN
  DISCH_THEN(X_CHOOSE_THEN (Term`N1:num`) (X_CHOOSE_TAC (Term`i1:num->real`))) THEN
  EXISTS_TAC (Term`N1 + N2:num`) THEN
  EXISTS_TAC (Term`\n:num. if n < N1 then i1(n):real else i2(n - N1)`) THEN
  X_GEN_TAC (Term`x:real`) THEN REWRITE_TAC[REAL_ENTIRE, POLY_MUL] THEN
  DISCH_THEN(DISJ_CASES_THEN (ANTE_RES_THEN (X_CHOOSE_TAC (Term`n:num`)))) THENL
   [EXISTS_TAC (Term`n:num`) THEN ASM_SIMP_TAC real_ac_ss [],
    EXISTS_TAC (Term`N1 + n:num`) THEN ASM_SIMP_TAC real_ac_ss [LT_ADD_LCANCEL]]
QED

Theorem POLY_ENTIRE:
 !p q. (poly (p * q) = poly []) = (poly p = poly []) \/ (poly q = poly [])
Proof
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[POLY_ENTIRE_LEMMA],
    REWRITE_TAC[FUN_EQ_THM, POLY_MUL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO, REAL_MUL_LZERO, poly_def]]
QED

Theorem POLY_MUL_LCANCEL:
 !p q r. (poly (p * q) = poly (p * r)) =
           (poly p = poly []) \/ (poly q = poly r)
Proof
  let
    val lemma1 = prove
     ((Term`!p q. (poly (p + poly_neg q) = poly []) = (poly p = poly q)`),
      REWRITE_TAC[FUN_EQ_THM, POLY_ADD, POLY_NEG, poly_def] THEN
      REWRITE_TAC[REAL_ARITH (Term`(p + ~q = &0) = (p = q)`)])
    val lemma2 = prove
     ((Term`!p q r. poly (p * q + poly_neg(p * r)) = poly (p * (q + poly_neg(r)))`),
      REWRITE_TAC[FUN_EQ_THM, POLY_ADD, POLY_NEG, POLY_MUL] THEN
      REAL_ARITH_TAC)
  in
    ONCE_REWRITE_TAC[GSYM lemma1] THEN
    REWRITE_TAC[lemma2, POLY_ENTIRE] THEN
    REWRITE_TAC[lemma1]
  end
QED

Theorem POLY_EXP_EQ_0:
 !p n. (poly (p poly_exp n) = poly []) = (poly p = poly []) /\ ~(n = 0)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM, poly_def] THEN
  REWRITE_TAC [LEFT_AND_FORALL_THM] THEN AP_TERM_TAC THEN ABS_TAC THEN
  SPEC_TAC((Term`n:num`),(Term`n:num`)) THEN INDUCT_TAC THEN
  SIMP_TAC real_ac_ss [poly_exp_def, poly_def, REAL_MUL_RZERO, REAL_ADD_RID,
    REAL_OF_NUM_EQ, NOT_SUC] THEN
  ASM_REWRITE_TAC[POLY_MUL, poly_def, REAL_ENTIRE] THEN
  MESON_TAC []
QED

Theorem POLY_PRIME_EQ_0:
 !a. ~(poly [a; &1] = poly [])
Proof
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM, poly_def] THEN
  DISCH_THEN(MP_TAC o SPEC (Term`&1 - a`)) THEN
  REAL_ARITH_TAC
QED

Theorem POLY_EXP_PRIME_EQ_0:
 !a n. ~(poly ([a; &1] poly_exp n) = poly [])
Proof
  MESON_TAC[POLY_EXP_EQ_0, POLY_PRIME_EQ_0]
QED

(* ------------------------------------------------------------------------- *)
(* Can also prove a more "constructive" notion of polynomial being trivial.  *)
(* ------------------------------------------------------------------------- *)

Theorem POLY_ZERO_LEMMA:
 !h t. (poly (CONS h t) = poly []) ==> (h = &0) /\ (poly t = poly [])
Proof
  let
    val lemma = REWRITE_RULE[FUN_EQ_THM, poly_def] POLY_ROOTS_FINITE
  in
    REPEAT GEN_TAC
    THEN SIMP_TAC real_ac_ss [FUN_EQ_THM, poly_def]
    THEN ASM_CASES_TAC (Term`h = &0`)
    THEN ASM_SIMP_TAC real_ac_ss []
    THENL [
      SIMP_TAC real_ac_ss [REAL_ADD_LID]
      THEN CONV_TAC CONTRAPOS_CONV
      THEN DISCH_THEN(MP_TAC o REWRITE_RULE[lemma])
      THEN DISCH_THEN(X_CHOOSE_THEN (Term`N:num`) (X_CHOOSE_TAC (Term`i:num->real`)))
      THEN MP_TAC
        (SPECL [(Term`i:num->real`), (Term`N:num`), (Term`\x. poly t x = &0`)] FINITE_LEMMA)
      THEN ASM_SIMP_TAC real_ac_ss []
      THEN DISCH_THEN(X_CHOOSE_TAC (Term`a:real`))
      THEN EXISTS_TAC (Term`abs(a) + &1`)
      THEN POP_ASSUM (MP_TAC o SPEC (Term`abs(a) + &1`))
      THEN REWRITE_TAC [REAL_ENTIRE]
      THEN REAL_ARITH_TAC,
      EXISTS_TAC (Term`&0`)
      THEN ASM_SIMP_TAC real_ac_ss []
    ]
  end
QED

Theorem POLY_ZERO:
 !p. (poly p = poly []) = EVERY (\c. c = &0) p
Proof
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FORALL] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP POLY_ZERO_LEMMA) THEN ASM_REWRITE_TAC[],
    POP_ASSUM(SUBST1_TAC o SYM) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[FUN_EQ_THM, poly_def] THEN REAL_ARITH_TAC]
QED

(* ------------------------------------------------------------------------- *)
(* Useful triviality.                                                        *)
(* ------------------------------------------------------------------------- *)

Theorem POLY_DIFF_AUX_ISZERO:
 !p n. EVERY (\c. c = &0) (poly_diff_aux (SUC n) p) =
         EVERY (\c. c = &0) p
Proof
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC
   [FORALL, poly_diff_aux_def, REAL_ENTIRE, REAL_OF_NUM_EQ, NOT_SUC]
QED


Theorem POLY_DIFF_ISZERO:
 !p. (poly (diff p) = poly []) ==> ?h. poly p = poly [h]
Proof
  REWRITE_TAC[POLY_ZERO] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[POLY_DIFF_CLAUSES, FORALL] THENL
   [EXISTS_TAC (Term`&0`) THEN REWRITE_TAC[FUN_EQ_THM, poly_def] THEN REAL_ARITH_TAC,
    REWRITE_TAC[ONE, POLY_DIFF_AUX_ISZERO] THEN
    REWRITE_TAC[GSYM POLY_ZERO] THEN DISCH_TAC THEN
    EXISTS_TAC (Term`h:real`) THEN ASM_REWRITE_TAC[poly_def, FUN_EQ_THM]]
QED

Theorem POLY_DIFF_ZERO:
 !p. (poly p = poly []) ==> (poly (diff p) = poly [])
Proof
  REWRITE_TAC[POLY_ZERO] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[poly_diff_def, NOT_CONS_NIL] THEN
  REWRITE_TAC[FORALL, TL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SPEC_TAC((Term`1:num`),(Term`n:num`)) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  SPEC_TAC((Term`t:real list`),(Term`t:real list`)) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[FORALL, poly_diff_aux_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]
QED

Theorem POLY_DIFF_WELLDEF:
 !p q. (poly p = poly q) ==> (poly (diff p) = poly (diff q))
Proof
  REPEAT STRIP_TAC THEN MP_TAC(SPEC (Term`p + poly_neg(q)`) POLY_DIFF_ZERO) THEN
  REWRITE_TAC[FUN_EQ_THM, POLY_DIFF_ADD, POLY_DIFF_NEG, POLY_ADD] THEN
  ASM_REWRITE_TAC[POLY_NEG, poly_def, REAL_ARITH (Term`a + ~a = &0`)] THEN
  REWRITE_TAC[REAL_ARITH (Term`(a + ~b = &0) = (a = b)`)]
QED

(* ------------------------------------------------------------------------- *)
(* Basics of divisibility.                                                   *)
(* ------------------------------------------------------------------------- *)

val poly_divides = new_infixl_definition ("poly_divides",
  (Term`$poly_divides p1 p2 = ?q. poly p2 = poly (p1 * q)`), 475);

Theorem POLY_PRIMES:
 !a p q. [a; &1] poly_divides (p * q)
                           =
               [a; &1] poly_divides p \/ [a; &1] poly_divides q
Proof
 REPEAT GEN_TAC THEN REWRITE_TAC[poly_divides, POLY_MUL, FUN_EQ_THM, poly_def] THEN
 REWRITE_TAC[REAL_MUL_RZERO, REAL_ADD_RID, REAL_MUL_RID] THEN EQ_TAC THENL
 [DISCH_THEN(X_CHOOSE_THEN (Term`r:real list`)
  (MP_TAC o SPEC (Term`~a:real`))) THEN
   REWRITE_TAC[REAL_ENTIRE, GSYM real_sub, REAL_SUB_REFL, REAL_MUL_LZERO] THEN
    DISCH_THEN DISJ_CASES_TAC THENL [DISJ1_TAC, DISJ2_TAC] THEN
    (POP_ASSUM(MP_TAC o REWRITE_RULE[POLY_LINEAR_DIVIDES]) THEN
     REWRITE_TAC[REAL_NEG_NEG] THEN
     DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN (Term`s:real list`) SUBST_ALL_TAC)) THENL
      [EXISTS_TAC (Term`[]:real list`) THEN REWRITE_TAC[poly_def, REAL_MUL_RZERO],
       EXISTS_TAC (Term`s:real list`) THEN GEN_TAC THEN
       REWRITE_TAC[POLY_MUL, poly_def] THEN REAL_ARITH_TAC]),
    DISCH_THEN(DISJ_CASES_THEN(X_CHOOSE_TAC (Term`s:real list`))) THEN
    ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC (Term`s * q`), EXISTS_TAC (Term`p * s`)] THEN
    GEN_TAC THEN REWRITE_TAC[POLY_MUL] THEN REAL_ARITH_TAC]
QED

Theorem POLY_DIVIDES_REFL:
 !p. p poly_divides p
Proof
  GEN_TAC THEN REWRITE_TAC[poly_divides] THEN EXISTS_TAC (Term`[&1]`) THEN
  REWRITE_TAC[FUN_EQ_THM, POLY_MUL, poly_def] THEN REAL_ARITH_TAC
QED

Theorem POLY_DIVIDES_TRANS:
 !p q r. p poly_divides q /\ q poly_divides r ==> p poly_divides r
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[poly_divides] THEN
  DISCH_THEN(CONJUNCTS_THEN MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN (Term`s:real list`) ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN (Term`t:real list`) ASSUME_TAC) THEN
  EXISTS_TAC (Term`t * s`) THEN
  ASM_REWRITE_TAC[FUN_EQ_THM, POLY_MUL, REAL_MUL_ASSOC]
QED

Theorem POLY_DIVIDES_EXP:
 !p m n. m <= n ==> (p poly_exp m) poly_divides (p poly_exp n)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN (Term`d:num`) SUBST1_TAC) THEN
  SPEC_TAC((Term`d:num`),(Term`d:num`)) THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES, POLY_DIVIDES_REFL] THEN
  MATCH_MP_TAC POLY_DIVIDES_TRANS THEN
  EXISTS_TAC (Term`p poly_exp (m + d)`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[poly_divides] THEN EXISTS_TAC (Term`p:real list`) THEN
  REWRITE_TAC[poly_exp_def, FUN_EQ_THM, POLY_MUL] THEN
  REAL_ARITH_TAC
QED

Theorem POLY_EXP_DIVIDES:
 !p q m n.
      (p poly_exp n) poly_divides q /\ m <= n ==> (p poly_exp m) poly_divides q
Proof
  MESON_TAC[POLY_DIVIDES_TRANS, POLY_DIVIDES_EXP]
QED

Theorem POLY_DIVIDES_ADD:
 !p q r. p poly_divides q /\ p poly_divides r ==> p poly_divides (q + r)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[poly_divides] THEN
  DISCH_THEN(CONJUNCTS_THEN MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN (Term`s:real list`) ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN (Term`t:real list`) ASSUME_TAC) THEN
  EXISTS_TAC (Term`t + s`) THEN
  ASM_REWRITE_TAC[FUN_EQ_THM, POLY_ADD, POLY_MUL] THEN
  REAL_ARITH_TAC
QED

Theorem POLY_DIVIDES_SUB:
 !p q r. p poly_divides q /\ p poly_divides (q + r) ==> p poly_divides r
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[poly_divides] THEN
  DISCH_THEN(CONJUNCTS_THEN MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN (Term`s:real list`) ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN (Term`t:real list`) ASSUME_TAC) THEN
  EXISTS_TAC (Term`s + poly_neg(t)`) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  REWRITE_TAC[FUN_EQ_THM, POLY_ADD, POLY_MUL, POLY_NEG] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB, REAL_MUL_RNEG] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC
QED

Theorem POLY_DIVIDES_SUB2:
 !p q r. p poly_divides r /\ p poly_divides (q + r) ==> p poly_divides q
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC POLY_DIVIDES_SUB THEN
  EXISTS_TAC (Term`r:real list`) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC (Term`p poly_divides (q + r)`) THEN
  REWRITE_TAC[poly_divides, POLY_ADD, FUN_EQ_THM, POLY_MUL] THEN
  DISCH_THEN(X_CHOOSE_TAC (Term`s:real list`)) THEN
  EXISTS_TAC (Term`s:real list`) THEN
  X_GEN_TAC (Term`x:real`) THEN POP_ASSUM(MP_TAC o SPEC (Term`x:real`)) THEN
  REAL_ARITH_TAC
QED

Theorem POLY_DIVIDES_ZERO:
 !p q. (poly p = poly []) ==> q poly_divides p
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[poly_divides] THEN
  EXISTS_TAC (Term`[]:real list`) THEN
  ASM_REWRITE_TAC[FUN_EQ_THM, POLY_MUL, poly_def, REAL_MUL_RZERO]
QED

(* ------------------------------------------------------------------------- *)
(* At last, we can consider the order of a root.                             *)
(* ------------------------------------------------------------------------- *)

Theorem POLY_ORDER_EXISTS:
 !a d. !p. (LENGTH p = d) /\ ~(poly p = poly [])
             ==> ?n. ([~a; &1] poly_exp n) poly_divides p /\
                     ~(([~a; &1] poly_exp (SUC n)) poly_divides p)
Proof
  GEN_TAC
  THEN (STRIP_ASSUME_TAC o prove_rec_fn_exists num_Axiom)
    (Term`(!p q. mulexp 0 p q = q) /\
     (!p q n. mulexp (SUC n) p q = p * (mulexp n p q))`)
  THEN SUBGOAL_THEN
    (Term`!d. !p. (LENGTH p = d) /\ ~(poly p = poly [])
           ==> ?n q. (p = mulexp (n:num) [~a; &1] q) /\
                     ~(poly q a = &0)`) MP_TAC
  THENL [ INDUCT_TAC THENL [SIMP_TAC real_ac_ss [LENGTH_NIL], ALL_TAC]
    THEN X_GEN_TAC (Term`p:real list`)
    THEN ASM_CASES_TAC (Term`poly p a = &0`)
    THENL [
      STRIP_TAC
      THEN UNDISCH_TAC (Term`poly p a = &0`)
      THEN DISCH_THEN(MP_TAC o REWRITE_RULE[POLY_LINEAR_DIVIDES])
      THEN DISCH_THEN(DISJ_CASES_THEN MP_TAC)
      THENL [
        ASM_MESON_TAC[],
        ALL_TAC
      ]
      THEN DISCH_THEN(X_CHOOSE_THEN (Term`q:real list`) SUBST_ALL_TAC)
      THEN UNDISCH_TAC
        (Term`!p. (LENGTH p = d) /\ ~(poly p = poly [])
         ==> ?n q. (p = mulexp (n:num) [~a; &1] q) /\
                   ~(poly q a = &0)`)
      THEN DISCH_THEN(MP_TAC o SPEC (Term`q:real list`))
      THEN RULE_ASSUM_TAC(REWRITE_RULE[POLY_LENGTH_MUL, POLY_ENTIRE,
        DE_MORGAN_THM, SUC_INJ])
      THEN ASM_REWRITE_TAC[]
      THEN DISCH_THEN(X_CHOOSE_THEN (Term`n:num`)
        (X_CHOOSE_THEN (Term`s:real list`) STRIP_ASSUME_TAC))
      THEN EXISTS_TAC (Term`SUC n`)
      THEN EXISTS_TAC (Term`s:real list`)
      THEN ASM_REWRITE_TAC[],
      STRIP_TAC
      THEN EXISTS_TAC (Term`0:num`)
      THEN EXISTS_TAC (Term`p:real list`)
      THEN ASM_REWRITE_TAC[]
    ],
    DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN DISCH_THEN(ANTE_RES_THEN MP_TAC)
    THEN DISCH_THEN(X_CHOOSE_THEN (Term`n:num`)
      (X_CHOOSE_THEN (Term`s:real list`) STRIP_ASSUME_TAC))
    THEN EXISTS_TAC (Term`n:num`)
    THEN ASM_REWRITE_TAC[]
    THEN REWRITE_TAC[poly_divides]
    THEN CONJ_TAC
    THENL [
      EXISTS_TAC (Term`s:real list`)
      THEN SPEC_TAC((Term`n:num`),(Term`n:num`))
      THEN INDUCT_TAC
      THEN ASM_REWRITE_TAC[poly_exp_def, FUN_EQ_THM, POLY_MUL, poly_def]
      THEN REAL_ARITH_TAC,
      DISCH_THEN(X_CHOOSE_THEN (Term`r:real list`) MP_TAC)
      THEN SPEC_TAC((Term`n:num`),(Term`n:num`))
      THEN INDUCT_TAC
      THEN ASM_SIMP_TAC bool_ss []
      THENL [
        UNDISCH_TAC (Term`~(poly s a = &0)`)
        THEN CONV_TAC CONTRAPOS_CONV
        THEN REWRITE_TAC[]
        THEN DISCH_THEN SUBST1_TAC
        THEN REWRITE_TAC[poly_def, poly_exp_def, POLY_MUL]
        THEN REAL_ARITH_TAC,
        REWRITE_TAC[]
        THEN ONCE_ASM_REWRITE_TAC[]
        THEN ONCE_REWRITE_TAC[poly_exp_def]
        THEN REWRITE_TAC[GSYM POLY_MUL_ASSOC, POLY_MUL_LCANCEL]
        THEN REWRITE_TAC[DE_MORGAN_THM]
        THEN CONJ_TAC
        THENL [
          REWRITE_TAC[FUN_EQ_THM]
          THEN DISCH_THEN(MP_TAC o SPEC (Term`a + &1`))
          THEN REWRITE_TAC[poly_def]
          THEN REAL_ARITH_TAC,
          DISCH_THEN(ANTE_RES_THEN MP_TAC)
          THEN REWRITE_TAC[]
        ]
      ]
    ]
  ]
QED

Theorem POLY_ORDER:
 !p a. ~(poly p = poly [])
         ==> ?!n. ([~a; &1] poly_exp n) poly_divides p /\
                      ~(([~a; &1] poly_exp (SUC n)) poly_divides p)
Proof
  MESON_TAC[POLY_ORDER_EXISTS, POLY_EXP_DIVIDES, LE_SUC_LT, LT_CASES]
QED

(* ------------------------------------------------------------------------- *)
(* Definition of order.                                                      *)
(* ------------------------------------------------------------------------- *)

val poly_order = new_definition ("poly_order",
  (Term`poly_order a p = @n. ([~a; &1] poly_exp n) poly_divides p /\
                   ~(([~a; &1] poly_exp (SUC n)) poly_divides p)`));

Theorem ORDER:
 !p a n. ([~a; &1] poly_exp n) poly_divides p /\
           ~(([~a; &1] poly_exp (SUC n)) poly_divides p) =
           (n = poly_order a p) /\
           ~(poly p = poly [])
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[poly_order] THEN
  EQ_TAC THEN STRIP_TAC THENL
   [SUBGOAL_THEN (Term`~(poly p = poly [])`) ASSUME_TAC THENL
     [FIRST_ASSUM(UNDISCH_TAC o assert is_neg o concl) THEN
      CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[poly_divides] THEN
      DISCH_THEN SUBST1_TAC THEN EXISTS_TAC (Term`[]:real list`) THEN
      REWRITE_TAC[FUN_EQ_THM, POLY_MUL, poly_def, REAL_MUL_RZERO],
      ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC SELECT_UNIQUE THEN REWRITE_TAC[]],
    ONCE_ASM_REWRITE_TAC[] THEN CONV_TAC SELECT_CONV] THEN
  ASM_MESON_TAC[POLY_ORDER]
QED

Theorem ORDER_THM:
 !p a. ~(poly p = poly [])
         ==> ([~a; &1] poly_exp (poly_order a p)) poly_divides p /\
             ~(([~a; &1] poly_exp (SUC(poly_order a p))) poly_divides p)
Proof
  MESON_TAC[ORDER]
QED

Theorem ORDER_UNIQUE:
 !p a n. ~(poly p = poly []) /\
           ([~a; &1] poly_exp n) poly_divides p /\
           ~(([~a; &1] poly_exp (SUC n)) poly_divides p)
           ==> (n = poly_order a p)
Proof
  MESON_TAC[ORDER]
QED

Theorem ORDER_POLY:
 !p q a. (poly p = poly q) ==> (poly_order a p = poly_order a q)
Proof
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[poly_order, poly_divides, FUN_EQ_THM, POLY_MUL]
QED

Theorem ORDER_ROOT:
 !p a. (poly p a = &0) = (poly p = poly []) \/ ~(poly_order a p = 0)
Proof
  REPEAT GEN_TAC THEN ASM_CASES_TAC (Term`poly p = poly []`) THEN
  ASM_REWRITE_TAC[poly_def] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o REWRITE_RULE[POLY_LINEAR_DIVIDES]) THEN
    ASM_CASES_TAC (Term`p:real list = []`) THENL [ASM_MESON_TAC[], ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN (Term`q:real list`) SUBST_ALL_TAC) THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC (Term`a:real`) o MATCH_MP ORDER_THM) THEN
    ASM_REWRITE_TAC[poly_exp_def, DE_MORGAN_THM] THEN DISJ2_TAC THEN
    REWRITE_TAC[poly_divides] THEN EXISTS_TAC (Term`q:real list`) THEN
    REWRITE_TAC[FUN_EQ_THM, POLY_MUL, poly_def] THEN REAL_ARITH_TAC,
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC (Term`a:real`) o MATCH_MP ORDER_THM) THEN
    UNDISCH_TAC (Term`~(poly_order a p = 0)`) THEN
    SPEC_TAC((Term`poly_order a p`),(Term`n:num`)) THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC[poly_exp_def, NOT_SUC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[poly_divides] THEN
    DISCH_THEN(X_CHOOSE_THEN (Term`s:real list`) SUBST1_TAC) THEN
    REWRITE_TAC[POLY_MUL, poly_def] THEN REAL_ARITH_TAC]
QED

Theorem ORDER_DIVIDES:
 !p a n. ([~a; &1] poly_exp n) poly_divides p =
           (poly p = poly []) \/ n <= poly_order a p
Proof
  REPEAT GEN_TAC THEN ASM_CASES_TAC (Term`poly p = poly []`) THEN
  ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[poly_divides] THEN EXISTS_TAC (Term`[]:real list`) THEN
    REWRITE_TAC[FUN_EQ_THM, POLY_MUL, poly_def, REAL_MUL_RZERO],
    ASM_MESON_TAC[ORDER_THM, POLY_EXP_DIVIDES, NOT_LE, LE_SUC_LT]]
QED

Theorem ORDER_DECOMP:
 !p a. ~(poly p = poly [])
         ==> ?q. (poly p = poly (([~a; &1] poly_exp (poly_order a p)) * q)) /\
                 ~([~a; &1] poly_divides q)
Proof
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP ORDER_THM) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC o SPEC (Term`a:real`)) THEN
  DISCH_THEN(X_CHOOSE_TAC (Term`q:real list`) o REWRITE_RULE[poly_divides]) THEN
  EXISTS_TAC (Term`q:real list`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC (Term`r: real list`) o REWRITE_RULE[poly_divides]) THEN
  UNDISCH_TAC (Term`~([~ a; &1] poly_exp SUC (poly_order a p) poly_divides p)`) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[poly_divides] THEN
  EXISTS_TAC (Term`r:real list`) THEN
  ASM_REWRITE_TAC[POLY_MUL, FUN_EQ_THM, poly_exp_def] THEN
  REAL_ARITH_TAC
QED

(* ------------------------------------------------------------------------- *)
(* Important composition properties of orders.                               *)
(* ------------------------------------------------------------------------- *)

Theorem ORDER_MUL:
 !a p q. ~(poly (p * q) = poly []) ==>
           (poly_order a (p * q) = poly_order a p + poly_order a q)
Proof
  REPEAT GEN_TAC
  THEN DISCH_THEN(fn th => ASSUME_TAC th THEN MP_TAC th)
  THEN REWRITE_TAC[POLY_ENTIRE, DE_MORGAN_THM]
  THEN STRIP_TAC
  THEN SUBGOAL_THEN (Term`(poly_order a p + poly_order a q
    = poly_order a (p * q)) /\ ~(poly (p * q) = poly [])`) MP_TAC
  THENL [
    ALL_TAC,
    MESON_TAC[]
  ]
  THEN REWRITE_TAC[GSYM ORDER]
  THEN CONJ_TAC
  THENL [
    MP_TAC(CONJUNCT1 (SPEC (Term`a:real`)
      (MATCH_MP ORDER_THM (ASSUME (Term`~(poly p = poly [])`)))))
    THEN DISCH_THEN(X_CHOOSE_TAC (Term`r: real list`) o REWRITE_RULE[poly_divides])
    THEN MP_TAC(CONJUNCT1 (SPEC (Term`a:real`)
      (MATCH_MP ORDER_THM (ASSUME (Term`~(poly q = poly [])`)))))
    THEN DISCH_THEN(X_CHOOSE_TAC (Term`s: real list`) o REWRITE_RULE[poly_divides])
    THEN REWRITE_TAC[poly_divides, FUN_EQ_THM]
    THEN EXISTS_TAC (Term`s * r`)
    THEN ASM_REWRITE_TAC[POLY_MUL, POLY_EXP_ADD]
    THEN REAL_ARITH_TAC,
    X_CHOOSE_THEN (Term`r: real list`) STRIP_ASSUME_TAC
    (SPEC (Term`a:real`) (MATCH_MP ORDER_DECOMP (ASSUME (Term`~(poly p = poly [])`))))
    THEN X_CHOOSE_THEN (Term`s: real list`) STRIP_ASSUME_TAC
    (SPEC (Term`a:real`) (MATCH_MP ORDER_DECOMP (ASSUME (Term`~(poly q = poly [])`))))
    THEN ASM_REWRITE_TAC[poly_divides, FUN_EQ_THM, POLY_EXP_ADD, POLY_MUL, poly_exp_def]
    THEN DISCH_THEN(X_CHOOSE_THEN (Term`t:real list`) STRIP_ASSUME_TAC)
    THEN SUBGOAL_THEN (Term`[~a; &1] poly_divides (r * s)`) MP_TAC
    THENL [
      ALL_TAC,
      ASM_REWRITE_TAC[POLY_PRIMES]
    ]
    THEN REWRITE_TAC[poly_divides]
    THEN EXISTS_TAC (Term`t:real list`)
    THEN SUBGOAL_THEN (Term`poly ([~ a; &1] poly_exp (poly_order a p) * (r * s)) =
      poly ([~ a; &1] poly_exp (poly_order a p) * ([~ a; &1] * t))`) MP_TAC
    THENL [
      ALL_TAC,
      MESON_TAC[POLY_MUL_LCANCEL, POLY_EXP_PRIME_EQ_0]
    ]
    THEN SUBGOAL_THEN (Term`poly ([~ a; &1] poly_exp (poly_order a q) *
                        ([~ a; &1] poly_exp (poly_order a p) * (r * s))) =
                  poly ([~ a; &1] poly_exp (poly_order a q) *
                        ([~ a; &1] poly_exp (poly_order a p) *
                         ([~ a; &1] * t)))`) MP_TAC
    THENL [
      ALL_TAC,
      MESON_TAC[POLY_MUL_LCANCEL, POLY_EXP_PRIME_EQ_0]
    ]
    THEN REWRITE_TAC[FUN_EQ_THM, POLY_MUL, POLY_ADD]
    THEN FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl)
    THEN SIMP_TAC real_ac_ss []
  ]
QED

Theorem ORDER_DIFF:
 !p a. ~(poly (diff p) = poly []) /\
         ~(poly_order a p = 0)
         ==> (poly_order a p = SUC (poly_order a (diff p)))
Proof
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN (Term`~(poly p = poly [])`) MP_TAC THENL
   [ASM_MESON_TAC[POLY_DIFF_ZERO], ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN (Term`q:real list`) MP_TAC o
    SPEC (Term`a:real`) o MATCH_MP ORDER_DECOMP) THEN
  SPEC_TAC((Term`poly_order a p`),(Term`n:num`)) THEN
  INDUCT_TAC THEN REWRITE_TAC[NOT_SUC, SUC_INJ] THEN
  STRIP_TAC THEN MATCH_MP_TAC ORDER_UNIQUE THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN (Term`!r. r poly_divides (diff p) =
                    r poly_divides (diff ([~ a; &1] poly_exp SUC n * q))`)
  (fn th => REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[poly_divides] THEN
    FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP POLY_DIFF_WELLDEF th]),
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[poly_divides, FUN_EQ_THM] THEN
    EXISTS_TAC (Term`[~a; &1] * (diff q) + &(SUC n) ## q`) THEN
    REWRITE_TAC[POLY_DIFF_MUL, POLY_DIFF_EXP_PRIME,
      POLY_ADD, POLY_MUL, POLY_CMUL] THEN
    REWRITE_TAC[poly_exp_def, POLY_MUL] THEN REAL_ARITH_TAC,
    REWRITE_TAC[FUN_EQ_THM, poly_divides, POLY_DIFF_MUL, POLY_DIFF_EXP_PRIME,
      POLY_ADD, POLY_MUL, POLY_CMUL] THEN
    DISCH_THEN(X_CHOOSE_THEN (Term`r:real list`) ASSUME_TAC) THEN
    UNDISCH_TAC (Term`~([~ a; &1] poly_divides q)`) THEN
    REWRITE_TAC[poly_divides] THEN
    EXISTS_TAC (Term`inv(&(SUC n)) ## (r + poly_neg(diff q))`) THEN
    SUBGOAL_THEN
        (Term`poly ([~a; &1] poly_exp n * q) =
         poly ([~a; &1] poly_exp n * ([~ a; &1] * (inv (&(SUC n)) ##
                                   (r + poly_neg (diff q)))))`)
    MP_TAC THENL
     [ALL_TAC, MESON_TAC[POLY_MUL_LCANCEL, POLY_EXP_PRIME_EQ_0]] THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC (Term`x:real`) THEN
    SUBGOAL_THEN
        (Term`!a b. (&(SUC n) * a = &(SUC n) * b) ==> (a = b)`)
    MATCH_MP_TAC THENL
     [REWRITE_TAC[REAL_EQ_MUL_LCANCEL, REAL_OF_NUM_EQ, NOT_SUC], ALL_TAC] THEN
    REWRITE_TAC[POLY_MUL, POLY_CMUL] THEN
    SUBGOAL_THEN (Term`!a b c. &(SUC n) * (a * (b * (inv(&(SUC n)) * c))) =
                          a * (b * c)`)
    (fn th => REWRITE_TAC[th]) THENL
      [REPEAT GEN_TAC THEN
       GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
       REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
       AP_TERM_TAC THEN
       GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
       GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
       REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
       MATCH_MP_TAC REAL_MUL_RINV THEN
       REWRITE_TAC[REAL_OF_NUM_EQ, NOT_SUC], ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC (Term`x:real`)) THEN
    REWRITE_TAC[poly_exp_def, POLY_MUL, POLY_ADD, POLY_NEG] THEN
    REAL_ARITH_TAC]
QED

(* ------------------------------------------------------------------------- *)
(* Now justify the standard squarefree decomposition, i.e. f / gcd(f,f').    *)
(* ------------------------------------------------------------------------- *)

Theorem POLY_SQUAREFREE_DECOMP_ORDER:
 !p q d e r s.
        ~(poly (diff p) = poly []) /\
        (poly p = poly (q * d)) /\
        (poly (diff p) = poly (e * d)) /\
        (poly d = poly (r * p + s * diff p))
        ==> !a. poly_order a q = (if (poly_order a p = 0) then 0 else 1)
Proof
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN (Term`poly_order a p = poly_order a q + poly_order a d`) MP_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (Term`poly_order a (q * d)`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ORDER_POLY THEN ASM_REWRITE_TAC[],
      MATCH_MP_TAC ORDER_MUL THEN
      FIRST_ASSUM(fn th =>
        GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
      ASM_MESON_TAC[POLY_DIFF_ZERO]], ALL_TAC] THEN
  ASM_CASES_TAC (Term`poly_order a p = 0`) THEN ASM_REWRITE_TAC[] THENL
   [ARITH_TAC, ALL_TAC] THEN
  SUBGOAL_THEN (Term`poly_order a (diff p) =
                poly_order a e + poly_order a d`) MP_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (Term`poly_order a (e * d)`) THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[ORDER_POLY], ASM_MESON_TAC[ORDER_MUL]], ALL_TAC] THEN
  SUBGOAL_THEN (Term`~(poly p = poly [])`) ASSUME_TAC THENL
   [ASM_MESON_TAC[POLY_DIFF_ZERO], ALL_TAC] THEN
  MP_TAC(SPECL [(Term`p:real list`), (Term`a:real`)] ORDER_DIFF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fn th => MP_TAC th THEN MP_TAC(AP_TERM (Term`PRE`) th)) THEN
  REWRITE_TAC[PRE] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  SUBGOAL_THEN (Term`poly_order a (diff p) <= poly_order a d`) MP_TAC THENL
   [SUBGOAL_THEN (Term`([~a; &1] poly_exp (poly_order a (diff p))) poly_divides d`)
    MP_TAC THENL [ALL_TAC, ASM_MESON_TAC[POLY_ENTIRE, ORDER_DIVIDES]] THEN
    SUBGOAL_THEN
      (Term`([~a; &1] poly_exp (poly_order a (diff p))) poly_divides p /\
       ([~a; &1] poly_exp (poly_order a (diff p))) poly_divides (diff p)`)
    MP_TAC THENL
     [REWRITE_TAC[ORDER_DIVIDES, LE_REFL] THEN DISJ2_TAC THEN
      REWRITE_TAC[ASSUME (Term`poly_order a (diff p) = PRE (poly_order a p)`)] THEN
      ARITH_TAC,
      DISCH_THEN(CONJUNCTS_THEN MP_TAC) THEN REWRITE_TAC[poly_divides] THEN
      REWRITE_TAC[ASSUME (Term`poly d = poly (r * p + s * diff p)`)] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN
      SIMP_TAC bool_ss [FUN_EQ_THM, POLY_MUL, POLY_ADD] THEN
      DISCH_THEN(X_CHOOSE_THEN (Term`f:real list`) ASSUME_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN (Term`g:real list`) ASSUME_TAC) THEN
      EXISTS_TAC (Term`r * g + s * f`)
      THEN GEN_TAC
      THEN SIMP_TAC real_ac_ss [POLY_MUL, POLY_ADD, REAL_LDISTRIB]
      THEN ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC],
    ARITH_TAC]
QED

(* ------------------------------------------------------------------------- *)
(* Define being "squarefree" --- NB with respect to real roots only.         *)
(* ------------------------------------------------------------------------- *)

val rsquarefree = new_definition ("rsquarefree",
  (Term`rsquarefree p = ~(poly p = poly []) /\
                   !a. (poly_order a p = 0) \/ (poly_order a p = 1)`));

(* ------------------------------------------------------------------------- *)
(* Standard squarefree criterion and rephasing of squarefree decomposition.  *)
(* ------------------------------------------------------------------------- *)

Theorem RSQUAREFREE_ROOTS:
 !p. rsquarefree p = !a. ~((poly p a = &0) /\ (poly (diff p) a = &0))
Proof
  GEN_TAC THEN REWRITE_TAC[rsquarefree] THEN
  ASM_CASES_TAC (Term`poly p = poly []`) THEN ASM_REWRITE_TAC[] THENL
   [FIRST_ASSUM(SUBST1_TAC o MATCH_MP POLY_DIFF_ZERO) THEN
    ASM_REWRITE_TAC[poly_def, NOT_FORALL_THM],
    ASM_CASES_TAC (Term`poly(diff p) = poly []`) THEN ASM_REWRITE_TAC[] THENL
     [FIRST_ASSUM(X_CHOOSE_THEN (Term`h:real`) MP_TAC o
        MATCH_MP POLY_DIFF_ISZERO) THEN
      DISCH_THEN(fn th => ASSUME_TAC th THEN MP_TAC th) THEN
      DISCH_THEN(fn th => REWRITE_TAC[MATCH_MP ORDER_POLY th]) THEN
      UNDISCH_TAC (Term`~(poly p = poly [])`) THEN ASM_REWRITE_TAC[poly_def] THEN
      REWRITE_TAC[FUN_EQ_THM, poly_def, REAL_MUL_RZERO, REAL_ADD_RID] THEN
      DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC (Term`a:real`) THEN DISJ1_TAC THEN
      MP_TAC(SPECL [(Term`[h:real]`), (Term`a:real`)] ORDER_ROOT) THEN
      ASM_REWRITE_TAC[FUN_EQ_THM, poly_def, REAL_MUL_RZERO, REAL_ADD_RID],
      ASM_REWRITE_TAC[ORDER_ROOT, DE_MORGAN_THM, ONE] THEN
      ASM_MESON_TAC[ORDER_DIFF, SUC_INJ]]]
QED

Theorem RSQUAREFREE_DECOMP:
 !p a. rsquarefree p /\ (poly p a = &0)
         ==> ?q. (poly p = poly ([~a; &1] * q)) /\
                 ~(poly q a = &0)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[rsquarefree] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ORDER_DECOMP) THEN
  DISCH_THEN(X_CHOOSE_THEN (Term`q:real list`) MP_TAC o SPEC (Term`a:real`)) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ORDER_ROOT]) THEN
  FIRST_ASSUM(DISJ_CASES_TAC o SPEC (Term`a:real`)) THEN
  ASM_SIMP_TAC real_ac_ss [] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  EXISTS_TAC (Term`q:real list`) THEN CONJ_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM, POLY_MUL] THEN GEN_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [ONE] THEN
    REWRITE_TAC[poly_exp_def, POLY_MUL] THEN
    REWRITE_TAC[poly_def] THEN REAL_ARITH_TAC,
    DISCH_TAC THEN UNDISCH_TAC (Term`~([~a; &1] poly_divides q)`) THEN
    REWRITE_TAC[poly_divides] THEN
    UNDISCH_TAC (Term`poly q a = &0`) THEN
    GEN_REWRITE_TAC LAND_CONV [POLY_LINEAR_DIVIDES] THEN
    ASM_CASES_TAC (Term`q:real list = []`) THEN ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC (Term`[] : real list`) THEN REWRITE_TAC[FUN_EQ_THM] THEN
      REWRITE_TAC[POLY_MUL, poly_def, REAL_MUL_RZERO],
      MESON_TAC[]]]
QED

Theorem POLY_SQUAREFREE_DECOMP:
 !p q d e r s.
        ~(poly (diff p) = poly []) /\
        (poly p = poly (q * d)) /\
        (poly (diff p) = poly (e * d)) /\
        (poly d = poly (r * p + s * diff p))
        ==> rsquarefree q /\ (!a. (poly q a = &0) = (poly p a = &0))
Proof
  REPEAT GEN_TAC THEN DISCH_THEN(fn th => MP_TAC th THEN
    ASSUME_TAC(MATCH_MP POLY_SQUAREFREE_DECOMP_ORDER th)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN (Term`~(poly p = poly [])`) ASSUME_TAC THENL
   [ASM_MESON_TAC[POLY_DIFF_ZERO], ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  UNDISCH_TAC (Term`~(poly p = poly [])`) THEN
  DISCH_THEN(fn th => MP_TAC th THEN MP_TAC th) THEN
  DISCH_THEN(fn th => ASM_REWRITE_TAC[] THEN ASSUME_TAC th) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[POLY_ENTIRE, DE_MORGAN_THM] THEN STRIP_TAC THEN
  UNDISCH_TAC (Term`poly p = poly (q * d)`) THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  ASM_REWRITE_TAC[rsquarefree, ORDER_ROOT] THEN
  CONJ_TAC THEN GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC real_ac_ss []
QED

(* ------------------------------------------------------------------------- *)
(* Normalization of a polynomial.                                            *)
(* ------------------------------------------------------------------------- *)

Definition normalize[nocompute]:
  (normalize [] = []) /\
  (normalize (CONS h t) = (if (normalize t = []) then
                             if (h = &0) then [] else [h]
                           else CONS h (normalize t)))
End

Theorem POLY_NORMALIZE:
 !p. poly (normalize p) = poly p
Proof
  LIST_INDUCT_TAC THEN REWRITE_TAC[normalize, poly_def] THEN
  ASM_CASES_TAC (Term`h = &0`) THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[poly_def, FUN_EQ_THM] THEN
  UNDISCH_TAC (Term`poly (normalize t) = poly t`) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[poly_def] THEN
  REWRITE_TAC[REAL_MUL_RZERO, REAL_ADD_LID]
QED

(* ------------------------------------------------------------------------- *)
(* The degree of a polynomial.                                               *)
(* ------------------------------------------------------------------------- *)

val degree = new_definition ("degree",
  (Term`degree p = PRE(LENGTH(normalize p))`));

Theorem DEGREE_ZERO:
 !p. (poly p = poly []) ==> (degree p = 0)
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[degree] THEN
  SUBGOAL_THEN (Term`normalize p = []`) SUBST1_TAC THENL
   [POP_ASSUM MP_TAC THEN SPEC_TAC((Term`p:real list`),(Term`p:real list`)) THEN
    REWRITE_TAC[POLY_ZERO] THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[normalize, FORALL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN (Term`normalize t = []`) (fn th => REWRITE_TAC[th]) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[],
    REWRITE_TAC[LENGTH, PRE]]
QED

(* ------------------------------------------------------------------------- *)
(* Tidier versions of finiteness of roots.                                   *)
(* ------------------------------------------------------------------------- *)

Theorem POLY_ROOTS_FINITE_SET:
 !p. ~(poly p = poly []) ==> FINITE {x | poly p x = &0}
Proof
  GEN_TAC THEN REWRITE_TAC[POLY_ROOTS_FINITE] THEN
  DISCH_THEN(X_CHOOSE_THEN (Term`N:num`) MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN (Term`i:num->real`) ASSUME_TAC) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC (Term`{x:real | ?n:num. n < N /\ (x = i n)}`) THEN
  CONJ_TAC THENL
   [SPEC_TAC((Term`N:num`),(Term`N:num`)) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    INDUCT_TAC THENL
     [SUBGOAL_THEN (Term`{x:real | ?n:num. n < 0 /\ (x = i n)} = {}`)
      (fn th => REWRITE_TAC[th, FINITE_RULES]) THEN
      SIMP_TAC bool_ss [GSPEC_DEF, EMPTY_DEF, pairTheory.CLOSED_PAIR_EQ,
        NOT_LESS, EQT_ELIM (ARITH_CONV (Term`!n:num. ~(n < 0)`))],
      SUBGOAL_THEN (Term`{x:real | ?n. n < SUC N /\ (x = i n)} =
                    (i N) INSERT {x:real | ?n:num. n < N /\ (x = i n)}`)
      SUBST1_TAC THENL
       [SIMP_TAC bool_ss [LT, EXTENSION, IN_INSERT, SPECIFICATION,
                          GSPEC_DEF,pairTheory.CLOSED_PAIR_EQ]
        THEN MESON_TAC[],
        MATCH_MP_TAC(CONJUNCT2 FINITE_RULES) THEN ASM_REWRITE_TAC[]]],
    ASM_SIMP_TAC bool_ss [SUBSET_DEF, SPECIFICATION, GSPEC_DEF,
                          pairTheory.CLOSED_PAIR_EQ]
    THEN ASM_MESON_TAC[]]
QED

(* ------------------------------------------------------------------------- *)
(* Crude bound for polynomial.                                               *)
(* ------------------------------------------------------------------------- *)

Theorem POLY_MONO:
 !x k p. abs(x) <= k ==> abs(poly p x) <= poly (MAP abs p) k
Proof
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[poly_def, REAL_LE_REFL, MAP, REAL_ABS_0] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC (Term`abs(h) + abs(x * poly t x)`) THEN
  REWRITE_TAC[REAL_ABS_TRIANGLE, REAL_LE_LADD] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]
QED

(* ------------------------------------------------------------------------- *)
(* Conversions to perform operations if coefficients are rational constants. *)
(* ------------------------------------------------------------------------- *)

(*
val POLY_DIFF_CONV =
  let
    val aux_conv0 = GEN_REWRITE_CONV I [CONJUNCT1 poly_diff_aux]
    val aux_conv1 = GEN_REWRITE_CONV I [CONJUNCT2 poly_diff_aux]
    val diff_conv0 = GEN_REWRITE_CONV I (butlast (CONJUNCTS POLY_DIFF_CLAUSES))
    val diff_conv1 = GEN_REWRITE_CONV I [last (CONJUNCTS POLY_DIFF_CLAUSES)]
    fun POLY_DIFF_AUX_CONV tm =
      (aux_conv0 ORELSEC
      (aux_conv1 THENC
      LAND_CONV REAL_RAT_MUL_CONV THENC
      RAND_CONV (LAND_CONV NUM_SUC_CONV THENC POLY_DIFF_AUX_CONV))) tm
  in
    diff_conv0 ORELSEC (diff_conv1 THENC POLY_DIFF_AUX_CONV)
  end;

val POLY_CMUL_CONV =
  let cmul_conv0 = GEN_REWRITE_CONV I [CONJUNCT1 poly_cmul]
  and cmul_conv1 = GEN_REWRITE_CONV I [CONJUNCT2 poly_cmul] in
  let rec POLY_CMUL_CONV tm =
   (cmul_conv0 ORELSEC
    (cmul_conv1 THENC
     LAND_CONV REAL_RAT_MUL_CONV THENC
     RAND_CONV POLY_CMUL_CONV)) tm in
  POLY_CMUL_CONV;

val POLY_ADD_CONV =
  let add_conv0 = GEN_REWRITE_CONV I (butlast (CONJUNCTS POLY_ADD_CLAUSES))
  and add_conv1 = GEN_REWRITE_CONV I [last (CONJUNCTS POLY_ADD_CLAUSES)] in
  let rec POLY_ADD_CONV tm =
   (add_conv0 ORELSEC
    (add_conv1 THENC
     LAND_CONV REAL_RAT_ADD_CONV THENC
     RAND_CONV POLY_ADD_CONV)) tm in
  POLY_ADD_CONV;

val POLY_MUL_CONV =
  let mul_conv0 = GEN_REWRITE_CONV I [CONJUNCT1 POLY_MUL_CLAUSES]
  and mul_conv1 = GEN_REWRITE_CONV I [CONJUNCT1(CONJUNCT2 POLY_MUL_CLAUSES)]
  and mul_conv2 = GEN_REWRITE_CONV I [CONJUNCT2(CONJUNCT2 POLY_MUL_CLAUSES)] in
  let rec POLY_MUL_CONV tm =
   (mul_conv0 ORELSEC
    (mul_conv1 THENC POLY_CMUL_CONV) ORELSEC
    (mul_conv2 THENC
     LAND_CONV POLY_CMUL_CONV THENC
     RAND_CONV(RAND_CONV POLY_MUL_CONV) THENC
     POLY_ADD_CONV)) tm in
  POLY_MUL_CONV;

val POLY_NORMALIZE_CONV =
  let pth = prove
   ((Term`normalize (CONS h t) =
      (\n. (n = []) => (h = &0) => [] | [h] | CONS h n) (normalize t)`),
    REWRITE_TAC[normalize]) in
  let norm_conv0 = GEN_REWRITE_CONV I [CONJUNCT1 normalize]
  and norm_conv1 = GEN_REWRITE_CONV I [pth]
  and norm_conv2 = GEN_REWRITE_CONV DEPTH_CONV
   [COND_CLAUSES, NOT_CONS_NIL, EQT_INTRO(SPEC_ALL EQ_REFL)] in
  let rec POLY_NORMALIZE_CONV tm =
   (norm_conv0 ORELSEC
    (norm_conv1 THENC
     RAND_CONV POLY_NORMALIZE_CONV THENC
     BETA_CONV THENC
     RATOR_CONV(RAND_CONV(RATOR_CONV(LAND_CONV REAL_RAT_EQ_CONV))) THENC
     norm_conv2)) tm in
  POLY_NORMALIZE_CONV;
*)
