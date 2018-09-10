(* ========================================================================= *)
(*                                                                           *)
(*               HOL-light's Cardinal Theory (Library/card.ml)               *)
(*                                                                           *)
(*        (c) Copyright 2015                                                 *)
(*                       Muhammad Qasim,                                     *)
(*                       Osman Hasan,                                        *)
(*                       Hardware Verification Group,                        *)
(*                       Concordia University                                *)
(*                                                                           *)
(*            Contact:  <m_qasi@ece.concordia.ca>                            *)
(*                                                                           *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib numLib unwindLib tautLib Arith prim_recTheory 
 quotientTheory arithmeticTheory hrealTheory realaxTheory realTheory 
realLib jrhUtils pairTheory seqTheory limTheory transcTheory listTheory mesonLib 
boolTheory pred_setTheory set_relationTheory util_probTheory 
optionTheory numTheory sumTheory InductiveDefinition ind_typeTheory;

(* now based on definitions from HOL4's cardinalTheory *)
open iterateTheory wellorderTheory cardinalTheory;

val _ = new_theory "rich_cardinal";

(* ------------------------------------------------------------------------- *)
(* MESON, METIS, SET_TAC, SET_RULE, ASSERT_TAC, ASM_ARITH_TAC                *)
(* ------------------------------------------------------------------------- *)

fun K_TAC _ = ALL_TAC;
fun MESON ths tm = prove(tm,MESON_TAC ths);
fun METIS ths tm = prove(tm,METIS_TAC ths);

val DISC_RW_KILL = DISCH_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN 
                   POP_ASSUM K_TAC;

fun SET_TAC L = 
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT COND_CASES_TAC THEN
    REWRITE_TAC (append [EXTENSION, SUBSET_DEF, PSUBSET_DEF, DISJOINT_DEF,
    SING_DEF] L) THEN
    SIMP_TAC std_ss [NOT_IN_EMPTY, IN_UNIV, IN_UNION, IN_INTER, IN_DIFF, 
      IN_INSERT, IN_DELETE, IN_REST, IN_BIGINTER, IN_BIGUNION, IN_IMAGE, 
      GSPECIFICATION, IN_DEF, EXISTS_PROD] THEN METIS_TAC [];

fun ASSERT_TAC tm = SUBGOAL_THEN tm STRIP_ASSUME_TAC;
fun SET_RULE tm = prove(tm,SET_TAC []);
fun ASM_SET_TAC L = REPEAT (POP_ASSUM MP_TAC) THEN SET_TAC L;

val ASM_ARITH_TAC = REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC;
val ASM_REAL_ARITH_TAC = REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;






(* ------------------------------------------------------------------------- *)
(* Finiteness and infiniteness in terms of cardinality of N.                 *)
(* ------------------------------------------------------------------------- *)

val INFINITE_CARD_LE = store_thm ("INFINITE_CARD_LE",
 ``!s:'a->bool. INFINITE s <=> (UNIV:num->bool) <=_c s``,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC,
    ONCE_REWRITE_TAC[MONO_NOT_EQ] THEN
    REWRITE_TAC[le_c, IN_UNIV] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP INFINITE_IMAGE_INJ) THEN
    DISCH_THEN(MP_TAC o C MATCH_MP num_INFINITE) THEN SIMP_TAC std_ss [] THEN
    MATCH_MP_TAC SUBSET_FINITE_I THEN EXISTS_TAC ``s:'a->bool`` THEN
    ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV, LEFT_IMP_EXISTS_THM]] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN ``?f:num->'a. !n. f(n) = @x. x IN (s DIFF IMAGE f {m | m < n})``
  MP_TAC THENL
   [ONCE_REWRITE_TAC [MESON [] ``(@x. x IN s DIFF IMAGE f {m | m < n}) =
                       (\f n:num. @x. x IN s DIFF IMAGE f {m | m < n}) f n``] THEN
    MATCH_MP_TAC(MATCH_MP WF_REC WF_num) THEN
    SIMP_TAC std_ss [IN_IMAGE, GSPECIFICATION, IN_DIFF] THEN REPEAT STRIP_TAC THEN
    AP_TERM_TAC THEN ABS_TAC THEN ASM_MESON_TAC[],
    ALL_TAC] THEN
  REWRITE_TAC[le_c] THEN DISCH_THEN (X_CHOOSE_TAC ``f:num->'a``) THEN
  EXISTS_TAC ``f:num->'a`` THEN
  SUBGOAL_THEN ``!n. (f:num->'a)(n) IN (s DIFF IMAGE f {m | m < n})`` MP_TAC THENL
   [GEN_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN CONV_TAC SELECT_CONV THEN
    REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
    MATCH_MP_TAC INFINITE_NONEMPTY THEN MATCH_MP_TAC INFINITE_DIFF_FINITE THEN
    ASM_SIMP_TAC std_ss [IMAGE_FINITE, FINITE_NUMSEG_LT],
    ALL_TAC] THEN
  SIMP_TAC std_ss [IN_IMAGE, GSPECIFICATION, IN_DIFF] THEN MESON_TAC[LT_CASES]);

val FINITE_CARD_LT = store_thm ("FINITE_CARD_LT",
 ``!s:'a->bool. FINITE s <=> s <_c (UNIV:num->bool)``,
  ONCE_REWRITE_TAC[TAUT `(a <=> b) <=> (~a <=> ~b)`] THEN
  REWRITE_TAC [Once (GSYM CARD_NOT_LT), INFINITE_CARD_LE]);

val CARD_LE_SUBSET = store_thm ("CARD_LE_SUBSET",
 ``!s:'a->bool t. s SUBSET t ==> s <=_c t``,
  REWRITE_TAC[SUBSET_DEF, le_c] THEN MESON_TAC[combinTheory.I_THM]);

val CARD_LE_UNIV = store_thm ("CARD_LE_UNIV",
 ``!s:'a->bool. s <=_c univ(:'a)``,
  GEN_TAC THEN MATCH_MP_TAC CARD_LE_SUBSET THEN REWRITE_TAC[SUBSET_UNIV]);

val CARD_LE_EQ_SUBSET = store_thm ("CARD_LE_EQ_SUBSET",
 ``!s:'a->bool t:'b->bool. s <=_c t <=> ?u. u SUBSET t /\ (s =_c u)``,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CARD_LE_SUBSET) THEN
    MATCH_MP_TAC(TAUT `(a <=> b) ==> b ==> a`) THEN
    MATCH_MP_TAC CARD_LE_CONG THEN
    ASM_REWRITE_TAC[CARD_LE_CONG, CARD_EQ_REFL]] THEN
  REWRITE_TAC[le_c, eq_c] THEN
  DISCH_THEN(X_CHOOSE_THEN ``f:'a->'b`` STRIP_ASSUME_TAC) THEN
  SIMP_TAC std_ss [GSYM RIGHT_EXISTS_AND_THM] THEN EXISTS_TAC ``IMAGE (f:'a->'b) s`` THEN
  EXISTS_TAC ``f:'a->'b`` THEN REWRITE_TAC[IN_IMAGE, SUBSET_DEF] THEN
  ASM_MESON_TAC[]);

val CARD_INFINITE_CONG = store_thm ("CARD_INFINITE_CONG",
 ``!s:'a->bool t:'b->bool. s =_c t ==> (INFINITE s <=> INFINITE t)``,
  REWRITE_TAC[INFINITE_CARD_LE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CARD_LE_CONG THEN ASM_SIMP_TAC std_ss [CARD_EQ_REFL]);

val CARD_FINITE_CONG = store_thm ("CARD_FINITE_CONG",
 ``!s:'a->bool t:'b->bool. s =_c t ==> (FINITE s <=> FINITE t)``,
  ONCE_REWRITE_TAC[TAUT `(a <=> b) <=> (~a <=> ~b)`] THEN
  SIMP_TAC std_ss [CARD_INFINITE_CONG]);

val CARD_LE_FINITE = store_thm ("CARD_LE_FINITE",
 ``!s:'a->bool t:'b->bool. FINITE t /\ s <=_c t ==> FINITE s``,
  ASM_MESON_TAC[CARD_LE_EQ_SUBSET, SUBSET_FINITE_I, CARD_FINITE_CONG]);

val CARD_EQ_FINITE = store_thm ("CARD_EQ_FINITE",
 ``!s t:'a->bool. FINITE t /\ s =_c t ==> FINITE s``,
  REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN MESON_TAC[CARD_LE_FINITE]);

val CARD_LE_INFINITE = store_thm ("CARD_LE_INFINITE",
 ``!s:'a->bool t:'b->bool. INFINITE s /\ s <=_c t ==> INFINITE t``,
  MESON_TAC[CARD_LE_FINITE]);

val CARD_LT_FINITE_INFINITE = store_thm ("CARD_LT_FINITE_INFINITE",
 ``!s:'a->bool t:'b->bool. FINITE s /\ INFINITE t ==> s <_c t``,
  ONCE_REWRITE_TAC[GSYM CARD_NOT_LE] THEN MESON_TAC[CARD_LE_FINITE]);

val CARD_LE_CARD_IMP = store_thm ("CARD_LE_CARD_IMP",
 ``!s:'a->bool t:'b->bool. FINITE t /\ s <=_c t ==> CARD s <= CARD t``,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN ``FINITE(s:'a->bool)`` ASSUME_TAC THENL
   [ASM_MESON_TAC[CARD_LE_FINITE], ALL_TAC] THEN
  UNDISCH_TAC ``s <=_c t`` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE [le_c]) THEN
  DISCH_THEN(X_CHOOSE_THEN ``f:'a->'b`` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC LESS_EQ_TRANS THEN EXISTS_TAC ``CARD(IMAGE (f:'a->'b) s)`` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(ARITH_PROVE ``(m = n:num) ==> n <= m``) THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[],
    KNOW_TAC ``(IMAGE (f :'a -> 'b) (s :'a -> bool)) SUBSET (t :'b -> bool)`` THENL
    [ASM_MESON_TAC[SUBSET_DEF, IN_IMAGE], ALL_TAC] THEN
    MATCH_MP_TAC (CARD_SUBSET) THEN ASM_REWRITE_TAC[]]);

val CARD_EQ_CARD_IMP = store_thm ("CARD_EQ_CARD_IMP",
 ``!s:'a->bool t:'b->bool. FINITE t /\ s =_c t ==> (CARD s = CARD t)``,
  METIS_TAC[CARD_FINITE_CONG, ARITH_PROVE ``m <= n /\ n <= m <=> (m = n:num)``, 
            CARD_LE_ANTISYM, CARD_LE_CARD_IMP]);

val CARD_LE_CARD = store_thm ("CARD_LE_CARD",
 ``!s:'a->bool t:'b->bool.
        FINITE s /\ FINITE t ==> (s <=_c t <=> CARD s <= CARD t)``,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(a ==> b) /\ (~a ==> ~b) ==> (a <=> b)`) THEN
  ASM_SIMP_TAC std_ss [CARD_LE_CARD_IMP] THEN
  REWRITE_TAC[NOT_LESS_EQUAL] THEN REWRITE_TAC[Once lt_c, LT_LE] THEN
  ASM_SIMP_TAC std_ss [CARD_LE_CARD_IMP] THEN
  MATCH_MP_TAC(TAUT `(c ==> a ==> b) ==> a /\ ~b ==> ~c`) THEN
  DISCH_TAC THEN GEN_REWR_TAC LAND_CONV [CARD_LE_EQ_SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN ``u:'a->bool`` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC CARD_EQ_IMP_LE THEN
  SUBGOAL_THEN ``u:'a->bool = s`` (fn th => ASM_MESON_TAC[th, CARD_EQ_SYM]) THEN
  METIS_TAC[CARD_SUBSET_EQ, CARD_EQ_CARD_IMP, CARD_EQ_SYM]);

val CARD_EQ_CARD = store_thm ("CARD_EQ_CARD",
 ``!s:'a->bool t:'b->bool.
        FINITE s /\ FINITE t ==> (s =_c t <=> (CARD s = CARD t))``,
  MESON_TAC[CARD_FINITE_CONG, ARITH_PROVE ``m <= n /\ n <= m <=> (m = n:num)``,
            CARD_LE_ANTISYM, CARD_LE_CARD]);

val CARD_LT_CARD = store_thm ("CARD_LT_CARD",
 ``!s:'a->bool t:'b->bool.
        FINITE s /\ FINITE t ==> (s <_c t <=> CARD s < CARD t)``,
  SIMP_TAC std_ss [CARD_LE_CARD, GSYM NOT_LESS_EQUAL]);

val CARD_HAS_SIZE_CONG = store_thm ("CARD_HAS_SIZE_CONG",
 ``!s:'a->bool t:'b->bool n. s HAS_SIZE n /\ s =_c t ==> t HAS_SIZE n``,
  REWRITE_TAC[HAS_SIZE] THEN
  MESON_TAC[CARD_EQ_CARD, CARD_FINITE_CONG]);

val CARD_LE_IMAGE = store_thm ("CARD_LE_IMAGE",
 ``!f s. IMAGE f s <=_c s``,
  SIMP_TAC std_ss [LE_C, FORALL_IN_IMAGE] THEN MESON_TAC[]);

val CARD_LE_IMAGE_GEN = store_thm ("CARD_LE_IMAGE_GEN",
 ``!f:'a->'b s t. t SUBSET IMAGE f s ==> t <=_c s``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_LE_TRANS THEN
  EXISTS_TAC ``IMAGE (f:'a->'b) s`` THEN
  ASM_SIMP_TAC std_ss [CARD_LE_IMAGE, CARD_LE_SUBSET]);

val CARD_EQ_IMAGE = store_thm ("CARD_EQ_IMAGE",
 ``!f:'a->'b s.
        (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
        ==> (IMAGE f s =_c s)``,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN
  REWRITE_TAC[eq_c] THEN EXISTS_TAC ``f:'a->'b`` THEN ASM_SET_TAC[]);

(* ------------------------------------------------------------------------- *)
(* Cardinal arithmetic operations.                                           *)
(* ------------------------------------------------------------------------- *)

val _ = set_fixity "+_c" (Infix(NONASSOC, 450));
val _ = set_fixity "*_c" (Infix(NONASSOC, 450));

val add_c = new_definition ("add_c",
  ``s +_c t = {INL x | x IN s} UNION {INR y | y IN t}``);

val _ = overload_on ("+", ``$+_c``);

val _ = overload_on ("*_c", ``$CROSS``); (* defined in pred_setTheory *)
val _ = Unicode.unicode_version {tmnm = "*_c", u = UTF8.chr 0xD7};
val _ = TeX_notation {hol = "*_c", TeX = ("\\ensuremath{\\times}", 1)};

val mul_c = store_thm ("mul_c",
  ``!s t. s *_c t = {(x,y) | x IN s /\ y IN t}``,
    NTAC 2 GEN_TAC
 >> REWRITE_TAC [CROSS_DEF, EXTENSION, GSPECIFICATION]
 >> GEN_TAC >> BETA_TAC
 >> REWRITE_TAC [PAIR_EQ]
 >> EQ_TAC >> STRIP_TAC
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC `(FST x, SND x)` >> RW_TAC std_ss [],
      (* goal 2 (of 2) *)
      Cases_on `x'` >> fs [] ]);

(* ------------------------------------------------------------------------- *)
(* Congruence properties for the arithmetic operators.                       *)
(* ------------------------------------------------------------------------- *)

val CARD_LE_ADD = store_thm ("CARD_LE_ADD",
 ``!s:'a->bool s':'b->bool t:'c->bool t':'d->bool.
      s <=_c s' /\ t <=_c t' ==> (s +_c t) <=_c (s' +_c t')``,
  REPEAT GEN_TAC THEN REWRITE_TAC[le_c, add_c] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN ``f:'a->'b`` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN ``g:'c->'d`` STRIP_ASSUME_TAC)) THEN
  KNOW_TAC ``(?h. (!x. h (INL x) = INL ((f:'a->'b) x)) /\ 
                  (!y. h (INR y) = INR ((g:'c->'d) y)))`` THENL
  [RW_TAC std_ss [sum_Axiom], ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_TAC ``h:('a+'c)->('b+'d)``) THEN 
  EXISTS_TAC ``h:('a+'c)->('b+'d)`` THEN
  POP_ASSUM MP_TAC THEN STRIP_TAC THEN
  SIMP_TAC std_ss [IN_UNION, GSPECIFICATION] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
         ASM_REWRITE_TAC[]) THEN
  ASM_SIMP_TAC std_ss [sum_distinct, INR_11, INL_11, INR_INL_11] THEN
  ASM_MESON_TAC[]);

val CARD_LE_MUL = store_thm ("CARD_LE_MUL",
 ``!s:'a->bool s':'b->bool t:'c->bool t':'d->bool.
      s <=_c s' /\ t <=_c t' ==> (s *_c t) <=_c (s' *_c t')``,
  REPEAT GEN_TAC THEN REWRITE_TAC[le_c, mul_c] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN ``f:'a->'b`` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN ``g:'c->'d`` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC ``\(x,y). (f:'a->'b) x,(g:'c->'d) y`` THEN
  SIMP_TAC std_ss [FORALL_PROD, GSPECIFICATION, EXISTS_PROD] THEN
  BETA_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]);

val CARD_ADD_CONG = store_thm ("CARD_ADD_CONG",
 ``!s:'a->bool s':'b->bool t:'c->bool t':'d->bool.
      s =_c s' /\ t =_c t' ==> (s +_c t) =_c (s' +_c t')``,
  SIMP_TAC std_ss [CARD_LE_ADD, GSYM CARD_LE_ANTISYM]);

val CARD_MUL_CONG = store_thm ("CARD_MUL_CONG",
 ``!s:'a->bool s':'b->bool t:'c->bool t':'d->bool.
      s =_c s' /\ t =_c t' ==> (s *_c t) =_c (s' *_c t')``,
  SIMP_TAC std_ss [CARD_LE_MUL, GSYM CARD_LE_ANTISYM]);

(* ------------------------------------------------------------------------- *)
(* Misc lemmas.                                                              *)
(* ------------------------------------------------------------------------- *)

val IN_CARD_ADD = store_thm ("IN_CARD_ADD",
 ``(!x. INL(x) IN (s +_c t) <=> x IN s) /\
   (!y. INR(y) IN (s +_c t) <=> y IN t)``,
  SIMP_TAC std_ss [add_c, IN_UNION, GSPECIFICATION]);

val IN_CARD_MUL = store_thm ("IN_CARD_MUL",
 ``!s t x y. (x,y) IN (s *_c t) <=> x IN s /\ y IN t``,
  SIMP_TAC std_ss [mul_c, GSPECIFICATION, PAIR_EQ, EXISTS_PROD]);

val CARD_LE_SQUARE = store_thm ("CARD_LE_SQUARE",
 ``!s:'a->bool. s <=_c (s *_c s)``,
  GEN_TAC THEN REWRITE_TAC[le_c] THEN EXISTS_TAC ``\x:'a. x,(@z:'a. z IN s)`` THEN
  SIMP_TAC std_ss [IN_CARD_MUL, PAIR_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV SELECT_CONV) THEN MESON_TAC[]);;

val CARD_SQUARE_NUM = store_thm ("CARD_SQUARE_NUM",
 ``((UNIV:num->bool) *_c (UNIV:num->bool)) =_c (UNIV:num->bool)``,
  REWRITE_TAC[GSYM CARD_LE_ANTISYM, CARD_LE_SQUARE] THEN
  SIMP_TAC std_ss [le_c, IN_UNIV, mul_c, GSPECIFICATION, EXISTS_PROD] THEN
  EXISTS_TAC ``(\(x,y). ind_type$NUMPAIR x y)`` THEN
  SIMP_TAC std_ss [FORALL_PROD] THEN BETA_TAC THEN
  MESON_TAC[NUMPAIR_INJ]);

val UNION_LE_ADD_C = store_thm ("UNION_LE_ADD_C",
 ``!s t:'a->bool. (s UNION t) <=_c (s +_c t)``,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CARD_LE_IMAGE_GEN THEN
  REWRITE_TAC[add_c, IMAGE_UNION] THEN ONCE_REWRITE_TAC[GSYM IMAGE_DEF] THEN
  REWRITE_TAC[GSYM IMAGE_COMPOSE, combinTheory.o_DEF] THEN
  EXISTS_TAC ``(\(y:'a+'a). if (?x:'a. y = INR x) then (OUTR:'a+'a->'a) y 
                                                  else (OUTL:'a+'a->'a) y)`` THEN
  REWRITE_TAC [SUBSET_DEF, IN_IMAGE, IN_UNION] THEN GEN_TAC THEN STRIP_TAC THENL 
  [DISJ1_TAC THEN EXISTS_TAC ``x:'a`` THEN ASM_REWRITE_TAC [] THEN BETA_TAC THEN
   COND_CASES_TAC THENL [ALL_TAC, METIS_TAC [OUTL]] THEN CCONTR_TAC THEN
   UNDISCH_TAC ``?x'. (INL x):'a+'a = INR x'`` THEN REWRITE_TAC [] THEN
   SIMP_TAC std_ss [NOT_EXISTS_THM],
   DISJ2_TAC THEN EXISTS_TAC ``x:'a`` THEN ASM_REWRITE_TAC [] THEN BETA_TAC THEN
   COND_CASES_TAC THENL [METIS_TAC [OUTR], METIS_TAC []]]);

val CARD_DISJOINT_UNION = store_thm
  ("CARD_DISJOINT_UNION",
  ``!s t.
         FINITE s /\ FINITE t /\ (s INTER t = {})
         ==> (CARD (s UNION t) = CARD s + CARD t)``,
  REPEAT STRIP_TAC THEN GEN_REWR_TAC LAND_CONV [ARITH_PROVE ``x = x + 0:num``] THEN
  ONCE_REWRITE_TAC [GSYM CARD_EMPTY] THEN METIS_TAC [CARD_UNION]);

val CARD_ADD_C = store_thm ("CARD_ADD_C",
 ``!s t. FINITE s /\ FINITE t ==> (CARD(s +_c t) = CARD s + CARD t)``,
  REPEAT STRIP_TAC THEN REWRITE_TAC[add_c] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) CARD_DISJOINT_UNION o lhand o snd) THEN
  ASM_SIMP_TAC real_ss [GSYM IMAGE_DEF, IMAGE_FINITE] THEN
  REWRITE_TAC[SET_RULE ``(IMAGE f s INTER IMAGE g t = {}) <=>
                        !x y. x IN s /\ y IN t ==> ~(f x = g y)``] THEN
  REWRITE_TAC[sum_distinct] THEN DISCH_THEN SUBST1_TAC THEN
  BINOP_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
  ASM_SIMP_TAC std_ss [INR_11, INL_11]);

(* ------------------------------------------------------------------------- *)
(* Various "arithmetical" lemmas.                                            *)
(* ------------------------------------------------------------------------- *)

val CARD_ADD_SYM = store_thm ("CARD_ADD_SYM",
 ``!s:'a->bool t:'b->bool. (s +_c t) =_c (t +_c s)``,
  REPEAT GEN_TAC THEN REWRITE_TAC[eq_c] THEN
  KNOW_TAC ``(?h. (!x. (h:'a+'b->'b+'a) (INL x) = INR x) /\ (!y. h (INR y) = INL y))`` THENL
  [RW_TAC std_ss [sum_Axiom], ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC ``(h:'a+'b->'b+'a)`` THEN REPEAT (POP_ASSUM MP_TAC) THEN
  SIMP_TAC std_ss [FORALL_SUM, EXISTS_SUM, EXISTS_UNIQUE_THM] THEN
  SIMP_TAC std_ss [sum_distinct, INR_11, INL_11, IN_CARD_ADD]);

val CARD_ADD_ASSOC = store_thm ("CARD_ADD_ASSOC",
 ``!s:'a->bool t:'b->bool u:'c->bool. (s +_c (t +_c u)) =_c ((s +_c t) +_c u)``,
  REPEAT GEN_TAC THEN REWRITE_TAC[eq_c] THEN
  KNOW_TAC ``?(i:'b+'c->('a+'b)+'c). (!u. i (INL u) = INL(INR u)) /\
                                     (!v. i (INR v) = INR v)`` THENL 
  [RW_TAC std_ss [sum_Axiom], STRIP_TAC] THEN
  KNOW_TAC ``?(h:'a+'b+'c->('a+'b)+'c).
     (!x. h (INL x) = INL(INL x)) /\ (!z. h(INR z) = i(z))`` THENL
  [RW_TAC std_ss [sum_Axiom], ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC ``(h:'a+'b+'c->('a+'b)+'c)`` THEN
  ASM_SIMP_TAC std_ss [FORALL_SUM, EXISTS_SUM, EXISTS_UNIQUE_THM,
                  sum_distinct, INR_11, INL_11, IN_CARD_ADD]);

val CARD_MUL_SYM = store_thm ("CARD_MUL_SYM",
 ``!s:'a->bool t:'b->bool. (s *_c t) =_c (t *_c s)``,
  REPEAT GEN_TAC THEN REWRITE_TAC[eq_c] THEN
  KNOW_TAC ``(?h. !x:'a y:'b. h (x,y) = (y,x))`` THENL
  [RW_TAC std_ss [pair_Axiom], ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC ``(h :'a # 'b -> 'b # 'a)`` THEN
  SIMP_TAC std_ss [EXISTS_UNIQUE_THM, FORALL_PROD, EXISTS_PROD] THEN
  ASM_SIMP_TAC std_ss [FORALL_PROD, IN_CARD_MUL, PAIR_EQ]);

val CARD_MUL_ASSOC = store_thm ("CARD_MUL_ASSOC",
 ``!s:'a->bool t:'b->bool u:'c->bool. (s *_c (t *_c u)) =_c ((s *_c t) *_c u)``,
  REPEAT GEN_TAC THEN REWRITE_TAC[eq_c] THEN
  KNOW_TAC ``?(i:'a->'b#'c->(('a#'b)#'c)). (!x y z. i x (y,z) = ((x,y),z))`` THENL
  [EXISTS_TAC ``(\x p. ((x, FST p), SND p))`` THEN METIS_TAC [FST, SND], STRIP_TAC] THEN
  KNOW_TAC ``(?(h:'a#'b#'c->('a#'b)#'c). !x p. h (x,p) = i x p)`` THENL
  [RW_TAC std_ss [pair_Axiom], ALL_TAC] THEN
   STRIP_TAC THEN EXISTS_TAC ``(h:'a#'b#'c->('a#'b)#'c)`` THEN
  SIMP_TAC std_ss [EXISTS_UNIQUE_THM, FORALL_PROD, EXISTS_PROD] THEN
  ASM_SIMP_TAC std_ss [FORALL_PROD, IN_CARD_MUL, PAIR_EQ]);

val CARD_LDISTRIB = store_thm ("CARD_LDISTRIB",
 ``!s:'a->bool t:'b->bool u:'c->bool.
        (s *_c (t +_c u)) =_c ((s *_c t) +_c (s *_c u))``,
  REPEAT GEN_TAC THEN REWRITE_TAC[eq_c] THEN
  KNOW_TAC
   ``?i. (!x y. (i:'a->('b+'c)->'a#'b+'a#'c) x (INL y) = INL(x,y)) /\
     (!x z. (i:'a->('b+'c)->'a#'b+'a#'c) x (INR z) = INR(x,z))`` THENL
  [EXISTS_TAC ``(\(x:'a) (y:'b+'c). if (?z:'b. y = INL z) 
                  then INL(x,@z. y = INL z) else INR(x,(OUTR:'b+'c->'c) y))`` THEN
   SIMP_TAC std_ss [], STRIP_TAC] THEN
  KNOW_TAC ``?h. (!x s. (h:'a#('b+'c)->('a#'b)+('a#'c)) (x,s) = i x s)`` THENL
  [RW_TAC std_ss [pair_Axiom], ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC ``(h:'a#('b+'c)->('a#'b)+('a#'c))`` THEN
  ASM_SIMP_TAC std_ss [EXISTS_UNIQUE_THM, FORALL_PROD, EXISTS_PROD,
                       FORALL_SUM, EXISTS_SUM, PAIR_EQ, IN_CARD_MUL,
                       sum_distinct, INL_11, INR_11, IN_CARD_ADD]);

val CARD_RDISTRIB = store_thm ("CARD_RDISTRIB",
 ``!s:'a->bool t:'b->bool u:'c->bool.
        ((s +_c t) *_c u) =_c ((s *_c u) +_c (t *_c u))``,
  REPEAT GEN_TAC THEN
  KNOW_TAC ``((u:'c->bool) *_c ((s:'a->bool) +_c (t:'b->bool))) =_c
              (((s:'a->bool) *_c (u:'c->bool)) +_c ((t:'b->bool) *_c u))`` THENL
  [ALL_TAC, METIS_TAC [CARD_MUL_SYM, CARD_EQ_TRANS]] THEN
  KNOW_TAC ``(((u:'c->bool) *_c (s:'a->bool)) +_c (u *_c (t:'b->bool))) =_c 
             ((s *_c u) +_c (t *_c u))`` THENL
  [ALL_TAC, METIS_TAC [CARD_EQ_TRANS, CARD_LDISTRIB]] THEN
  MATCH_MP_TAC CARD_ADD_CONG THEN REWRITE_TAC[CARD_MUL_SYM]);

val CARD_LE_ADDR = store_thm ("CARD_LE_ADDR",
 ``!s:'a->bool t:'b->bool. s <=_c (s +_c t)``,
  REPEAT GEN_TAC THEN REWRITE_TAC[le_c] THEN
  EXISTS_TAC ``INL:'a->'a+'b`` THEN SIMP_TAC std_ss [IN_CARD_ADD, INR_11, INL_11]);;

val CARD_LE_ADDL = store_thm ("CARD_LE_ADDL",
 ``!s:'a->bool t:'b->bool. t <=_c (s +_c t)``,
  REPEAT GEN_TAC THEN REWRITE_TAC[le_c] THEN
  EXISTS_TAC ``INR:'b->'a+'b`` THEN SIMP_TAC std_ss [IN_CARD_ADD, INR_11, INL_11]);

(* ------------------------------------------------------------------------- *)
(* A rather special lemma but temporarily useful.                            *)
(* ------------------------------------------------------------------------- *)

val CARD_ADD_LE_MUL_INFINITE = store_thm ("CARD_ADD_LE_MUL_INFINITE",
 ``!s:'a->bool. INFINITE s ==> (s +_c s) <=_c (s *_c s)``,
  GEN_TAC THEN REWRITE_TAC[INFINITE_CARD_LE, le_c, IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN ``f:num->'a`` STRIP_ASSUME_TAC) THEN
  KNOW_TAC ``?h. (!x. h(INL x) = (f(0:num),x):'a#'a) /\ (!x. h(INR x) = (f(1),x))`` THENL
  [RW_TAC std_ss [sum_Axiom], ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC ``h:'a+'a->'a#'a`` THEN STRIP_TAC THENL
  [ONCE_REWRITE_TAC [METIS [] ``( x IN s +_c s ==> h x IN s *_c s) =
                            (\x.  x IN s +_c s ==> h x IN s *_c s) x``] THEN
   MATCH_MP_TAC sum_INDUCT THEN
   ASM_SIMP_TAC std_ss [IN_CARD_ADD, IN_CARD_MUL, PAIR_EQ], ALL_TAC] THEN
   ONCE_REWRITE_TAC [METIS [] ``(!y. x IN s +_c s /\ y IN s +_c s /\ (h x = h y) ==> (x = y)) =
                          (\x. !y. x IN s +_c s /\ y IN s +_c s /\ (h x = h y) ==> (x = y)) x``] THEN
   MATCH_MP_TAC sum_INDUCT THEN
   ASM_SIMP_TAC std_ss [IN_CARD_ADD, IN_CARD_MUL, PAIR_EQ] THEN STRIP_TAC THEN STRIP_TAC THENL
   [ONCE_REWRITE_TAC [METIS [] ``(x IN s /\ y IN s +_c s /\ ((f (0:num),x) =  
                                (h :'a + 'a -> 'a # 'a) y) ==> (INL x = y)) =
                      (\y:'a+'a. x IN s /\ y IN s +_c s /\ ((f (0:num),x) = 
                                (h :'a + 'a -> 'a # 'a) y) ==> (INL x = y)) y``],
    ONCE_REWRITE_TAC [METIS [] ``(x IN s /\ y IN s +_c s /\ ((f (1:num),x) =  
                                (h :'a + 'a -> 'a # 'a) y) ==> (INR x = y)) =
                      (\y:'a+'a. x IN s /\ y IN s +_c s /\ ((f (1:num),x) = 
                                (h :'a + 'a -> 'a # 'a) y) ==> (INR x = y)) y``]] THEN
   MATCH_MP_TAC sum_INDUCT THEN
   ASM_SIMP_TAC std_ss [IN_CARD_ADD, IN_CARD_MUL, PAIR_EQ] THEN
   ASM_MESON_TAC[REDUCE_CONV ``1 = 0:num``]);

(* ------------------------------------------------------------------------- *)
(* Relate cardinal addition to the simple union operation.                   *)
(* ------------------------------------------------------------------------- *)

val CARD_DISJOINT_UNION = store_thm ("CARD_DISJOINT_UNION",
 ``!s:'a->bool t. (s INTER t = EMPTY) ==> (s UNION t =_c (s +_c t))``,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN
  STRIP_TAC THEN REWRITE_TAC[eq_c, IN_UNION] THEN
  EXISTS_TAC ``\x:'a. if x IN s then INL x else INR x`` THEN
  SIMP_TAC std_ss [FORALL_SUM, IN_CARD_ADD] THEN
  REWRITE_TAC[COND_RAND, COND_RATOR] THEN
  REWRITE_TAC[TAUT `(if b then x else y) <=> b /\ x \/ ~b /\ y`] THEN
  SIMP_TAC std_ss [sum_distinct, INL_11, INR_11, IN_CARD_ADD] THEN
  ASM_MESON_TAC[]);

(* ------------------------------------------------------------------------- *)
(* The key to arithmetic on infinite cardinals: k^2 = k.                     *)
(* ------------------------------------------------------------------------- *)

val lemma = prove (
   ``INFINITE(s:'a->bool) /\ s SUBSET k /\
     (!x y. R(x,y) ==> x IN (s *_c s) /\ y IN s) /\
     (!x. x IN (s *_c s) ==> ?!y. y IN s /\ R(x,y)) /\
     (!y:'a. y IN s ==> ?!x. x IN (s *_c s) /\ R(x,y))
     ==> (s = {z | ?p. R(p,z)})``,
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN MESON_TAC[]);

val CARD_SQUARE_INFINITE = store_thm ("CARD_SQUARE_INFINITE",
 ``!k:'a->bool. INFINITE k ==> ((k *_c k) =_c k)``,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   ``P = \R. ?s. INFINITE(s:'a->bool) /\ s SUBSET k /\
                 (!x y. R(x,y) ==> x IN (s *_c s) /\ y IN s) /\
                 (!x. x IN (s *_c s) ==> ?!y. y IN s /\ R(x,y)) /\
                 (!y. y IN s ==> ?!x. x IN (s *_c s) /\ R(x,y))`` THEN
  MP_TAC(ISPEC ``P:(('a#'a)#'a->bool)->bool`` ZL_SUBSETS_BIGUNION_NONEMPTY) THEN
  KNOW_TAC ``(?(x :('a # 'a) # 'a -> bool).
    (P :(('a # 'a) # 'a -> bool) -> bool) x) /\
 (!(c :(('a # 'a) # 'a -> bool) -> bool).
    (?(x :('a # 'a) # 'a -> bool). x IN c) /\
    (!(x :('a # 'a) # 'a -> bool). x IN c ==> P x) /\
    (!(x :('a # 'a) # 'a -> bool) (y :('a # 'a) # 'a -> bool).
       x IN c /\ y IN c ==> x SUBSET y \/ y SUBSET x) ==>
    P (BIGUNION c))`` THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN SIMP_TAC std_ss [] THEN
      KNOW_TAC ``?(s :'a -> bool) (x :('a # 'a) # 'a -> bool).
       INFINITE s /\ s SUBSET (k :'a -> bool) /\
       (!(x' :'a # 'a) (y :'a). x (x',y) ==> x' IN s *_c s /\ y IN s) /\
       (!(x' :'a # 'a). x' IN s *_c s ==> ?!(y :'a). y IN s /\ x (x',y)) /\
        !(y :'a). y IN s ==> ?!(x' :'a # 'a). x' IN s *_c s /\ x (x',y)`` THENL
      [ALL_TAC, STRIP_TAC THEN EXISTS_TAC ``(x :('a # 'a) # 'a -> bool)`` THEN
       EXISTS_TAC ``(s :'a -> bool)`` THEN METIS_TAC []] THEN
      SIMP_TAC std_ss [RIGHT_EXISTS_AND_THM, GSYM EQ_C] THEN
      FIRST_X_ASSUM(MP_TAC o REWRITE_RULE [INFINITE_CARD_LE]) THEN
      SIMP_TAC std_ss [CARD_LE_EQ_SUBSET] THEN
      DISCH_THEN (X_CHOOSE_TAC ``s:'a->bool``) THEN EXISTS_TAC ``s:'a->bool`` THEN
      POP_ASSUM MP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[num_INFINITE, CARD_INFINITE_CONG], ALL_TAC] THEN
      FIRST_ASSUM(fn th =>
       MP_TAC(MATCH_MP CARD_MUL_CONG (CONJ th th))) THEN
      GEN_REWR_TAC LAND_CONV [CARD_EQ_SYM] THEN
      DISCH_THEN(MP_TAC o C CONJ CARD_SQUARE_NUM) THEN
      DISCH_THEN(MP_TAC o MATCH_MP CARD_EQ_TRANS) THEN
      FIRST_ASSUM(fn th =>
        DISCH_THEN(ACCEPT_TAC o MATCH_MP CARD_EQ_TRANS o C CONJ th)),
      ALL_TAC] THEN
    SUBGOAL_THEN
     ``P = \R. INFINITE {z | ?x y. R((x,y),z)} /\
              (!x:'a y z. R((x,y),z) ==> x IN k /\ y IN k /\ z IN k) /\
              (!x y. (?u v. R((u,v),x)) /\ (?u v. R((u,v),y))
                     ==> ?z. R((x,y),z)) /\
              (!x y. (?z. R((x,y),z))
                     ==> (?u v. R((u,v),x)) /\ (?u v. R((u,v),y))) /\
              (!x y z1 z2. R((x,y),z1) /\ R((x,y),z2) ==> (z1 = z2)) /\
              (!x1 y1 x2 y2 z. R((x1,y1),z) /\ R((x2,y2),z)
                               ==> (x1 = x2) /\ (y1 = y2))``
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN SIMP_TAC std_ss [] THEN
      ONCE_REWRITE_TAC[MATCH_MP(TAUT `(a ==> b) ==> (a <=> b /\ a)`) lemma] THEN
      SIMP_TAC std_ss [UNWIND_THM2] THEN SIMP_TAC std_ss [FUN_EQ_THM] THEN
      SIMP_TAC std_ss [IN_CARD_MUL, EXISTS_PROD, SUBSET_DEF, FUN_EQ_THM,
                       GSPECIFICATION, FORALL_PROD, EXISTS_UNIQUE_THM,
                       BIGUNION, PAIR_EQ] THEN
      GEN_TAC THEN AP_TERM_TAC THEN MESON_TAC[],
      ALL_TAC] THEN
    FIRST_X_ASSUM(K ALL_TAC o SYM) THEN SIMP_TAC std_ss [] THEN GEN_TAC THEN
    GEN_REWR_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
    DISCH_THEN (MP_TAC o SIMP_RULE std_ss [FORALL_AND_THM]) THEN
    MATCH_MP_TAC(TAUT
     `(c /\ d ==> f) /\ (a /\ b ==> e)
      ==> (a /\ (b /\ c) /\ d ==> e /\ f)`) THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC [METIS [SPECIFICATION]
       ``BIGUNION c ((x1,y1),z) = ((x1,y1),z) IN BIGUNION c``] THEN
      SIMP_TAC std_ss [BIGUNION, GSPECIFICATION] THEN
      SIMP_TAC std_ss [SUBSET_DEF, IN_DEF] THEN MESON_TAC[],
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC ``s:('a#'a)#'a->bool``) MP_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC ``s:('a#'a)#'a->bool``) THEN
    ASM_REWRITE_TAC[GSYM MONO_NOT_EQ] THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE[TAUT `a /\ b ==> c <=> b ==> a ==> c`]
                      SUBSET_FINITE_I) THEN
    ONCE_REWRITE_TAC [METIS [SPECIFICATION]
       ``BIGUNION c ((x1,y1),z) = ((x1,y1),z) IN BIGUNION c``] THEN
    SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, BIGUNION] THEN ASM_MESON_TAC[IN_DEF],
    DISCH_TAC THEN ASM_REWRITE_TAC [] THEN POP_ASSUM K_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN SIMP_TAC std_ss [] THEN
  DISCH_THEN(X_CHOOSE_THEN ``R:('a#'a)#'a->bool``
   (CONJUNCTS_THEN2 (X_CHOOSE_TAC ``s:'a->bool``) ASSUME_TAC)) THEN
  SUBGOAL_THEN ``((s:'a->bool) *_c s) =_c s`` ASSUME_TAC THENL
   [REWRITE_TAC[EQ_C] THEN EXISTS_TAC ``R:('a#'a)#'a->bool`` THEN METIS_TAC [],
    ALL_TAC] THEN
  SUBGOAL_THEN ``(s +_c s) <=_c (s:'a->bool)`` ASSUME_TAC THENL
   [KNOW_TAC ``(s +_c s) <=_c ((s:'a->bool) *_c s) /\ ((s:'a->bool) *_c s) <=_c s`` THENL
    [ALL_TAC, METIS_TAC [CARD_LE_TRANS]] THEN
    ASM_SIMP_TAC std_ss [CARD_EQ_IMP_LE, CARD_ADD_LE_MUL_INFINITE],
    ALL_TAC] THEN
  SUBGOAL_THEN ``(s:'a->bool) INTER (k DIFF s) = EMPTY`` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION, IN_INTER, IN_DIFF, NOT_IN_EMPTY] THEN MESON_TAC[],
    ALL_TAC] THEN
  DISJ_CASES_TAC(ISPECL [``k DIFF (s:'a->bool)``, ``s:'a->bool``] CARD_LE_TOTAL)
  THENL
   [SUBGOAL_THEN ``k = (s:'a->bool) UNION (k DIFF s)`` SUBST1_TAC THENL
     [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
      REWRITE_TAC[SUBSET_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY,
                  IN_UNION, IN_DIFF] THEN
      MESON_TAC[],
      ALL_TAC] THEN
    SIMP_TAC std_ss [GSYM CARD_LE_ANTISYM, CARD_LE_SQUARE] THEN
    KNOW_TAC ``(s UNION (k DIFF s) *_c s UNION (k DIFF s)) <=_c 
               (((s:'a->bool) +_c (k DIFF s:'a->bool)) *_c (s +_c k DIFF s)) /\
               (((s:'a->bool) +_c (k DIFF s:'a->bool)) *_c (s +_c k DIFF s)) <=_c
                s UNION (k DIFF s)`` THENL
    [ALL_TAC, METIS_TAC [CARD_LE_TRANS]] THEN
    ASM_SIMP_TAC std_ss [CARD_DISJOINT_UNION, CARD_EQ_IMP_LE, CARD_MUL_CONG] THEN
    KNOW_TAC ``((s +_c k DIFF s) *_c (s +_c k DIFF s)) <=_c 
               (((s:'a->bool) +_c s) *_c (s +_c s)) /\
               (((s:'a->bool) +_c s) *_c (s +_c s)) <=_c s UNION (k DIFF s)`` THENL
    [ALL_TAC, METIS_TAC [CARD_LE_TRANS]] THEN
    ASM_SIMP_TAC std_ss [CARD_LE_ADD, CARD_LE_MUL, CARD_LE_REFL] THEN
    KNOW_TAC ``((s +_c s) *_c (s +_c s)) <=_c ((s:'a->bool) *_c s) /\
               ((s:'a->bool) *_c s) <=_c (s UNION (k DIFF s))`` THENL
    [ALL_TAC, METIS_TAC [CARD_LE_TRANS]] THEN
    ASM_SIMP_TAC std_ss [CARD_LE_MUL] THEN
    KNOW_TAC ``(s *_c s) <=_c (s:'a->bool) /\ (s:'a->bool) <=_c s UNION (k DIFF s)`` THENL
    [ALL_TAC, METIS_TAC [CARD_LE_TRANS]] THEN
    ASM_SIMP_TAC std_ss [CARD_EQ_IMP_LE] THEN
    SIMP_TAC std_ss [CARD_LE_EQ_SUBSET] THEN EXISTS_TAC ``s:'a->bool`` THEN
    SIMP_TAC std_ss [CARD_EQ_REFL, SUBSET_DEF, IN_UNION],
    ALL_TAC] THEN
  UNDISCH_TAC ``s:'a->bool <=_c k DIFF s`` THEN
  SIMP_TAC std_ss [CARD_LE_EQ_SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN ``d:'a->bool`` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN ``(s:'a->bool *_c d) UNION (d *_c s) UNION (d *_c d) =_c d``
  MP_TAC THENL
   [KNOW_TAC ``(s *_c d) UNION (d *_c s) UNION (d *_c d) =_c 
               (((s:'a->bool) *_c (d:'a->bool)) +_c ((d *_c s) +_c (d *_c d))) /\ 
               (((s:'a->bool) *_c (d:'a->bool)) +_c ((d *_c s) +_c (d *_c d))) =_c d`` THENL
    [ALL_TAC, METIS_TAC [CARD_EQ_TRANS]] THEN CONJ_TAC THENL
     [KNOW_TAC ``(s *_c d) UNION (d *_c s) UNION (d *_c d) =_c
                 (((s:'a->bool) *_c d) +_c ((d *_c s) UNION (d *_c d))) /\
                 (((s:'a->bool) *_c d) +_c ((d *_c s) UNION (d *_c d))) =_c
                 ((s *_c d) +_c ((d *_c s) +_c (d *_c d)))`` THENL
      [ALL_TAC, METIS_TAC [CARD_EQ_TRANS]] THEN
      CONJ_TAC THENL
       [ALL_TAC,
        MATCH_MP_TAC CARD_ADD_CONG THEN SIMP_TAC std_ss [CARD_EQ_REFL]] THEN
      REWRITE_TAC [GSYM UNION_ASSOC] THEN
      MATCH_MP_TAC CARD_DISJOINT_UNION THEN
      UNDISCH_TAC ``s INTER (k DIFF s:'a->bool) = {}`` THEN
      UNDISCH_TAC ``d SUBSET (k DIFF s:'a->bool)`` THEN
      SIMP_TAC std_ss [EXTENSION, SUBSET_DEF, FORALL_PROD, NOT_IN_EMPTY,
                  IN_INTER, IN_UNION, IN_CARD_MUL, IN_DIFF] THEN MESON_TAC[],
      ALL_TAC] THEN
    KNOW_TAC ``(((s *_c d) +_c (((d:'a->bool) *_c s) +_c (d *_c d))) =_c s) /\ 
               ((s:'a->bool) =_c d)`` THENL
    [ALL_TAC, METIS_TAC [CARD_EQ_TRANS]] THEN ASM_SIMP_TAC std_ss [] THEN
    KNOW_TAC ``(((s *_c d) +_c ((d *_c s) +_c (d *_c (d:'a->bool)))) =_c 
               ((s:'a->bool *_c s) +_c ((s *_c s) +_c (s *_c s)))) /\
               (((s:'a->bool *_c s) +_c ((s *_c s) +_c (s *_c s))) =_c s)`` THENL
    [ALL_TAC, METIS_TAC [CARD_EQ_TRANS]] THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC CARD_ADD_CONG THEN CONJ_TAC) THEN
      MATCH_MP_TAC CARD_MUL_CONG THEN ASM_REWRITE_TAC[CARD_EQ_REFL] THEN
      ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN ASM_REWRITE_TAC[],
      ALL_TAC] THEN
    KNOW_TAC ``(((s *_c s) +_c ((s *_c s) +_c (s *_c s))) =_c 
               ((s:'a->bool) +_c (s +_c s))) /\ 
               (((s:'a->bool) +_c (s +_c s)) =_c s)`` THENL
    [ALL_TAC, METIS_TAC [CARD_EQ_TRANS]] THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC CARD_ADD_CONG THEN ASM_REWRITE_TAC[]),
      ALL_TAC] THEN
    REWRITE_TAC[GSYM CARD_LE_ANTISYM, CARD_LE_ADDR] THEN
    KNOW_TAC ``(s +_c (s +_c s)) <=_c ((s:'a->bool) +_c s) /\
               ((s:'a->bool) +_c s) <=_c s`` THENL
    [ALL_TAC, METIS_TAC [CARD_LE_TRANS]] THEN
    ASM_SIMP_TAC std_ss [CARD_LE_ADD, CARD_LE_REFL],
    ALL_TAC] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
  SIMP_TAC std_ss [EQ_C, IN_UNION] THEN
  DISCH_THEN(X_CHOOSE_TAC ``SS:('a#'a)#'a->bool``) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC ``\x:('a#'a)#'a. R(x) \/ SS(x)``) THEN
  ONCE_REWRITE_TAC[MONO_NOT_EQ] THEN DISCH_THEN(K ALL_TAC) THEN
  SIMP_TAC std_ss [NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC ``(s:'a->bool) UNION d``,
    SIMP_TAC std_ss [SUBSET_DEF, IN_DEF],
    SUBGOAL_THEN ``~(d:'a->bool = {})`` MP_TAC THENL
     [DISCH_THEN(MP_TAC o AP_TERM ``FINITE:('a->bool)->bool``) THEN
      SIMP_TAC std_ss [FINITE_EMPTY, FINITE_INSERT] THEN
      ASM_MESON_TAC[CARD_INFINITE_CONG],
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN(X_CHOOSE_TAC ``a:'a``) THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP
     (ASSUME ``a:'a IN d``) o last o CONJUNCTS) THEN
    DISCH_THEN(MP_TAC o EXISTENCE) THEN
    DISCH_THEN(X_CHOOSE_THEN ``b:'a#'a`` (CONJUNCTS_THEN ASSUME_TAC)) THEN
    SIMP_TAC std_ss [EXTENSION, NOT_FORALL_THM] THEN
    EXISTS_TAC ``(b:'a#'a,a:'a)`` THEN ASM_SIMP_TAC std_ss [IN_DEF] THEN
    DISCH_THEN(fn th => FIRST_ASSUM
     (MP_TAC o CONJUNCT2 o C MATCH_MP th o CONJUNCT1)) THEN
    MAP_EVERY UNDISCH_TAC
     [``a:'a IN d``, ``(d:'a->bool) SUBSET (k DIFF s)``] THEN
    REWRITE_TAC[SUBSET_DEF, IN_DIFF] THEN MESON_TAC[]] THEN
  SIMP_TAC std_ss [FINITE_UNION, DE_MORGAN_THM] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [``(d:'a->bool) SUBSET (k DIFF s)``, ``(s:'a->bool) SUBSET k``] THEN
    REWRITE_TAC[SUBSET_DEF, IN_UNION, IN_DIFF] THEN MESON_TAC[],
    ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  SIMP_TAC std_ss [FORALL_PROD, EXISTS_UNIQUE_THM, EXISTS_PROD,
              IN_CARD_MUL, IN_UNION, PAIR_EQ] THEN
  MAP_EVERY UNDISCH_TAC
   [``(s:'a->bool) SUBSET k``,
    ``(d:'a->bool) SUBSET (k DIFF s)``] THEN
  REWRITE_TAC[SUBSET_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER, IN_DIFF] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REPEAT DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[], ASM_MESON_TAC[], ALL_TAC] THEN
  GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [ASM_MESON_TAC[], ALL_TAC] THEN
  DISCH_THEN(fn th => CONJ_TAC THEN MP_TAC th) THENL
   [ALL_TAC, ASM_MESON_TAC[]] THEN
  DISCH_THEN(fn th =>
   FIRST_ASSUM(MP_TAC o C MATCH_MP th o last o CONJUNCTS)) THEN
  MESON_TAC[]);

(* ------------------------------------------------------------------------- *)
(* Preservation of finiteness.                                               *)
(* ------------------------------------------------------------------------- *)

val CARD_ADD_FINITE = store_thm ("CARD_ADD_FINITE",
 ``!s t. FINITE s /\ FINITE t ==> FINITE(s +_c t)``,
  SIMP_TAC std_ss [add_c, FINITE_UNION, GSYM IMAGE_DEF, IMAGE_FINITE]);

val CARD_ADD_FINITE_EQ = store_thm ("CARD_ADD_FINITE_EQ",
 ``!s:'a->bool t:'b->bool. FINITE(s +_c t) <=> FINITE s /\ FINITE t``,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[CARD_ADD_FINITE] THEN
  DISCH_THEN(fn th => CONJ_TAC THEN MP_TAC th) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CARD_LE_FINITE) THEN
  REWRITE_TAC[CARD_LE_ADDL, CARD_LE_ADDR]);

val CARD_MUL_FINITE = store_thm ("CARD_MUL_FINITE",
 ``!s t. FINITE s /\ FINITE t ==> FINITE(s *_c t)``,
  SIMP_TAC std_ss [mul_c, FINITE_PRODUCT]);

(* ------------------------------------------------------------------------- *)
(* Hence the "absorption laws" for arithmetic with an infinite cardinal.     *)
(* ------------------------------------------------------------------------- *)

val CARD_MUL_ABSORB_LE = store_thm ("CARD_MUL_ABSORB_LE",
 ``!s:'a->bool t:'b->bool. INFINITE(t) /\ s <=_c t ==> (s *_c t) <=_c t``,
  REPEAT STRIP_TAC THEN 
  KNOW_TAC ``(s *_c t) <=_c ((t:'b->bool) *_c t) /\
             ((t:'b->bool) *_c t) <=_c t`` THENL
  [ALL_TAC, METIS_TAC [CARD_LE_TRANS]] THEN
  ASM_SIMP_TAC std_ss [CARD_LE_MUL, CARD_LE_REFL,
               CARD_SQUARE_INFINITE, CARD_EQ_IMP_LE]);

val CARD_MUL2_ABSORB_LE = store_thm ("CARD_MUL2_ABSORB_LE",
 ``!s:'a->bool t:'b->bool u:'c->bool.
     INFINITE(u) /\ s <=_c u /\ t <=_c u ==> (s *_c t) <=_c u``,
  REPEAT STRIP_TAC THEN
  KNOW_TAC ``(s *_c t) <=_c ((s:'a->bool) *_c (u:'c->bool)) /\ 
             ((s:'a->bool) *_c (u:'c->bool)) <=_c u`` THENL
  [ALL_TAC, METIS_TAC [CARD_LE_TRANS]] THEN
  ASM_SIMP_TAC std_ss [CARD_MUL_ABSORB_LE] THEN MATCH_MP_TAC CARD_LE_MUL THEN
  ASM_REWRITE_TAC[CARD_LE_REFL]);

val CARD_ADD_ABSORB_LE = store_thm ("CARD_ADD_ABSORB_LE",
 ``!s:'a->bool t:'b->bool. INFINITE(t) /\ s <=_c t ==> (s +_c t) <=_c t``,
  REPEAT STRIP_TAC THEN
  KNOW_TAC ``(s +_c t) <=_c ((t:'b->bool) *_c t) /\
             ((t:'b->bool) *_c t) <=_c t`` THENL
  [ALL_TAC, METIS_TAC [CARD_LE_TRANS]] THEN
  ASM_SIMP_TAC std_ss [CARD_SQUARE_INFINITE, CARD_EQ_IMP_LE] THEN
  KNOW_TAC ``(s +_c t) <=_c ((t:'b->bool) +_c t) /\
             ((t:'b->bool) +_c t) <=_c (t *_c t)`` THENL
  [ALL_TAC, METIS_TAC [CARD_LE_TRANS]] THEN
  ASM_SIMP_TAC std_ss [CARD_ADD_LE_MUL_INFINITE, CARD_LE_ADD, CARD_LE_REFL]);

val CARD_ADD2_ABSORB_LE = store_thm ("CARD_ADD2_ABSORB_LE",
 ``!s:'a->bool t:'b->bool u:'c->bool.
     INFINITE(u) /\ s <=_c u /\ t <=_c u ==> (s +_c t) <=_c u``,
  REPEAT STRIP_TAC THEN
  KNOW_TAC ``(s +_c t) <=_c ((s:'a->bool) +_c (u:'c->bool)) /\
             ((s:'a->bool) +_c (u:'c->bool)) <=_c u`` THENL
  [ALL_TAC, METIS_TAC [CARD_LE_TRANS]] THEN
  ASM_SIMP_TAC std_ss [CARD_ADD_ABSORB_LE] THEN MATCH_MP_TAC CARD_LE_ADD THEN
  ASM_REWRITE_TAC[CARD_LE_REFL]);

val CARD_MUL_ABSORB = store_thm ("CARD_MUL_ABSORB",
 ``!s:'a->bool t:'b->bool.
     INFINITE(t) /\ ~(s = {}) /\ s <=_c t ==> (s *_c t) =_c t``,
  SIMP_TAC std_ss [GSYM CARD_LE_ANTISYM, CARD_MUL_ABSORB_LE] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC ``a:'a`` o
   REWRITE_RULE [GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[le_c] THEN EXISTS_TAC ``\x:'b. (a:'a,x)`` THEN
  ASM_SIMP_TAC std_ss [IN_CARD_MUL, PAIR_EQ]);

val CARD_ADD_ABSORB = store_thm ("CARD_ADD_ABSORB",
 ``!s:'a->bool t:'b->bool. INFINITE(t) /\ s <=_c t ==> (s +_c t) =_c t``,
  SIMP_TAC std_ss [GSYM CARD_LE_ANTISYM, CARD_LE_ADDL, CARD_ADD_ABSORB_LE]);

val CARD_ADD2_ABSORB_LT = store_thm ("CARD_ADD2_ABSORB_LT",
 ``!s:'a->bool t:'b->bool u:'c->bool.
        INFINITE u /\ s <_c u /\ t <_c u ==> (s +_c t) <_c u``,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  ASM_CASES_TAC ``FINITE((s:'a->bool) +_c (t:'b->bool))`` THEN
  ASM_SIMP_TAC std_ss [CARD_LT_FINITE_INFINITE] THEN
  DISJ_CASES_TAC(ISPECL [``s:'a->bool``, ``t:'b->bool``] CARD_LE_TOTAL) THENL
   [(* goal 1 (of 2) *)
    ASM_CASES_TAC ``FINITE(t:'b->bool)`` THENL
     [ASM_MESON_TAC[CARD_LE_FINITE, CARD_ADD_FINITE],
      KNOW_TAC ``(s +_c t) <=_c (t:'b->bool) /\
                 (t:'b->bool) <_c u`` THENL
      [ALL_TAC, METIS_TAC [CARD_LET_TRANS]]],
    (* goal 2 (of 2) *)
    ASM_CASES_TAC ``FINITE(s:'a->bool)`` THENL
     [ASM_MESON_TAC[CARD_LE_FINITE, CARD_ADD_FINITE],
      KNOW_TAC ``(s +_c t) <=_c (s:'a->bool) /\
                 (s:'a->bool) <_c u`` THENL
      [ALL_TAC, METIS_TAC [CARD_LET_TRANS]]]] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CARD_ADD2_ABSORB_LE THEN
  ASM_REWRITE_TAC[CARD_LE_REFL]);

val CARD_LT_ADD = store_thm ("CARD_LT_ADD",
 ``!s:'a->bool s':'b->bool t:'c->bool t':'d->bool.
        s <_c s' /\ t <_c t' ==> (s +_c t) <_c (s' +_c t')``,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  ASM_CASES_TAC ``FINITE((s':'b->bool) +_c (t':'d->bool))`` THENL
   [FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE
      [CARD_ADD_FINITE_EQ]) THEN
    SUBGOAL_THEN ``FINITE(s:'a->bool) /\ FINITE(t:'c->bool)``
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
        (REWRITE_RULE[IMP_CONJ_ALT] CARD_LE_FINITE) o
        MATCH_MP CARD_LT_IMP_LE) THEN
      ASM_REWRITE_TAC[],
      MAP_EVERY UNDISCH_TAC
       [``(s:'a->bool) <_c (s':'b->bool)``,
        ``(t:'c->bool) <_c (t':'d->bool)``] THEN
      ASM_SIMP_TAC std_ss [CARD_LT_CARD, CARD_ADD_FINITE, CARD_ADD_C] THEN
      ARITH_TAC],
    MATCH_MP_TAC CARD_ADD2_ABSORB_LT THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [METIS_TAC [CARD_LTE_TRANS, CARD_LE_ADDR],
      METIS_TAC [CARD_LTE_TRANS, CARD_LE_ADDL]]]);

(* ------------------------------------------------------------------------- *)
(* Some more ad-hoc but useful theorems.                                     *)
(* ------------------------------------------------------------------------- *)

val CARD_MUL_LT_LEMMA = store_thm ("CARD_MUL_LT_LEMMA",
 ``!s t:'b->bool u. s <=_c t /\ t <_c u /\ INFINITE u ==> (s *_c t) <_c u``,
  REPEAT GEN_TAC THEN ASM_CASES_TAC ``FINITE(t:'b->bool)`` THENL
   [REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ONCE_REWRITE_TAC[MONO_NOT_EQ] THEN REWRITE_TAC[CARD_NOT_LT] THEN
    ASM_MESON_TAC[CARD_LE_FINITE, CARD_MUL_FINITE],
    ASM_MESON_TAC[CARD_MUL_ABSORB_LE, CARD_LET_TRANS]]);

val CARD_MUL_LT_INFINITE = store_thm ("CARD_MUL_LT_INFINITE",
 ``!s:'a->bool t:'b->bool u. s <_c u /\ t <_c u /\ INFINITE u ==> (s *_c t) <_c u``,
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC(ISPECL [``s:'a->bool``, ``t:'b->bool``] CARD_LE_TOTAL) THENL
   [ASM_MESON_TAC[CARD_MUL_SYM, CARD_MUL_LT_LEMMA],
    STRIP_TAC THEN KNOW_TAC ``(s *_c t) <=_c (t:'b->bool *_c s:'a->bool) /\
                              (t:'b->bool *_c s:'a->bool) <_c u`` THENL
    [ALL_TAC, METIS_TAC [CARD_LET_TRANS]] THEN
    ASM_MESON_TAC[CARD_EQ_IMP_LE, CARD_MUL_SYM, CARD_MUL_LT_LEMMA]]);

(* ------------------------------------------------------------------------- *)
(* Cantor's theorem.                                                         *)
(* ------------------------------------------------------------------------- *)

val CANTOR_THM = store_thm ("CANTOR_THM",
 ``!s:'a->bool. s <_c {t | t SUBSET s}``,
  GEN_TAC THEN ONCE_REWRITE_TAC [lt_c] THEN CONJ_TAC THENL
   [REWRITE_TAC[le_c] THEN EXISTS_TAC ``(=):'a->'a->bool`` THEN
    SIMP_TAC std_ss [FUN_EQ_THM] THEN 
    SIMP_TAC std_ss [GSPECIFICATION,  SUBSET_DEF, IN_DEF],
    SIMP_TAC std_ss [LE_C, GSPECIFICATION, SURJECTIVE_RIGHT_INVERSE] THEN
    X_GEN_TAC ``g:'a->('a->bool)`` THEN
    EXISTS_TAC ``\x:'a. s(x) /\ ~((g:'a->('a->bool)) x x)`` THEN
    SIMP_TAC std_ss [SUBSET_DEF, IN_DEF, FUN_EQ_THM] THEN MESON_TAC[]]);

val CANTOR_THM_UNIV = store_thm ("CANTOR_THM_UNIV",
 ``(UNIV:'a->bool) <_c (UNIV:('a->bool)->bool)``,
  MP_TAC(ISPEC ``UNIV:'a->bool`` CANTOR_THM) THEN
  MATCH_MP_TAC EQ_IMPLIES THEN AP_TERM_TAC THEN
  SIMP_TAC std_ss [EXTENSION, SUBSET_DEF, IN_UNIV, GSPECIFICATION] THEN
  SUFF_TAC ``{t | T} = (UNIV:('a->bool)->bool)``
  THEN1 ( DISCH_TAC THEN ASM_REWRITE_TAC [] ) THEN
  ONCE_REWRITE_TAC [GSYM EQ_UNIV] THEN
  RW_TAC std_ss [GSPECIFICATION]);


(* ------------------------------------------------------------------------- *)
(* Lemmas about countability.                                                *)
(* ------------------------------------------------------------------------- *)

val NUM_COUNTABLE = store_thm ("NUM_COUNTABLE",
 ``COUNTABLE univ(:num)``,
  REWRITE_TAC[COUNTABLE, ge_c, CARD_LE_REFL]);

val COUNTABLE_ALT_cardleq = store_thm
  ("COUNTABLE_ALT_cardleq",
 ``!s. COUNTABLE s <=> s <=_c univ(:num)``,
  REWRITE_TAC[COUNTABLE, ge_c]);

val COUNTABLE_CASES = store_thm ("COUNTABLE_CASES",
  ``!s. COUNTABLE s <=> FINITE s \/ s =_c univ(:num)``,
    GEN_TAC
 >> ONCE_REWRITE_TAC[COUNTABLE_ALT_cardleq, FINITE_CARD_LT]
 >> METIS_TAC [CARD_LE_LT]);

val CARD_LE_COUNTABLE = store_thm ("CARD_LE_COUNTABLE",
 ``!s:'a->bool t:'a->bool. COUNTABLE t /\ s <=_c t ==> COUNTABLE s``,
  REWRITE_TAC[COUNTABLE, ge_c] THEN REPEAT STRIP_TAC THEN
  KNOW_TAC ``?(t :'a -> bool).
      (s :'a -> bool) <=_c t /\ t <=_c univ((:num) :num itself)`` THENL
  [EXISTS_TAC ``t:'a->bool`` THEN ASM_REWRITE_TAC[],
   METIS_TAC [CARD_LE_TRANS]]);

val CARD_EQ_COUNTABLE = store_thm ("CARD_EQ_COUNTABLE",
 ``!s:'a->bool t:'a->bool. COUNTABLE t /\ s =_c t ==> COUNTABLE s``,
  REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN MESON_TAC[CARD_LE_COUNTABLE]);

val CARD_COUNTABLE_CONG = store_thm ("CARD_COUNTABLE_CONG",
 ``!s:'a->bool t:'a->bool. s =_c t ==> (COUNTABLE s <=> COUNTABLE t)``,
  REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN MESON_TAC[CARD_LE_COUNTABLE]);

val COUNTABLE_RESTRICT = store_thm ("COUNTABLE_RESTRICT",
 ``!s P. COUNTABLE s ==> COUNTABLE {x | x IN s /\ P x}``,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[CONJ_EQ_IMP] COUNTABLE_SUBSET) THEN
  SET_TAC[]);

val FINITE_IMP_COUNTABLE = store_thm ("FINITE_IMP_COUNTABLE",
 ``!s. FINITE s ==> COUNTABLE s``,
  SIMP_TAC std_ss [FINITE_CARD_LT, Once lt_c, COUNTABLE, ge_c]);

val COUNTABLE_IMAGE = store_thm ("COUNTABLE_IMAGE",
 ``!f:'a->'b s. COUNTABLE s ==> COUNTABLE (IMAGE f s)``,
  SIMP_TAC std_ss [COUNTABLE, ge_c] THEN REPEAT STRIP_TAC THEN
  KNOW_TAC ``IMAGE (f:'a->'b) s <=_c s /\ s <=_c univ(:num)`` THENL
  [ASM_SIMP_TAC std_ss [CARD_LE_IMAGE], METIS_TAC [CARD_LE_TRANS]]);

val COUNTABLE_IMAGE_INJ_GENERAL = store_thm ("COUNTABLE_IMAGE_INJ_GENERAL",
 ``!(f:'a->'b) A s.
        (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) /\
        COUNTABLE A
        ==> COUNTABLE {x | x IN s /\ f(x) IN A}``,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC ``!x y. x IN s /\ y IN s /\ ((f:'a->'b) x = f y) ==> 
                (x = y)`` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE [INJECTIVE_ON_LEFT_INVERSE]) THEN
  DISCH_THEN(X_CHOOSE_TAC ``g:'b->'a``) THEN
  MATCH_MP_TAC COUNTABLE_SUBSET THEN EXISTS_TAC ``IMAGE (g:'b->'a) A`` THEN
  ASM_SIMP_TAC std_ss [COUNTABLE_IMAGE] THEN ASM_SET_TAC[]);

val COUNTABLE_IMAGE_INJ_EQ = store_thm ("COUNTABLE_IMAGE_INJ_EQ",
 ``!(f:'a->'b) s.
        (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y))
        ==> (COUNTABLE(IMAGE f s) <=> COUNTABLE s)``,
  REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC std_ss [COUNTABLE_IMAGE] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[AND_IMP_INTRO] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COUNTABLE_IMAGE_INJ_GENERAL) THEN
  MATCH_MP_TAC EQ_IMPLIES THEN AP_TERM_TAC THEN SET_TAC[]);

val COUNTABLE_IMAGE_INJ = store_thm ("COUNTABLE_IMAGE_INJ",
 ``!(f:'a->'b) A.
        (!x y. (f(x) = f(y)) ==> (x = y)) /\
         COUNTABLE A
         ==> COUNTABLE {x | f(x) IN A}``,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [``f:'a->'b``, ``A:'b->bool``, ``UNIV:'a->bool``]
    COUNTABLE_IMAGE_INJ_GENERAL) THEN SIMP_TAC std_ss [IN_UNIV]);

val COUNTABLE_EMPTY = store_thm ("COUNTABLE_EMPTY",
 ``COUNTABLE {}``,
  REWRITE_TAC [COUNTABLE, ge_c, le_c, NOT_IN_EMPTY]);

val COUNTABLE_INTER = store_thm ("COUNTABLE_INTER",
 ``!s t. COUNTABLE s \/ COUNTABLE t ==> COUNTABLE (s INTER t)``,
  REWRITE_TAC[TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`] THEN
  REPEAT GEN_TAC THEN CONJ_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[CONJ_EQ_IMP] COUNTABLE_SUBSET) THEN
  SET_TAC[]);

val COUNTABLE_UNION_IMP = store_thm ("COUNTABLE_UNION_IMP",
 ``!s t:'a->bool. COUNTABLE s /\ COUNTABLE t ==> COUNTABLE(s UNION t)``,
  REWRITE_TAC[COUNTABLE, ge_c] THEN REPEAT STRIP_TAC THEN
  KNOW_TAC ``s UNION t <=_c ((s:'a->bool) +_c (t:'a->bool)) /\
             ((s:'a->bool) +_c (t:'a->bool)) <=_c univ(:num)`` THENL
  [ALL_TAC, METIS_TAC [CARD_LE_TRANS]] THEN
  ASM_SIMP_TAC std_ss [CARD_ADD2_ABSORB_LE, num_INFINITE, UNION_LE_ADD_C]);

val COUNTABLE_UNION = store_thm ("COUNTABLE_UNION",
 ``!s t:'a->bool. COUNTABLE(s UNION t) <=> COUNTABLE s /\ COUNTABLE t``,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[COUNTABLE_UNION_IMP] THEN
  DISCH_THEN(fn th => CONJ_TAC THEN MP_TAC th) THEN
  MATCH_MP_TAC(REWRITE_RULE[CONJ_EQ_IMP] COUNTABLE_SUBSET) THEN
  SET_TAC[]);

val COUNTABLE_SING = store_thm ("COUNTABLE_SING",
 ``!x. COUNTABLE {x}``,
  REWRITE_TAC [COUNTABLE, ge_c, le_c, IN_SING, IN_UNIV] THEN
  METIS_TAC []);

val COUNTABLE_INSERT = store_thm ("COUNTABLE_INSERT",
 ``!x s. COUNTABLE(x INSERT s) <=> COUNTABLE s``,
  ONCE_REWRITE_TAC[SET_RULE ``x INSERT s = {x} UNION s``] THEN
  REWRITE_TAC[COUNTABLE_UNION, COUNTABLE_SING]);

val COUNTABLE_DELETE = store_thm ("COUNTABLE_DELETE",
 ``!x:'a s. COUNTABLE(s DELETE x) <=> COUNTABLE s``,
  REPEAT GEN_TAC THEN ASM_CASES_TAC ``(x:'a) IN s`` THEN
  ASM_SIMP_TAC std_ss [SET_RULE ``~(x IN s) ==> (s DELETE x = s)``] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC ``COUNTABLE((x:'a) INSERT (s DELETE x))`` THEN CONJ_TAC THENL
   [REWRITE_TAC[COUNTABLE_INSERT], AP_TERM_TAC THEN ASM_SET_TAC[]]);

val COUNTABLE_DIFF_FINITE = store_thm ("COUNTABLE_DIFF_FINITE",
 ``!s t. FINITE s ==> (COUNTABLE(t DIFF s) <=> COUNTABLE t)``,
  SIMP_TAC std_ss [RIGHT_FORALL_IMP_THM] THEN
  ONCE_REWRITE_TAC [METIS [] ``!s. (!t. COUNTABLE (t DIFF s) <=> COUNTABLE t) =
                          (\s. !t. COUNTABLE (t DIFF s) <=> COUNTABLE t) s``] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN BETA_TAC THEN
  SIMP_TAC std_ss [DIFF_EMPTY, SET_RULE ``s DIFF (x INSERT t) = (s DIFF t) DELETE x``,
           COUNTABLE_DELETE]);

val COUNTABLE_CROSS = store_thm ("COUNTABLE_CROSS",
  ``!s t. COUNTABLE s /\ COUNTABLE t ==> COUNTABLE(s CROSS t)``,
    rpt GEN_TAC
 >> REWRITE_TAC [COUNTABLE, ge_c]
 >> STRIP_TAC
 >> MATCH_MP_TAC (Q.SPEC `UNIV`
                   (INST_TYPE [``:'c`` |-> ``:num``]
                     (ISPECL [``s :'a set``, ``t :'b set``] CARD_MUL2_ABSORB_LE)))
 >> ASM_REWRITE_TAC [num_INFINITE]);

val COUNTABLE_AS_IMAGE_SUBSET = store_thm ("COUNTABLE_AS_IMAGE_SUBSET",
 ``!s. COUNTABLE s ==> ?f. s SUBSET (IMAGE f univ(:num))``,
  REWRITE_TAC[COUNTABLE, ge_c, LE_C, SUBSET_DEF, IN_IMAGE] THEN MESON_TAC[]);

val COUNTABLE_AS_IMAGE_SUBSET_EQ = store_thm ("COUNTABLE_AS_IMAGE_SUBSET_EQ",
 ``!s:'a->bool. COUNTABLE s <=> ?f. s SUBSET (IMAGE f univ(:num))``,
  REWRITE_TAC[COUNTABLE, ge_c, LE_C, SUBSET_DEF, IN_IMAGE] THEN MESON_TAC[]);
 
val COUNTABLE_AS_IMAGE = store_thm ("COUNTABLE_AS_IMAGE",
 ``!s:'a->bool. COUNTABLE s /\ ~(s = {}) ==> ?f. (s = IMAGE f univ(:num))``,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(X_CHOOSE_TAC ``a:'a`` o
    REWRITE_RULE [GSYM MEMBER_NOT_EMPTY]) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP COUNTABLE_AS_IMAGE_SUBSET) THEN
  DISCH_THEN(X_CHOOSE_TAC ``f:num->'a``) THEN
  EXISTS_TAC ``\n. if (f:num->'a) n IN s then f n else a`` THEN
  ASM_SET_TAC[]);

val FORALL_COUNTABLE_AS_IMAGE = store_thm ("FORALL_COUNTABLE_AS_IMAGE",
 ``(!d. COUNTABLE d ==> P d) <=> P {} /\ (!f. P(IMAGE f univ(:num)))``,
  MESON_TAC[COUNTABLE_AS_IMAGE, COUNTABLE_IMAGE, NUM_COUNTABLE,
            COUNTABLE_EMPTY]);

val COUNTABLE_AS_INJECTIVE_IMAGE = store_thm ("COUNTABLE_AS_INJECTIVE_IMAGE",
 ``!s. COUNTABLE s /\ INFINITE s
       ==> ?f. (s = IMAGE f univ(:num)) /\ (!m n. (f(m) = f(n)) ==> (m = n))``,
  GEN_TAC THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[INFINITE_CARD_LE, COUNTABLE, ge_c] THEN
  SIMP_TAC std_ss [CARD_LE_ANTISYM, eq_c] THEN SET_TAC[]);

val COUNTABLE_BIGUNION = store_thm ("COUNTABLE_BIGUNION",
 ``!A:('a->bool)->bool.
        COUNTABLE A /\ (!s. s IN A ==> COUNTABLE s)
        ==> COUNTABLE (BIGUNION A)``,
  GEN_TAC THEN
  GEN_REWR_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [COUNTABLE_AS_IMAGE_SUBSET_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC ``f:num->'a->bool``) MP_TAC) THEN
  DISCH_THEN (MP_TAC o SIMP_RULE std_ss [RIGHT_IMP_EXISTS_THM]) THEN
  SIMP_TAC std_ss [SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC ``g:('a->bool)->num->'a``) THEN
  MATCH_MP_TAC COUNTABLE_SUBSET THEN
  EXISTS_TAC ``IMAGE (\(m,n). (g:('a->bool)->num->'a) ((f:num->'a->bool) m) n)
                    (univ(:num) CROSS univ(:num))`` THEN
  ASM_SIMP_TAC std_ss [COUNTABLE_IMAGE, COUNTABLE_CROSS, NUM_COUNTABLE] THEN
  SIMP_TAC std_ss [SUBSET_DEF, FORALL_IN_BIGUNION] THEN
  SIMP_TAC std_ss [IN_IMAGE, EXISTS_PROD, IN_CROSS, IN_UNIV] THEN
  ASM_SET_TAC[]);

val COUNTABLE_PRODUCT_DEPENDENT = store_thm ("COUNTABLE_PRODUCT_DEPENDENT",
 ``!f:'a->'b->'c s t.
        COUNTABLE s /\ (!x. x IN s ==> COUNTABLE(t x))
        ==> COUNTABLE {f x y | x IN s /\ y IN (t x)}``,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN ``{(f:'a->'b->'c) x y | x IN s /\ y IN (t x)} =
                 IMAGE (\(x,y). f x y) {(x,y) | x IN s /\ y IN (t x)}``
  SUBST1_TAC THENL
   [SIMP_TAC std_ss [EXTENSION, IN_IMAGE, EXISTS_PROD, IN_ELIM_PAIR_THM] THEN
    SET_TAC[],
    MATCH_MP_TAC COUNTABLE_IMAGE THEN POP_ASSUM MP_TAC] THEN
  GEN_REWR_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [COUNTABLE_AS_IMAGE_SUBSET_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC ``f:num->'a``) MP_TAC) THEN
  DISCH_THEN (MP_TAC o SIMP_RULE std_ss [RIGHT_IMP_EXISTS_THM]) THEN
  SIMP_TAC std_ss [SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC ``g:'a->num->'b``) THEN
  MATCH_MP_TAC COUNTABLE_SUBSET THEN
  EXISTS_TAC ``IMAGE (\(m,n). (f:num->'a) m,(g:'a->num->'b)(f m) n)
                    (univ(:num) CROSS univ(:num))`` THEN
  ASM_SIMP_TAC std_ss [COUNTABLE_IMAGE, COUNTABLE_CROSS, NUM_COUNTABLE] THEN
  SIMP_TAC std_ss [SUBSET_DEF, FORALL_IN_BIGUNION] THEN
  SIMP_TAC std_ss [IN_IMAGE, FORALL_PROD, IN_ELIM_PAIR_THM,
              EXISTS_PROD, IN_CROSS, IN_UNIV] THEN
  ASM_SET_TAC[]);

val _ = export_theory();
