(* ========================================================================= *)
(* FILE          : fcpScript.sml                                             *)
(* DESCRIPTION   : A port, from HOL light, of John Harrison's treatment of   *)
(*                 finite Cartesian products (TPHOLs 2005)                   *)
(* DATE          : 2005                                                      *)
(* ========================================================================= *)

(* interactive use:
  app load ["pred_setTheory","pred_setSimps","quotient"];
*)

open HolKernel Parse boolLib bossLib;
open Q pred_setTheory;

val _ = new_theory "fcp";

(* ------------------------------------------------------------------------- *)

val _ = set_fixity "HAS_SIZE" (Infix(NONASSOC, 450))

val HAS_SIZE = Define`
  (s HAS_SIZE n) = FINITE s /\ (CARD s = n)`;

val CARD_CLAUSES = CONJ CARD_EMPTY (PROVE [CARD_INSERT]
  ``!x s. FINITE s ==>
           (CARD (x INSERT s) = (if x IN s then CARD s else SUC (CARD s)))``);
val IMAGE_CLAUSES = CONJ IMAGE_EMPTY IMAGE_INSERT;
val FINITE_RULES = CONJ FINITE_EMPTY FINITE_INSERT;
val NOT_SUC = numTheory.NOT_SUC;
val SUC_INJ = prim_recTheory.INV_SUC_EQ;
val LT = CONJ (DECIDE ``!m. ~(m < 0)``) prim_recTheory.LESS_THM;
val LT_REFL = prim_recTheory.LESS_REFL;

val CARD_IMAGE_INJ = prove(
  `!(f:'a->'b) s. (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) /\
                FINITE s ==> (CARD (IMAGE f s) = CARD s)`,
  GEN_TAC THEN
  REWRITE_TAC[DECIDE ``a /\ b ==> c = b ==> a ==> c``] THEN
  SPEC_THEN `\s. (!x y. (f x = f y) ==> y IN s ==> x IN s ==> (x = y)) ==>
      (CARD (IMAGE f s) = CARD s)` (MATCH_MP_TAC o BETA_RULE) FINITE_INDUCT THEN
  REWRITE_TAC[NOT_IN_EMPTY, IMAGE_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC std_ss [CARD_CLAUSES, IMAGE_FINITE, IN_IMAGE] THEN
  COND_CASES_TAC THEN PROVE_TAC[IN_INSERT]);

val HAS_SIZE_IMAGE_INJ = prove(
  `!(f:'a->'b) s n.
        (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) /\ (s HAS_SIZE n)
        ==> ((IMAGE f s) HAS_SIZE n)`,
  SIMP_TAC std_ss [HAS_SIZE, IMAGE_FINITE] THEN PROVE_TAC[CARD_IMAGE_INJ]);

val HAS_SIZE_0 = prove(
  `!(s:'a->bool) n. (s HAS_SIZE 0) = (s = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_SIZE] THEN
  EQ_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[FINITE_RULES, CARD_CLAUSES] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1) THEN
  SPEC_TAC(`s:'a->bool`,`s:'a->bool`) THEN
  SPEC_THEN `\s. (CARD s = 0) ==> (s = {})` (MATCH_MP_TAC o BETA_RULE) FINITE_INDUCT THEN
  REWRITE_TAC[NOT_INSERT_EMPTY] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC arith_ss [CARD_INSERT]);

val HAS_SIZE_SUC = prove
 (`!(s:'a->bool) n. (s HAS_SIZE (SUC n)) =
                   ~(s = {}) /\ !a. a IN s ==> ((s DELETE a) HAS_SIZE n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_SIZE] THEN
  ASM_CASES_TAC `s:'a->bool = {}` THEN
  ASM_REWRITE_TAC[CARD_CLAUSES, FINITE_RULES, NOT_IN_EMPTY, GSYM NOT_SUC] THEN
  REWRITE_TAC[FINITE_DELETE] THEN
  ASM_CASES_TAC `FINITE(s:'a->bool)` THEN
  ASM_SIMP_TAC std_ss[NOT_FORALL_THM, MEMBER_NOT_EMPTY] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`a:'a`, `s DELETE a:'a`] (CONJUNCT2 CARD_CLAUSES)) THEN
    ASM_REWRITE_TAC [FINITE_DELETE, IN_DELETE] THEN
    SUBGOAL_THEN `a INSERT (s DELETE a:'a) = s` SUBST1_TAC THENL
     [UNDISCH_TAC `a:'a IN s` THEN PROVE_TAC[INSERT_DELETE],
      ASM_REWRITE_TAC[SUC_INJ] THEN PROVE_TAC[]],
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I empty_rewrites [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `a:'a`) THEN
    MP_TAC(ISPECL [`a:'a`, `s DELETE a:'a`] (CONJUNCT2 CARD_CLAUSES)) THEN
    ASM_REWRITE_TAC[FINITE_DELETE, IN_DELETE] THEN
    SUBGOAL_THEN `a INSERT (s DELETE a:'a) = s` SUBST1_TAC THENL
     [UNDISCH_TAC `a:'a IN s` THEN PROVE_TAC[INSERT_DELETE],
      PROVE_TAC[]]]);

val HAS_SIZE_INDEX = prove(
  `!s n. (s HAS_SIZE n)
         ==> ?f:num->'a. (!m. m < n ==> f(m) IN s) /\
                         (!x. x IN s ==> ?!m. m < n /\ (f m = x))`,
  CONV_TAC SWAP_VARS_CONV THEN numLib.INDUCT_TAC THEN
  SIMP_TAC std_ss [HAS_SIZE_0, HAS_SIZE_SUC, LT, NOT_IN_EMPTY] THEN
  X_GEN_TAC `s:'a->bool` THEN REWRITE_TAC[EXTENSION, NOT_IN_EMPTY] THEN
  SIMP_TAC std_ss[NOT_FORALL_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `a:'a`) (MP_TAC o SPEC `a:'a`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s DELETE (a:'a)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->'a` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\m:num. if m < n then f(m) else a:'a` THEN CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN BETA_TAC THEN COND_CASES_TAC THEN
    PROVE_TAC[IN_DELETE], ALL_TAC] THEN
  X_GEN_TAC `x:'a` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:'a`) THEN
  ASM_SIMP_TAC (std_ss++boolSimps.COND_elim_ss) [IN_DELETE] THEN
  ASM_CASES_TAC `a:'a = x` THEN ASM_SIMP_TAC std_ss [] THEN
  PROVE_TAC[LT_REFL, IN_DELETE]);

(* ------------------------------------------------------------------------- *)
(* An isomorphic image of any finite type, 1-element for infinite ones.      *)
(* ------------------------------------------------------------------------- *)

val finite_image_tybij = BETA_RULE (define_new_type_bijections
  {name="finite_image_tybij", ABS="mk_finite_image", REP="dest_finite_image",
   tyax=new_type_definition("finite_image",
          prove(`?x:'a. (\x. (x = ARB) \/ FINITE(UNIV:'a->bool)) x`,PROVE_TAC[]))});

val FINITE_IMAGE_IMAGE = prove(
  `UNIV:'a finite_image->bool =
    IMAGE mk_finite_image
      (if FINITE(UNIV:'a->bool) then UNIV:'a->bool else {ARB})`,
  MP_TAC finite_image_tybij THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION, IN_IMAGE, IN_SING, IN_UNIV] THEN PROVE_TAC[]);

(* ------------------------------------------------------------------------- *)
(* Dimension of such a type, and indexing over it.                           *)
(* ------------------------------------------------------------------------- *)

val _ = computeLib.auto_import_definitions := false;

val dimindex_def = Define`
  dimindex(:'a) = if FINITE(UNIV:'a->bool) then CARD(UNIV:'a->bool) else 1`;
val dimindex = save_thm("dimindex", dimindex_def);

val NOT_FINITE_IMP_dimindex_1 = Q.store_thm("NOT_FINITE_IMP_dimindex_1",
  `~FINITE univ(:'a) ==> (dimindex (:'a) = 1)`,
  METIS_TAC [dimindex]);

val HAS_SIZE_FINITE_IMAGE = prove(
  `(UNIV:'a finite_image->bool) HAS_SIZE dimindex(:'a)`,
  REWRITE_TAC[dimindex, FINITE_IMAGE_IMAGE] THEN
  MP_TAC finite_image_tybij THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
  ASM_REWRITE_TAC [HAS_SIZE, IN_UNIV, IN_SING] THEN
  SIMP_TAC arith_ss [CARD_EMPTY, CARD_SING, CARD_INSERT, FINITE_SING,
    FINITE_INSERT, NOT_IN_EMPTY] THEN
  PROVE_TAC[]);

val CARD_FINITE_IMAGE = prove(
  `CARD(UNIV:'a finite_image->bool) = dimindex(:'a)`,
  PROVE_TAC[HAS_SIZE_FINITE_IMAGE, HAS_SIZE]);

val FINITE_FINITE_IMAGE = prove(
  `FINITE(UNIV:'a finite_image->bool)`,
  PROVE_TAC[HAS_SIZE_FINITE_IMAGE, HAS_SIZE]);

val DIMINDEX_NONZERO = prove(
  `~(dimindex(:'a) = 0)`,
  DISCH_TAC THEN
  MP_TAC HAS_SIZE_FINITE_IMAGE THEN
  ASM_REWRITE_TAC[HAS_SIZE_0,UNIV_NOT_EMPTY]);

val DIMINDEX_GE_1 = store_thm("DIMINDEX_GE_1",
  `1 <= dimindex(:'a)`,
  REWRITE_TAC[DECIDE ``1 <= x = ~(x = 0)``, DIMINDEX_NONZERO]);

val DIMINDEX_FINITE_IMAGE = prove(
  `dimindex(:'a finite_image) = dimindex(:'a)`,
  GEN_REWRITE_TAC LAND_CONV empty_rewrites [dimindex] THEN
  MP_TAC HAS_SIZE_FINITE_IMAGE THEN
  SIMP_TAC std_ss [FINITE_FINITE_IMAGE, HAS_SIZE]);

val finite_index = Define`
  finite_index =
    @f:num->'a. !x:'a. ?!n. n < dimindex(:'a) /\ (f n = x)`;

val FINITE_INDEX_WORKS_FINITE = prove(
  `FINITE(UNIV:'n->bool) ==>
   !i:'n. ?!n. n < dimindex(:'n) /\ (finite_index n = i)`,
  DISCH_TAC THEN ASM_REWRITE_TAC[finite_index, dimindex] THEN
  CONV_TAC SELECT_CONV THEN
  SUBGOAL_THEN `(UNIV:'n->bool) HAS_SIZE CARD(UNIV:'n->bool)`
  MP_TAC THENL [PROVE_TAC[HAS_SIZE], ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_SIZE_INDEX) THEN
  ASM_REWRITE_TAC[HAS_SIZE, IN_UNIV]);

val FINITE_INDEX_WORKS = prove
 (`!i:'a finite_image.
        ?!n. n < dimindex(:'a) /\ (finite_index n = i)`,
  MP_TAC(MATCH_MP FINITE_INDEX_WORKS_FINITE FINITE_FINITE_IMAGE) THEN
  PROVE_TAC[DIMINDEX_FINITE_IMAGE]);

val FINITE_INDEX_INJ = prove
 (`!i j. i < dimindex(:'a) /\ j < dimindex(:'a)
         ==> ((finite_index i :'a = finite_index j) = (i = j))`,
  ASM_CASES_TAC `FINITE(UNIV:'a->bool)` THEN ASM_REWRITE_TAC[dimindex] THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP FINITE_INDEX_WORKS_FINITE) THEN
    ASM_REWRITE_TAC[dimindex] THEN PROVE_TAC[],
    PROVE_TAC[DECIDE ``!a. a < 1 = (a = 0)``]]);

val FORALL_FINITE_INDEX = prove
 (`(!k:'n finite_image. P k) =
   (!i. i < dimindex(:'n) ==> P(finite_index i))`,
  PROVE_TAC[FINITE_INDEX_WORKS]);

(* ------------------------------------------------------------------------- *)
(* Hence finite Cartesian products, with indexing and lambdas.               *)
(* ------------------------------------------------------------------------- *)

val cart_tybij = SIMP_RULE std_ss [] (define_new_type_bijections
  {name="cart_tybij", ABS="mk_cart", REP="dest_cart",
   tyax=new_type_definition("cart",
    prove(`?f:'b finite_image->'a. (\f. T) f`,REWRITE_TAC[]))});

val _ = add_infix_type {Prec = 60, ParseName = SOME "**", Name = "cart",
                        Assoc = HOLgrammars.RIGHT};

val fcp_index_def = new_infixl_definition("fcp_index",
  `$fcp_index x i = dest_cart x (finite_index i)`,500);

val _ = set_fixity "'" (Infixl 2000);
val _ = overload_on ("'", Term`$fcp_index`);

(* ----------------------------------------------------------------------
    Establish arrays as an algebraic datatype, with constructor
    mk_cart, even though no user would want to define functions that way.

    When the datatype package handles function-spaces (recursing on
    the right), this will allow the datatype package to define types
    that recurse through arrays.
   ---------------------------------------------------------------------- *)

val fcp_Axiom = store_thm(
  "fcp_Axiom",
  `! f : ('b finite_image -> 'a) -> 'c.
      ?g : 'a['b] -> 'c.
         !h. g (mk_cart h) = f h`,
  STRIP_TAC THEN Q.EXISTS_TAC `f o dest_cart` THEN SRW_TAC [][cart_tybij]);

val fcp_ind = store_thm(
  "fcp_ind",
  `!P. (!f. P (mk_cart f)) ==> !a. P a`,
  SRW_TAC [][] THEN
  Q.SPEC_THEN `a` (SUBST1_TAC o SYM) (CONJUNCT1 cart_tybij) THEN
  SRW_TAC [][]);

val fcp_case_def = new_specification(
  "fcp_case_def", ["fcp_case"],
  SIMP_RULE (srw_ss()) [SKOLEM_THM] fcp_Axiom);

val fcp_tyinfo = TypeBasePure.gen_datatype_info {
  ax = fcp_Axiom,
  ind = fcp_ind,
  case_defs = [fcp_case_def]
};
val _ = TypeBase.write fcp_tyinfo

local (* and here the palaver to make this persistent; this should be easier
         (even without the faff I went through with PP-blocks etc to make it
         look pretty) *)
fun out pps = let
  val S = PP.add_string pps
  val Brk = PP.add_break pps
  val Blk = PP.begin_block pps PP.CONSISTENT
  fun EBlk() = PP.end_block pps
in
  Blk 2; S "val _ = let"; Brk (1,0);
  Blk 2;
  S "val tyi = "; Brk (0,0);
  Blk 2; S "TypeBasePure.gen_datatype_info {"; Brk (0,0);
  S "ax = fcp_Axiom,"; Brk (1,0);
  S "ind = fcp_ind,";  Brk (1,0);
  S "case_defs = [fcp_case_def]"; Brk (1,~2);
  S "}";
  EBlk(); EBlk();
  Brk (1,~2);
  S "in"; Brk(1,0);
  S "TypeBase.write tyi"; Brk(1,~2);
  S "end"; EBlk()
end
in
val _ = adjoin_to_theory {
  sig_ps = NONE,
  struct_ps = SOME out
}
end




val CART_EQ = store_thm("CART_EQ",
  `!(x:'a ** 'b) y.
    (x = y) = (!i. i < dimindex(:'b) ==> (x ' i = y ' i))`,
  REPEAT GEN_TAC THEN SIMP_TAC std_ss [fcp_index_def, GSYM FORALL_FINITE_INDEX]
    THEN REWRITE_TAC[GSYM FUN_EQ_THM, ETA_AX] THEN PROVE_TAC[cart_tybij]);

val FCP = new_binder_definition("FCP",
  ``($FCP) = \g.
     @(f:'a ** 'b). (!i. i < dimindex(:'b) ==> (f ' i = g i))``);

val FCP_BETA = store_thm("FCP_BETA",
  `!i. i < dimindex(:'b)
       ==> (((FCP) g:'a ** 'b) ' i = g i)`,
  SIMP_TAC std_ss [FCP] THEN CONV_TAC SELECT_CONV THEN
  EXISTS_TAC `mk_cart(\k. g(@i. i < dimindex(:'b) /\
                                (finite_index i = k))):'a ** 'b` THEN
  SIMP_TAC std_ss [fcp_index_def, cart_tybij] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  GEN_TAC THEN REWRITE_TAC[] THEN
  PROVE_TAC[FINITE_INDEX_INJ, DIMINDEX_FINITE_IMAGE]);

val FCP_UNIQUE = prove
 (`!(f:'a ** 'b) g.
        (!i. i < dimindex(:'b) ==> (f ' i = g i)) =
        ((FCP) g = f)`,
  SIMP_TAC std_ss [CART_EQ, FCP_BETA] THEN PROVE_TAC[]);

val FCP_ETA = store_thm("FCP_ETA",
  `!g. (FCP i. g ' i) = g`,
  SIMP_TAC std_ss [CART_EQ, FCP_BETA]);

(* ------------------------------------------------------------------------- *)
(* Support for introducing finite index types                                *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Sums (for concatenation)                                                  *)
(* ------------------------------------------------------------------------- *)

val sum_union = prove(
  `UNIV:('a+'b)->bool = ISL UNION ISR`,
  REWRITE_TAC [FUN_EQ_THM,UNIV_DEF,UNION_DEF]
    THEN STRIP_TAC THEN ONCE_REWRITE_TAC [GSYM SPECIFICATION]
    THEN SIMP_TAC std_ss [GSPECIFICATION,IN_DEF,sumTheory.ISL_OR_ISR]);

val inl_inr_bij = prove(
  `BIJ INL (UNIV:'a->bool) (ISL:'a + 'b -> bool) /\
   BIJ INR (UNIV:'b->bool) (ISR:'a + 'b -> bool)`,
  RW_TAC std_ss [UNIV_DEF,BIJ_DEF,INJ_DEF,SURJ_DEF,IN_DEF]
    THEN PROVE_TAC [sumTheory.INL,sumTheory.INR]);

val inl_inr_image = prove(
  `((ISL:'a + 'b -> bool) = IMAGE INL (UNIV:'a->bool)) /\
   ((ISR:'a + 'b -> bool) = IMAGE INR (UNIV:'b->bool))`,
  RW_TAC std_ss [EXTENSION,IMAGE_DEF,IN_UNIV,GSPECIFICATION]
    THEN SIMP_TAC std_ss [IN_DEF] THEN Cases_on `x`
    THEN SIMP_TAC std_ss [sumTheory.ISL,sumTheory.ISR,sumTheory.sum_distinct]);

val isl_isr_finite = prove(
  `(FINITE (ISL:'a + 'b -> bool) = FINITE (UNIV:'a->bool)) /\
   (FINITE (ISR:'a + 'b -> bool) = FINITE (UNIV:'b->bool))`,
  REWRITE_TAC [inl_inr_image] THEN CONJ_TAC
    THEN MATCH_MP_TAC INJECTIVE_IMAGE_FINITE
    THEN REWRITE_TAC [sumTheory.INR_INL_11]);

val isl_isr_univ = prove(
  `(FINITE (UNIV:'a -> bool) ==>
     (CARD (ISL:'a + 'b -> bool) = CARD (UNIV:'a->bool))) /\
   (FINITE (UNIV:'b -> bool) ==>
     (CARD (ISR:'a + 'b -> bool) = CARD (UNIV:'b->bool)))`,
   METIS_TAC [FINITE_BIJ_CARD_EQ,isl_isr_finite,inl_inr_bij]);

val isl_isr_inter = prove(
  `(ISL:'a + 'b -> bool) INTER (ISR:'a + 'b -> bool) = {}`,
  RW_TAC std_ss [INTER_DEF,EXTENSION,NOT_IN_EMPTY,GSPECIFICATION]
    THEN SIMP_TAC std_ss [IN_DEF] THEN Cases_on `x`
    THEN SIMP_TAC std_ss [sumTheory.ISR,sumTheory.ISL]);

val isl_isr_union = prove(
  `FINITE (UNIV:'a -> bool) /\ FINITE (UNIV:'b -> bool) ==>
     (CARD ((ISL:'a + 'b -> bool) UNION (ISR:'a + 'b -> bool)) =
      CARD (ISL:'a + 'b -> bool) + CARD (ISR:'a + 'b -> bool))`,
  METIS_TAC [CARD_UNION,arithmeticTheory.ADD_0,CARD_EMPTY,
    isl_isr_inter,isl_isr_finite]);

(* ......... *)

val index_sum = store_thm("index_sum",
  `dimindex(:('a+'b)) =
   if FINITE (UNIV:'a->bool) /\ FINITE (UNIV:'b->bool) then
     dimindex(:'a) + dimindex(:'b)
   else
     1`,
  RW_TAC std_ss [dimindex,sum_union,isl_isr_union,isl_isr_univ,FINITE_UNION]
    THEN METIS_TAC [isl_isr_finite]);

val finite_sum = store_thm("finite_sum",
  `FINITE (UNIV:('a+'b)->bool) =
   FINITE (UNIV:'a->bool) /\ FINITE (UNIV:'b->bool)`,
  SIMP_TAC std_ss [FINITE_UNION,sum_union,isl_isr_finite]);

(* ------------------------------------------------------------------------- *)
(* 'a sub1, for recursive functions                                          *)
(* ------------------------------------------------------------------------- *)

val EQUAL_def = Define `
  EQUAL = {CHOICE (UNIV:'a -> bool) ; CHOICE (REST (UNIV : 'a -> bool))}`;

val sub_equiv_def = Define `
  sub_equiv a b = a IN EQUAL /\ b IN EQUAL \/ (a = b)`;

val sub_equiv = prove(
  `!a b. sub_equiv a b = (sub_equiv a = sub_equiv b)`,
  RW_TAC arith_ss [sub_equiv_def,FUN_EQ_THM] THEN EQ_TAC THEN
  RW_TAC std_ss [] THEN EQ_TAC THEN RW_TAC arith_ss [] THEN
  DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC);

val sub_equiv_ref = prove(
  `!x y a. sub_equiv a a`,
  REWRITE_TAC [sub_equiv]);

val _ = quotient.define_quotient_type "sub1" "abs_sub1" "rep_sub1" sub_equiv

val QUOTIENT_def = DB.fetch "quotient" "QUOTIENT_def";

val sub1_def =
  REWRITE_RULE [sub_equiv_ref,QUOTIENT_def] (DB.fetch "-" "sub1_QUOTIENT");

val sub1_eq = GSYM (CONJUNCT2 sub1_def);
val abs_rep_sub1 = CONJUNCT1 sub1_def;

(* ......... *)

val parith_ss = arith_ss ++ pred_setSimps.PRED_SET_ss;

val equal_els_diff = prove(
  `~(REST (UNIV :'a -> bool) = {})
   ==> ~(CHOICE (REST (UNIV:'a -> bool)) = CHOICE (UNIV:'a -> bool))`,
  METIS_TAC [EXTENSION,CHOICE_DEF,CHOICE_NOT_IN_REST,UNIV_NOT_EMPTY]);

val eq_not_choice = prove(
  `~(REST (UNIV : 'a -> bool) = {})
   ==> ?x. (abs_sub1 y = abs_sub1 x) /\ ~(x = CHOICE (UNIV:'a -> bool))`,
  REPEAT STRIP_TAC THEN IMP_RES_TAC equal_els_diff THEN
  Cases_on `y = CHOICE UNIV` THEN
  ASM_REWRITE_TAC [
      sub1_eq,sub_equiv_def,EQUAL_def,IN_INSERT,NOT_IN_EMPTY] THENL [
    EXISTS_TAC `CHOICE (REST UNIV)`,EXISTS_TAC `y`] THEN
  RW_TAC std_ss []);

val univ_sub1 = prove(
  `~(REST (UNIV : 'a -> bool) = {})
   ==> (UNIV : 'a sub1 -> bool = IMAGE abs_sub1 (REST UNIV:'a -> bool))`,
  STRIP_TAC THEN
  RW_TAC parith_ss
   [EXTENSION,IMAGE_DEF,IN_UNIV,REST_DEF,DELETE_DEF,DIFF_DEF] THEN
  RW_TAC parith_ss [IN_DEF] THEN
  `?y. x = abs_sub1 y` by Q.EXISTS_TAC `rep_sub1 x` THEN
  RW_TAC arith_ss [eq_not_choice,abs_rep_sub1]);

val bijection_lem1 = prove(
  `~(CHOICE (UNIV:'a -> bool) IN R) ==> BIJ abs_sub1 R (IMAGE abs_sub1 R)`,
  REPEAT STRIP_TAC THEN
  RW_TAC parith_ss
    [BIJ_DEF,SURJ_DEF,INJ_DEF,IMAGE_DEF,EXTENSION,
     sub1_eq,sub_equiv_def,EQUAL_def] THEN
  FULL_SIMP_TAC arith_ss
    [sub1_eq,sub_equiv_def,EQUAL_def,IN_INSERT,NOT_IN_EMPTY] THEN
  METIS_TAC []);

val rest_bijection =
  MATCH_MP bijection_lem1 (SPEC `UNIV` CHOICE_NOT_IN_REST);

val finite_rest = prove(
  `FINITE (REST a) = FINITE a`,
  REWRITE_TAC [REST_DEF,DELETE_DEF] THEN
  METIS_TAC [FINITE_DIFF_down,FINITE_SING,FINITE_DIFF]);

val card_rest = prove(
   `!S. FINITE S ==> ~(S = {}) ==> (CARD (REST S) = PRE (CARD S))`,
   HO_MATCH_MP_TAC FINITE_INDUCT THEN
   RW_TAC arith_ss [REST_DEF,CARD_DEF,CARD_DELETE,FINITE_INSERT,CHOICE_DEF]);

val rest_empty = prove(
  `REST {} = {}`,
  REWRITE_TAC [REST_DEF,EMPTY_DELETE]);

val rest_empty_iff = prove(
  `(REST x = {}) = (x = {}) \/ (?y. x = {y})`,
  METIS_TAC [SING_IFF_EMPTY_REST,SING_DEF,rest_empty]);

val sing_univ = prove(
  `(UNIV = {y}) ==> (!x. x = abs_sub1 y)`,
  REPEAT STRIP_TAC THEN
  METIS_TAC [IN_UNIV,IN_SING,abs_rep_sub1]);

val finite_lem1 = prove(
  `~(REST (UNIV : 'a -> bool) = {})
   ==> (FINITE (UNIV : 'a sub1 -> bool) = FINITE (UNIV : 'a -> bool))`,
  RW_TAC std_ss [univ_sub1] THEN
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM finite_rest))) THEN
  METIS_TAC [FINITE_INJ,IMAGE_FINITE,BIJ_DEF,rest_bijection]);

val finite_lem2 = prove(
  `(REST (UNIV : 'a -> bool) = {})
   ==> (FINITE (UNIV : 'a sub1 -> bool) = FINITE (UNIV : 'a -> bool))`,
  RW_TAC std_ss [rest_empty_iff,UNIV_NOT_EMPTY] THEN
  RW_TAC std_ss [FINITE_SING] THEN
  SUBGOAL_THEN `UNIV = {abs_sub1 y}` ASSUME_TAC THEN
  RW_TAC std_ss [FINITE_SING,EXTENSION,IN_SING,IN_UNIV] THEN
  METIS_TAC [sing_univ]);

val index_lem1 = prove(
  `~(REST (UNIV : 'a -> bool) = {}) /\ FINITE (UNIV : 'a -> bool)
   ==> (dimindex (:'a sub1) = PRE (dimindex (:'a)))`,
  RW_TAC arith_ss [dimindex_def,finite_lem1,univ_sub1,
    GSYM card_rest,UNIV_NOT_EMPTY] THEN
  MATCH_MP_TAC (CONV_RULE (REDEPTH_CONV RIGHT_IMP_FORALL_CONV THENC
    REWRITE_CONV [AND_IMP_INTRO]) (GSYM FINITE_BIJ_CARD_EQ)) THEN
  EXISTS_TAC `abs_sub1` THEN
  RW_TAC std_ss [rest_bijection,finite_rest,GSYM univ_sub1,finite_lem1]);

val index_lem2 = prove(
  `(REST (UNIV :'a -> bool) = {}) ==> (dimindex (:'a sub1) = 1)`,
  RW_TAC std_ss [rest_empty_iff,dimindex_def,FINITE_SING,
    UNIV_NOT_EMPTY] THEN
  SUBGOAL_THEN `UNIV = {abs_sub1 y}` ASSUME_TAC THEN
  RW_TAC std_ss [FINITE_SING,EXTENSION,IN_SING,IN_UNIV,CARD_SING] THEN
  METIS_TAC [sing_univ]);

(* ......... *)

val finite_sub1 =
  save_thm("finite_sub1",
    DISJ_CASES (SPEC `REST UNIV = {}` EXCLUDED_MIDDLE)
        (UNDISCH finite_lem2) (UNDISCH finite_lem1));

val INDEX_SUB1 = store_thm(
  "INDEX_SUB1",
  `dimindex (:'a sub1) = if 1 < dimindex (:'a) then PRE (dimindex (:'a)) else 1`,
  Cases_on `FINITE (UNIV : 'a -> bool)` THENL [
    Cases_on `REST (UNIV : 'a -> bool) = {}` THEN
    RW_TAC arith_ss [index_lem1,index_lem2],
    ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [rest_empty_iff,UNIV_NOT_EMPTY,dimindex_def,finite_sub1] THEN
  REPEAT (POP_ASSUM MP_TAC) THEN
  RW_TAC std_ss [CARD_SING,DECIDE ``~(1 < a) = (a = 0n) \/ (a = 1n)``] THEN
  METIS_TAC [UNIV_NOT_EMPTY,CARD_EQ_0,CARD_EMPTY,SING_IFF_CARD1,SING_DEF]);

(* ------------------------------------------------------------------------- *)
(* bit0                                                                      *)
(* ------------------------------------------------------------------------- *)

val _ = Hol_datatype `bit0 = BIT0A of 'a | BIT0B of 'a`;

val IS_BIT0A_def = Define`
  (IS_BIT0A (BIT0A x) = T) /\ (IS_BIT0A (BIT0B x) = F)`;

val IS_BIT0B_def = Define`
  (IS_BIT0B (BIT0A x) = F) /\ (IS_BIT0B (BIT0B x) = T)`;

val IS_BIT0A_OR_IS_BIT0B = prove(
  `!x. IS_BIT0A x \/ IS_BIT0B x`,
  Cases THEN METIS_TAC [IS_BIT0A_def,IS_BIT0B_def]);

val bit0_union = prove(
  `UNIV:('a bit0)->bool = IS_BIT0A UNION IS_BIT0B`,
  REWRITE_TAC [FUN_EQ_THM,UNIV_DEF,UNION_DEF]
    THEN STRIP_TAC THEN ONCE_REWRITE_TAC [GSYM SPECIFICATION]
    THEN SIMP_TAC std_ss [GSPECIFICATION,IN_DEF,IS_BIT0A_OR_IS_BIT0B]);

val is_bit0a_bij = prove(
  `BIJ BIT0A (UNIV:'a->bool) (IS_BIT0A:'a bit0->bool)`,
  RW_TAC std_ss [UNIV_DEF,BIJ_DEF,INJ_DEF,SURJ_DEF,IN_DEF,IS_BIT0A_def]
    THEN Cases_on `x` THEN FULL_SIMP_TAC std_ss [IS_BIT0A_def,IS_BIT0B_def]
    THEN METIS_TAC []);

val is_bit0b_bij = prove(
  `BIJ BIT0B (UNIV:'a->bool) (IS_BIT0B:'a bit0->bool)`,
  RW_TAC std_ss [UNIV_DEF,BIJ_DEF,INJ_DEF,SURJ_DEF,IN_DEF,IS_BIT0B_def]
    THEN Cases_on `x` THEN FULL_SIMP_TAC std_ss [IS_BIT0A_def,IS_BIT0B_def]
    THEN METIS_TAC []);

val is_bit0a_image = prove(
  `IS_BIT0A = IMAGE BIT0A (UNIV:'a->bool)`,
  RW_TAC std_ss [EXTENSION,IMAGE_DEF,IN_UNIV,GSPECIFICATION]
    THEN SIMP_TAC std_ss [IN_DEF] THEN Cases_on `x`
    THEN SIMP_TAC (srw_ss()) [IS_BIT0A_def,IS_BIT0B_def]);

val is_bit0b_image = prove(
  `IS_BIT0B = IMAGE BIT0B (UNIV:'a->bool)`,
  RW_TAC std_ss [EXTENSION,IMAGE_DEF,IN_UNIV,GSPECIFICATION]
    THEN SIMP_TAC std_ss [IN_DEF] THEN Cases_on `x`
    THEN SIMP_TAC (srw_ss()) [IS_BIT0A_def,IS_BIT0B_def]);

val is_bit0a_finite = prove(
  `FINITE (IS_BIT0A:'a bit0->bool) = FINITE (UNIV:'a->bool)`,
  REWRITE_TAC [is_bit0a_image] THEN MATCH_MP_TAC INJECTIVE_IMAGE_FINITE
    THEN SIMP_TAC (srw_ss()) []);

val is_bit0b_finite = prove(
  `FINITE (IS_BIT0B:'a bit0->bool) = FINITE (UNIV:'a->bool)`,
  REWRITE_TAC [is_bit0b_image] THEN MATCH_MP_TAC INJECTIVE_IMAGE_FINITE
    THEN SIMP_TAC (srw_ss()) []);

val is_bit0a_card = prove(
  `FINITE (UNIV:'a->bool) ==>
     (CARD (IS_BIT0A:'a bit0->bool) = CARD (UNIV:'a->bool))`,
  METIS_TAC [FINITE_BIJ_CARD_EQ,is_bit0a_finite,is_bit0a_bij]);

val is_bit0b_card = prove(
  `FINITE (UNIV:'a->bool) ==>
     (CARD (IS_BIT0B:'a bit0->bool) = CARD (UNIV:'a->bool))`,
  METIS_TAC [FINITE_BIJ_CARD_EQ,is_bit0b_finite,is_bit0b_bij]);

val is_bit0a_is_bit0b_inter = prove(
  `IS_BIT0A INTER IS_BIT0B = {}`,
  RW_TAC std_ss [INTER_DEF,EXTENSION,NOT_IN_EMPTY,GSPECIFICATION]
    THEN Cases_on `x` THEN SIMP_TAC std_ss [IN_DEF,IS_BIT0A_def,IS_BIT0B_def]);

val is_bit0a_is_bit0b_union = prove(
  `FINITE (UNIV:'a -> bool) ==>
     (CARD ((IS_BIT0A:'a bit0 -> bool) UNION (IS_BIT0B:'a bit0 -> bool)) =
      CARD (IS_BIT0A:'a bit0 -> bool) + CARD (IS_BIT0B:'a bit0 -> bool))`,
  STRIP_TAC
    THEN IMP_RES_TAC (GSYM is_bit0a_finite)
    THEN IMP_RES_TAC (GSYM is_bit0b_finite)
    THEN IMP_RES_TAC CARD_UNION
    THEN FULL_SIMP_TAC std_ss [is_bit0a_is_bit0b_inter,CARD_EMPTY]);

(* ......... *)

val index_bit0 = store_thm("index_bit0",
  `dimindex(:('a bit0)) =
     if FINITE (UNIV:'a->bool) then 2 * dimindex(:'a) else 1`,
  RW_TAC std_ss [dimindex,bit0_union,is_bit0a_is_bit0b_union,FINITE_UNION]
    THEN METIS_TAC [is_bit0a_finite,is_bit0a_card,
                    is_bit0b_finite,is_bit0b_card,arithmeticTheory.TIMES2]);


val finite_bit0 = store_thm("finite_bit0",
  `FINITE (UNIV:'a bit0->bool) = FINITE (UNIV:'a->bool)`,
  SIMP_TAC std_ss [FINITE_UNION,is_bit0a_finite,is_bit0b_finite,bit0_union]);

(* ------------------------------------------------------------------------- *)
(* bit1                                                                      *)
(* ------------------------------------------------------------------------- *)

val _ = Hol_datatype `bit1 = BIT1A of 'a | BIT1B of 'a | BIT1C`;

val IS_BIT1A_def = Define`
  (IS_BIT1A (BIT1A x) = T) /\ (IS_BIT1A (BIT1B x) = F) /\
  (IS_BIT1A (BIT1C) = F)`;

val IS_BIT1B_def = Define`
  (IS_BIT1B (BIT1A x) = F) /\ (IS_BIT1B (BIT1B x) = T) /\
  (IS_BIT1B (BIT1C) = F)`;

val IS_BIT1C_def = Define`
  (IS_BIT1C (BIT1A x) = F) /\ (IS_BIT1C (BIT1B x) = F) /\
  (IS_BIT1C (BIT1C) = T)`;

val IS_BIT1A_OR_IS_BIT1B_OR_IS_BIT1C = prove(
  `!x. IS_BIT1A x \/ IS_BIT1B x \/ IS_BIT1C x`,
  Cases THEN METIS_TAC [IS_BIT1A_def,IS_BIT1B_def,IS_BIT1C_def]);

val bit1_union = prove(
  `UNIV:('a bit1)->bool = IS_BIT1A UNION IS_BIT1B UNION IS_BIT1C`,
  REWRITE_TAC [FUN_EQ_THM,UNIV_DEF,UNION_DEF]
    THEN STRIP_TAC THEN ONCE_REWRITE_TAC [GSYM SPECIFICATION]
    THEN SIMP_TAC std_ss [GSPECIFICATION,IN_DEF]
    THEN METIS_TAC [IS_BIT1A_OR_IS_BIT1B_OR_IS_BIT1C]);

val is_bit1a_bij = prove(
  `BIJ BIT1A (UNIV:'a->bool) (IS_BIT1A:'a bit1->bool)`,
  RW_TAC std_ss [UNIV_DEF,BIJ_DEF,INJ_DEF,SURJ_DEF,IN_DEF,IS_BIT1A_def]
    THEN Cases_on `x`
    THEN FULL_SIMP_TAC std_ss [IS_BIT1A_def,IS_BIT1B_def,IS_BIT1C_def]
    THEN METIS_TAC []);

val is_bit1b_bij = prove(
  `BIJ BIT1B (UNIV:'a->bool) (IS_BIT1B:'a bit1->bool)`,
  RW_TAC std_ss [UNIV_DEF,BIJ_DEF,INJ_DEF,SURJ_DEF,IN_DEF,IS_BIT1B_def]
    THEN Cases_on `x`
    THEN FULL_SIMP_TAC std_ss [IS_BIT1A_def,IS_BIT1B_def,IS_BIT1C_def]
    THEN METIS_TAC []);

val is_bit1a_image = prove(
  `IS_BIT1A = IMAGE BIT1A (UNIV:'a->bool)`,
  RW_TAC std_ss [EXTENSION,IMAGE_DEF,IN_UNIV,GSPECIFICATION]
    THEN SIMP_TAC std_ss [IN_DEF] THEN Cases_on `x`
    THEN SIMP_TAC (srw_ss()) [IS_BIT1A_def,IS_BIT1B_def,IS_BIT1C_def]);

val is_bit1b_image = prove(
  `IS_BIT1B = IMAGE BIT1B (UNIV:'a->bool)`,
  RW_TAC std_ss [EXTENSION,IMAGE_DEF,IN_UNIV,GSPECIFICATION]
    THEN SIMP_TAC std_ss [IN_DEF] THEN Cases_on `x`
    THEN SIMP_TAC (srw_ss()) [IS_BIT1A_def,IS_BIT1B_def,IS_BIT1C_def]);

val is_bit1a_finite = prove(
  `FINITE (IS_BIT1A:'a bit1->bool) = FINITE (UNIV:'a->bool)`,
  REWRITE_TAC [is_bit1a_image] THEN MATCH_MP_TAC INJECTIVE_IMAGE_FINITE
    THEN SIMP_TAC (srw_ss()) []);

val is_bit1b_finite = prove(
  `FINITE (IS_BIT1B:'a bit1->bool) = FINITE (UNIV:'a->bool)`,
  REWRITE_TAC [is_bit1b_image] THEN MATCH_MP_TAC INJECTIVE_IMAGE_FINITE
    THEN SIMP_TAC (srw_ss()) []);

val is_bit1a_card = prove(
  `FINITE (UNIV:'a->bool) ==>
     (CARD (IS_BIT1A:'a bit1->bool) = CARD (UNIV:'a->bool))`,
  METIS_TAC [FINITE_BIJ_CARD_EQ,is_bit1a_finite,is_bit1a_bij]);

val is_bit1b_card = prove(
  `FINITE (UNIV:'a->bool) ==>
     (CARD (IS_BIT1B:'a bit1->bool) = CARD (UNIV:'a->bool))`,
  METIS_TAC [FINITE_BIJ_CARD_EQ,is_bit1b_finite,is_bit1b_bij]);

val is_bit1a_is_bit1b_inter = prove(
  `IS_BIT1A INTER IS_BIT1B = {}`,
  RW_TAC std_ss [INTER_DEF,EXTENSION,NOT_IN_EMPTY,GSPECIFICATION]
    THEN Cases_on `x`
    THEN SIMP_TAC std_ss [IN_DEF,IS_BIT1A_def,IS_BIT1B_def,IS_BIT1C_def]);

val IS_BIT1C_EQ_BIT1C = prove(
  `!x. IS_BIT1C x = (x = BIT1C)`,
  Cases THEN SIMP_TAC (srw_ss()) [IS_BIT1C_def]);

val is_bit1c_sing = prove(
  `SING IS_BIT1C`,
  REWRITE_TAC [SING_DEF] THEN EXISTS_TAC `BIT1C`
    THEN SIMP_TAC std_ss[FUN_EQ_THM,IS_BIT1C_EQ_BIT1C]
    THEN METIS_TAC [IN_SING,SPECIFICATION]);

val is_bit1c_finite_card = REWRITE_RULE [SING_IFF_CARD1] is_bit1c_sing;

val bit1_union_inter = prove(
  `(IS_BIT1A UNION IS_BIT1B) INTER IS_BIT1C = {}`,
  RW_TAC std_ss [INTER_DEF,EXTENSION,NOT_IN_EMPTY,GSPECIFICATION,IN_UNION]
    THEN Cases_on `x`
    THEN SIMP_TAC std_ss [IN_DEF,IS_BIT1A_def,IS_BIT1B_def,IS_BIT1C_def]);

val is_bit1a_is_bit1b_is_bit1c_union = prove(
  `FINITE (UNIV:'a -> bool) ==>
     (CARD ((IS_BIT1A:'a bit1 -> bool) UNION (IS_BIT1B:'a bit1 -> bool) UNION
            (IS_BIT1C:'a bit1 -> bool)) =
      CARD (IS_BIT1A:'a bit1 -> bool) + CARD (IS_BIT1B:'a bit1 -> bool) + 1)`,
  STRIP_TAC
    THEN `FINITE (IS_BIT1A UNION IS_BIT1B)`
      by METIS_TAC [is_bit1a_finite,is_bit1b_finite,FINITE_UNION]
    THEN STRIP_ASSUME_TAC is_bit1c_finite_card
    THEN IMP_RES_TAC CARD_UNION
    THEN FULL_SIMP_TAC std_ss [bit1_union_inter,CARD_EMPTY]
    THEN NTAC 8 (POP_ASSUM (K ALL_TAC))
    THEN IMP_RES_TAC (GSYM is_bit1a_finite)
    THEN IMP_RES_TAC (GSYM is_bit1b_finite)
    THEN IMP_RES_TAC CARD_UNION
    THEN FULL_SIMP_TAC std_ss [is_bit1a_is_bit1b_inter,CARD_EMPTY]);

(* ......... *)

val index_bit1 = store_thm("index_bit1",
  `dimindex(:('a bit1)) =
     if FINITE (UNIV:'a->bool) then 2 * dimindex(:'a) + 1 else 1`,
  RW_TAC std_ss
         [dimindex,bit1_union,is_bit1a_is_bit1b_is_bit1c_union,FINITE_UNION]
    THEN METIS_TAC [is_bit1a_finite,is_bit1a_card,is_bit1c_finite_card,
                    is_bit1b_finite,is_bit1b_card,arithmeticTheory.TIMES2]);


val finite_bit1 = store_thm("finite_bit1",
  `FINITE (UNIV:'a bit1->bool) = FINITE (UNIV:'a->bool)`,
  SIMP_TAC std_ss [FINITE_UNION,
    is_bit1a_finite,is_bit1b_finite,is_bit1c_finite_card,bit1_union]);

(* ------------------------------------------------------------------------ *)
(* one                                                                      *)
(* ------------------------------------------------------------------------ *)

val one_sing = prove(
  `SING (UNIV:one->bool)`,
  REWRITE_TAC [SING_DEF] THEN EXISTS_TAC `()`
    THEN SIMP_TAC std_ss [FUN_EQ_THM] THEN Cases
    THEN METIS_TAC [IN_SING,IN_UNIV,SPECIFICATION]);

val one_finite_card = REWRITE_RULE [SING_IFF_CARD1] one_sing;

(* ......... *)

val index_one = store_thm("index_one",
  `dimindex(:one) = 1`, METIS_TAC [dimindex_def,one_finite_card]);

val finite_one = save_thm("finite_one", CONJUNCT2 one_finite_card);

(* ------------------------------------------------------------------------ *)

val card_dimindex = save_thm("card_dimindex",
  METIS_PROVE [dimindex_def]
   ``FINITE (UNIV:'a->bool) ==> (CARD (UNIV:'a->bool) = dimindex(:'a))``);

(* ------------------------------------------------------------------------ *)

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val FCP_ss = rewrites [FCP_BETA,FCP_ETA,CART_EQ];

val _ = set_fixity ":+"  (Infixl 325);

val _ = computeLib.auto_import_definitions := false;

val FCP_UPDATE_def = xDefine "FCP_UPDATE"
  `$:+ a b = \m:'a ** 'b. (FCP c. if a = c then b else m ' c):'a ** 'b`;

val FCP_UPDATE_COMMUTES = store_thm ("FCP_UPDATE_COMMUTES",
  `!m a b c d.  ~(a = b) ==>
     ((a :+ c) ((b :+ d) m) = (b :+ d) ((a :+ c) m))`,
  REPEAT STRIP_TAC \\ REWRITE_TAC [FUN_EQ_THM]
    \\ SRW_TAC [FCP_ss] [FCP_UPDATE_def] \\ RW_TAC std_ss []);

val FCP_UPDATE_EQ = store_thm("FCP_UPDATE_EQ",
  `!m a b c. (a :+ c) ((a :+ b) m) = (a :+ c) m`,
  REPEAT STRIP_TAC \\ REWRITE_TAC [FUN_EQ_THM]
    \\ SRW_TAC [FCP_ss] [FCP_UPDATE_def]);

val FCP_UPDATE_IMP_ID = store_thm("FCP_UPDATE_IMP_ID",
  `!m a v. (m ' a = v) ==> ((a :+ v) m = m)`,
  SRW_TAC [FCP_ss] [FCP_UPDATE_def] \\ RW_TAC std_ss []);

val APPLY_FCP_UPDATE_ID = store_thm("APPLY_FCP_UPDATE_ID",
  `!m a. (a :+ (m ' a)) m = m`, SRW_TAC [FCP_ss] [FCP_UPDATE_def]);

val FCP_APPLY_UPDATE_THM = store_thm("FCP_APPLY_UPDATE_THM",
  `!(m:'a ** 'b) a w b. ((a :+ w) m) ' b =
       if b < dimindex(:'b) then
         if a = b then w else m ' b
       else
         FAIL (fcp_index) ^(mk_var("index out of range", bool)) ((a :+ w) m) b`,
  SRW_TAC [FCP_ss] [FCP_UPDATE_def, combinTheory.FAIL_THM]);

(* ------------------------------------------------------------------------ *)

open listTheory;

val FCP_TL_def = Define `
  FCP_TL v = (FCP i. v ' (SUC i))`;
val FCP_HD_def = Define `
  FCP_HD v = v ' 0`;
val FCP_CONS_def = Define `
  FCP_CONS h (v:'a ** 'b) = (0 :+ h) (FCP i. v ' (PRE i))`;

val FCP_MAP_def = Define `
  FCP_MAP f (v:'a ** 'c) = (FCP i. f (v ' i)):'b ** 'c`;
val FCP_EXISTS_def = Define `
  FCP_EXISTS P (v:'b ** 'a) = ?i. i < dimindex (:'a) /\ P (v ' i)`;
val FCP_EVERY_def = Define `
  FCP_EVERY P (v:'b ** 'a) = !i. dimindex (:'a) <= i \/ P (v ' i)`;

val V2L_def = Define `
  V2L (v:'a ** 'b) =
    @L. (LENGTH L = dimindex (:'b)) /\
        !i. i < dimindex (:'b) ==> (EL i L = (v:'a ** 'b) ' i)`;
val L2V_def = Define `
  L2V L = FCP i. EL i L`;

(* ......... *)

val exists_v2l_lem = prove(
  `!n. n <= dimindex (:'b)
   ==> ?x. (LENGTH x = n) /\ !i. i < n ==> (EL i x = (v:'a ** 'b) ' i)`,
  Induct THEN RW_TAC arith_ss [] THEN FULL_SIMP_TAC arith_ss [] THENL [
    Q.EXISTS_TAC `[]`,
    Q.EXISTS_TAC `x ++ [v ' n]`] THEN
  REWRITE_TAC [LENGTH,LENGTH_APPEND] THEN
  CONJ_TAC THEN REPEAT STRIP_TAC THEN1 DECIDE_TAC THEN
  `i < n \/ (i = n)` by DECIDE_TAC THEN
  RW_TAC arith_ss [
    rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2,EL,HD]);

val exists_v2l_thm =
  save_thm("exists_v2l_thm",
  SIMP_RULE arith_ss [] (SPEC `dimindex (:'b)` exists_v2l_lem));

val ELIM_V2L_TAC =
  REWRITE_TAC [V2L_def] THEN SELECT_ELIM_TAC THEN
  CONJ_TAC THEN1 MATCH_ACCEPT_TAC exists_v2l_thm;

(* ......... *)

val el_tl = prove(
  `!x. 0 < LENGTH x ==> (EL i (TL x) = EL (SUC i) x)`,
  Induct THEN RW_TAC arith_ss [LENGTH,EL,TL]);

val exists_el_thm = prove(
  `!x. EXISTS P x = ?i. i < LENGTH x /\ P (EL i x)`,
  Induct THEN RW_TAC arith_ss [EXISTS_DEF,LENGTH] THEN
  EQ_TAC THEN RW_TAC arith_ss [] THENL [
    Q.EXISTS_TAC `0`,
    Q.EXISTS_TAC `SUC i`,
    Cases_on `i`] THEN
  FULL_SIMP_TAC arith_ss [EL,HD,TL] THEN
  DISJ2_TAC THEN Q.EXISTS_TAC `n` THEN ASM_REWRITE_TAC []);

val every_el_thm = prove(
  `!x. EVERY P x = !i. LENGTH x <= i \/ P (EL i x)`,
  Induct THEN RW_TAC arith_ss [EVERY_DEF,EXISTS_DEF,LENGTH] THEN
  EQ_TAC THEN RW_TAC arith_ss [] THENL [
    Cases_on `i`,
    POP_ASSUM (STRIP_ASSUME_TAC o SPEC `0`),
    POP_ASSUM (STRIP_ASSUME_TAC o SPEC `SUC i`)] THEN
  FULL_SIMP_TAC arith_ss [EL,HD,TL]);

val length_tl_thm = prove(
  `LENGTH (TL (V2L (v :'a ** 'b)) :'a list) = PRE (dimindex (:'b))`,
  ELIM_V2L_TAC THEN RW_TAC arith_ss [] THEN
  Cases_on `x` THEN FULL_SIMP_TAC arith_ss [LENGTH,DIMINDEX_NONZERO,TL]);

(* ......... *)

val LENGTH_V2L = store_thm(
  "LENGTH_V2L",
  `LENGTH (V2L (v:'a ** 'b)) = dimindex (:'b)`,
  ELIM_V2L_TAC THEN RW_TAC arith_ss []);

val EL_V2L = store_thm(
  "EL_V2L",
  `i < dimindex (:'b) ==> (EL i (V2L v) = (v:'a ** 'b)  ' i)`,
  ELIM_V2L_TAC THEN RW_TAC arith_ss []);

val FCP_MAP = store_thm(
  "FCP_MAP",
  `FCP_MAP f v = L2V (MAP f (V2L v))`,
  ELIM_V2L_TAC THEN RW_TAC arith_ss [FCP_MAP_def,L2V_def,FCP_BETA,CART_EQ,
    rich_listTheory.EL_MAP]);

val FCP_TL = store_thm(
  "FCP_TL",
  `1 < dimindex (:'b) ==> (FCP_TL (v:'a ** 'b) = L2V (TL (V2L v)):'a ** 'b sub1)`,
  ELIM_V2L_TAC THEN
  RW_TAC arith_ss [FCP_TL_def,L2V_def,el_tl,FCP_BETA,CART_EQ,INDEX_SUB1,GSYM LENGTH_V2L]);

val FCP_EXISTS = store_thm(
  "FCP_EXISTS",
  `FCP_EXISTS P v = EXISTS P (V2L v)`,
  ELIM_V2L_TAC THEN RW_TAC arith_ss [exists_el_thm,FCP_EXISTS_def] THEN PROVE_TAC []);

val FCP_EVERY = store_thm(
  "FCP_EVERY",
  `FCP_EVERY P v = EVERY P (V2L v)`,
  ELIM_V2L_TAC THEN RW_TAC arith_ss [every_el_thm,FCP_EVERY_def] THEN
  PROVE_TAC [arithmeticTheory.NOT_LESS_EQUAL]);

val FCP_HD = store_thm(
  "FCP_HD",
  `FCP_HD v = HD (V2L v)`,
  ELIM_V2L_TAC THEN Cases_on `x` THEN
  RW_TAC arith_ss [LENGTH,DIMINDEX_NONZERO,HD,EL,FCP_HD_def] THEN
  POP_ASSUM (STRIP_ASSUME_TAC o SPEC `0`) THEN FULL_SIMP_TAC arith_ss [EL,HD]);

val FCP_CONS = store_thm(
  "FCP_CONS",
  `FCP_CONS a (v:'a ** 'b) = L2V (a::V2L v):'a ** 'b + 1`,
  ELIM_V2L_TAC THEN
  RW_TAC arith_ss [FCP_CONS_def,CART_EQ,FCP_UPDATE_def,FCP_BETA,L2V_def] THEN
  POP_ASSUM MP_TAC THEN Cases_on `i` THEN
  RW_TAC arith_ss [EL,HD,TL,index_sum,index_one]);

val V2L_L2V = store_thm("V2L_L2V",
  `!x. (dimindex (:'b) = LENGTH x) ==> (V2L (L2V x:'a ** 'b) = x)`,
  RW_TAC arith_ss [L2V_def] THEN ELIM_V2L_TAC THEN
  RW_TAC arith_ss [FCP_BETA,listTheory.LIST_EQ]);

val NULL_V2L = store_thm("NULL_V2L",`~NULL (V2L v)`,
  ELIM_V2L_TAC THEN Cases THEN
  RW_TAC arith_ss [NULL,LENGTH,DIMINDEX_NONZERO]);

val V2L_RECURSIVE = store_thm(
  "V2L_RECURSIVE",
  `V2L (v:'a ** 'b) = (FCP_HD v) ::
       (if dimindex (:'b) = 1 then [] else V2L (FCP_TL v:'a ** 'b sub1))`,
  RW_TAC arith_ss [FCP_HD] THENL [
    ELIM_V2L_TAC THEN Cases THEN RW_TAC arith_ss [LENGTH,EL,HD] THEN
    Cases_on `t` THEN FULL_SIMP_TAC arith_ss [LENGTH],
    `1 < dimindex (:'b)` by RW_TAC arith_ss [DIMINDEX_NONZERO,
        DECIDE ``1 < a = ~(a = 0n) /\ ~(a = 1n)``]] THEN
  RW_TAC arith_ss [FCP_TL,V2L_L2V,CONS,NULL_V2L,length_tl_thm,INDEX_SUB1]);

val READ_TL = store_thm(
  "READ_TL",
  `i < dimindex (:'b) ==> (((FCP_TL a):'a ** 'b) ' i = (a:'a ** 'c) ' (SUC i))`,
  RW_TAC arith_ss [FCP_TL_def,FCP_BETA]);

val READ_L2V = store_thm(
  "READ_L2V",
  `i < dimindex (:'b) ==> ((L2V a:'a ** 'b) ' i = EL i a)`,
  RW_TAC arith_ss [L2V_def,FCP_BETA]);

val index_comp = Q.store_thm("index_comp",
  `!f n. (($FCP f):'a ** 'b) ' n =
      if n < dimindex (:'b) then
        f n
      else
        FAIL $' ^(mk_var("FCP out of bounds",bool))
             (($FCP f):'a ** 'b) n`,
  SRW_TAC [FCP_ss] [combinTheory.FAIL_THM]);

val fcp_subst_comp = Q.store_thm("fcp_subst_comp",
  `!a b f. (x :+ y) ($FCP f):'a ** 'b =
         ($FCP (\c. if x = c then y else f c)):'a ** 'b`,
  SRW_TAC [FCP_ss] [FCP_UPDATE_def]);

val _ = export_theory();
