(* ========================================================================= *)
(* FILE          : fcpScript.sml                                             *)
(* DESCRIPTION   : A port, from HOL light, of John Harrison's treatment of   *)
(*                 finite Cartesian products (TPHOLs 2005)                   *)
(* DATE          : 2005                                                      *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;
open lcsymtacs pred_setTheory listTheory

val () = new_theory "fcp";

(* ------------------------------------------------------------------------- *)

infix \\
val op \\ = op THEN;

val qDefine = Feedback.trace ("Define.storage_message", 0) zDefine

val CARD_CLAUSES =
   CONJ CARD_EMPTY
     (PROVE [CARD_INSERT]
        ``!x s.
             FINITE s ==>
             (CARD (x INSERT s) = (if x IN s then CARD s else SUC (CARD s)))``)

val IMAGE_CLAUSES = CONJ IMAGE_EMPTY IMAGE_INSERT
val FINITE_RULES = CONJ FINITE_EMPTY FINITE_INSERT
val NOT_SUC = numTheory.NOT_SUC
val SUC_INJ = prim_recTheory.INV_SUC_EQ
val LT = CONJ (DECIDE ``!m. ~(m < 0)``) prim_recTheory.LESS_THM
val LT_REFL = prim_recTheory.LESS_REFL

(* ------------------------------------------------------------------------- *)

val () = Parse.set_fixity "HAS_SIZE" (Infix (NONASSOC, 450))

val HAS_SIZE = Define `(s HAS_SIZE n) = FINITE s /\ (CARD s = n)`

val CARD_IMAGE_INJ = Q.prove(
   `!(f:'a->'b) s.
       (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) /\
       FINITE s ==> (CARD (IMAGE f s) = CARD s)`,
   GEN_TAC
   THEN REWRITE_TAC [DECIDE ``a /\ b ==> c = b ==> a ==> c``]
   THEN Q.SPEC_THEN
           `\s. (!x y. (f x = f y) ==> y IN s ==> x IN s ==> (x = y)) ==>
                (CARD (IMAGE f s) = CARD s)`
           (MATCH_MP_TAC o BETA_RULE) FINITE_INDUCT
   THEN REWRITE_TAC [NOT_IN_EMPTY, IMAGE_CLAUSES]
   THEN REPEAT STRIP_TAC
   THEN ASM_SIMP_TAC std_ss [CARD_CLAUSES, IMAGE_FINITE, IN_IMAGE]
   THEN COND_CASES_TAC
   THEN PROVE_TAC [IN_INSERT]
   )

val HAS_SIZE_IMAGE_INJ = Q.prove(
   `!(f:'a->'b) s n.
        (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) /\
        (s HAS_SIZE n) ==> ((IMAGE f s) HAS_SIZE n)`,
   SIMP_TAC std_ss [HAS_SIZE, IMAGE_FINITE] THEN PROVE_TAC[CARD_IMAGE_INJ])

val HAS_SIZE_0 = Q.prove(
   `!(s:'a->bool) n. (s HAS_SIZE 0) = (s = {})`,
   REPEAT GEN_TAC
   THEN REWRITE_TAC [HAS_SIZE]
   THEN EQ_TAC
   THEN DISCH_TAC
   THEN ASM_REWRITE_TAC [FINITE_RULES, CARD_CLAUSES]
   THEN FIRST_ASSUM (MP_TAC o CONJUNCT2)
   THEN FIRST_ASSUM (MP_TAC o CONJUNCT1)
   THEN Q.SPEC_TAC (`s:'a->bool`,`s:'a->bool`)
   THEN Q.SPEC_THEN `\s. (CARD s = 0) ==> (s = {})`
                    (MATCH_MP_TAC o BETA_RULE) FINITE_INDUCT
   THEN REWRITE_TAC [NOT_INSERT_EMPTY]
   THEN REPEAT GEN_TAC
   THEN STRIP_TAC
   THEN ASM_SIMP_TAC arith_ss [CARD_INSERT]
   )

val HAS_SIZE_SUC = Q.prove(
   `!(s:'a->bool) n.
        (s HAS_SIZE (SUC n)) =
        ~(s = {}) /\ !a. a IN s ==> ((s DELETE a) HAS_SIZE n)`,
   REPEAT GEN_TAC
   THEN REWRITE_TAC [HAS_SIZE]
   THEN Q.ASM_CASES_TAC `s:'a->bool = {}`
   THEN ASM_REWRITE_TAC [CARD_CLAUSES, FINITE_RULES, NOT_IN_EMPTY, GSYM NOT_SUC]
   THEN REWRITE_TAC [FINITE_DELETE]
   THEN Q.ASM_CASES_TAC `FINITE(s:'a->bool)`
   THEN ASM_SIMP_TAC std_ss [NOT_FORALL_THM, MEMBER_NOT_EMPTY]
   THEN EQ_TAC
   THEN REPEAT STRIP_TAC
   THENL [
      MP_TAC (Q.ISPECL [`a:'a`, `s DELETE a:'a`] (CONJUNCT2 CARD_CLAUSES))
      THEN ASM_REWRITE_TAC [FINITE_DELETE, IN_DELETE]
      THEN Q.SUBGOAL_THEN `a INSERT (s DELETE a:'a) = s` SUBST1_TAC
      THENL [
         Q.UNDISCH_TAC `a:'a IN s`
         THEN PROVE_TAC [INSERT_DELETE],
         ASM_REWRITE_TAC [SUC_INJ]
         THEN PROVE_TAC []
      ],
      FIRST_ASSUM
         (MP_TAC o GEN_REWRITE_RULE I empty_rewrites [GSYM MEMBER_NOT_EMPTY])
      THEN DISCH_THEN (Q.X_CHOOSE_TAC `a:'a`)
      THEN MP_TAC (Q.ISPECL [`a:'a`, `s DELETE a:'a`] (CONJUNCT2 CARD_CLAUSES))
      THEN ASM_REWRITE_TAC [FINITE_DELETE, IN_DELETE]
      THEN Q.SUBGOAL_THEN `a INSERT (s DELETE a:'a) = s` SUBST1_TAC
      THENL [
         Q.UNDISCH_TAC `a:'a IN s` THEN PROVE_TAC[INSERT_DELETE],
         PROVE_TAC[]
      ]
   ])

val HAS_SIZE_INDEX = Q.prove(
   `!s n.
      (s HAS_SIZE n) ==>
      ?f:num->'a. (!m. m < n ==> f(m) IN s) /\
                  (!x. x IN s ==> ?!m. m < n /\ (f m = x))`,
   CONV_TAC SWAP_VARS_CONV
   THEN numLib.INDUCT_TAC
   THEN SIMP_TAC std_ss [HAS_SIZE_0, HAS_SIZE_SUC, LT, NOT_IN_EMPTY]
   THEN Q.X_GEN_TAC `s:'a->bool`
   THEN REWRITE_TAC [EXTENSION, NOT_IN_EMPTY]
   THEN SIMP_TAC std_ss [NOT_FORALL_THM]
   THEN DISCH_THEN
           (CONJUNCTS_THEN2 (Q.X_CHOOSE_TAC `a:'a`) (MP_TAC o Q.SPEC `a:'a`))
   THEN ASM_REWRITE_TAC[]
   THEN DISCH_TAC
   THEN FIRST_X_ASSUM (MP_TAC o Q.SPEC `s DELETE (a:'a)`)
   THEN ASM_REWRITE_TAC []
   THEN DISCH_THEN (Q.X_CHOOSE_THEN `f:num->'a` STRIP_ASSUME_TAC)
   THEN Q.EXISTS_TAC `\m:num. if m < n then f(m) else a:'a`
   THEN CONJ_TAC
   THENL [
      GEN_TAC
      THEN REWRITE_TAC []
      THEN BETA_TAC
      THEN COND_CASES_TAC
      THEN PROVE_TAC [IN_DELETE],
      ALL_TAC
   ]
   THEN Q.X_GEN_TAC `x:'a`
   THEN DISCH_TAC
   THEN ASM_REWRITE_TAC []
   THEN FIRST_X_ASSUM (MP_TAC o Q.SPEC `x:'a`)
   THEN ASM_SIMP_TAC (std_ss++boolSimps.COND_elim_ss) [IN_DELETE]
   THEN Q.ASM_CASES_TAC `a:'a = x`
   THEN ASM_SIMP_TAC std_ss []
   THEN PROVE_TAC [LT_REFL, IN_DELETE]
   )

(* ------------------------------------------------------------------------- *
 * An isomorphic image of any finite type, 1-element for infinite ones.      *
 * ------------------------------------------------------------------------- *)

val finite_image_tybij =
   BETA_RULE
     (define_new_type_bijections
        {name = "finite_image_tybij",
         ABS  = "mk_finite_image",
         REP  = "dest_finite_image",
         tyax = new_type_definition ("finite_image",
                   PROVE []
                      ``?x:'a. (\x. (x = ARB) \/ FINITE (UNIV:'a->bool)) x``)})

val FINITE_IMAGE_IMAGE = Q.prove(
   `UNIV:'a finite_image->bool =
    IMAGE mk_finite_image
      (if FINITE(UNIV:'a->bool) then UNIV:'a->bool else {ARB})`,
   MP_TAC finite_image_tybij
   THEN COND_CASES_TAC
   THEN ASM_REWRITE_TAC []
   THEN REWRITE_TAC [EXTENSION, IN_IMAGE, IN_SING, IN_UNIV]
   THEN PROVE_TAC []
   )

(* ------------------------------------------------------------------------- *
 * Dimension of such a type, and indexing over it.                           *
 * ------------------------------------------------------------------------- *)

val dimindex_def = zDefine`
   dimindex(:'a) = if FINITE (UNIV:'a->bool) then CARD (UNIV:'a->bool) else 1`

val NOT_FINITE_IMP_dimindex_1 = Q.store_thm("NOT_FINITE_IMP_dimindex_1",
   `~FINITE univ(:'a) ==> (dimindex(:'a) = 1)`,
   METIS_TAC [dimindex_def]
   )

val HAS_SIZE_FINITE_IMAGE = Q.prove(
   `(UNIV:'a finite_image->bool) HAS_SIZE dimindex(:'a)`,
   REWRITE_TAC [dimindex_def, FINITE_IMAGE_IMAGE]
   THEN MP_TAC finite_image_tybij
   THEN COND_CASES_TAC
   THEN ASM_REWRITE_TAC []
   THEN STRIP_TAC
   THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ
   THEN ASM_REWRITE_TAC [HAS_SIZE, IN_UNIV, IN_SING]
   THEN SIMP_TAC arith_ss [CARD_EMPTY, CARD_SING, CARD_INSERT, FINITE_SING,
                           FINITE_INSERT, NOT_IN_EMPTY]
   THEN PROVE_TAC[]
   )

val CARD_FINITE_IMAGE =
   PROVE [HAS_SIZE_FINITE_IMAGE, HAS_SIZE]
      ``CARD (UNIV:'a finite_image->bool) = dimindex(:'a)``

val FINITE_FINITE_IMAGE =
   PROVE [HAS_SIZE_FINITE_IMAGE, HAS_SIZE]
      ``FINITE (UNIV:'a finite_image->bool)``

val DIMINDEX_NONZERO =
   METIS_PROVE [HAS_SIZE_0, UNIV_NOT_EMPTY, HAS_SIZE_FINITE_IMAGE]
      ``~(dimindex(:'a) = 0)``

val DIMINDEX_GE_1 = Q.store_thm("DIMINDEX_GE_1",
   `1 <= dimindex(:'a)`,
   REWRITE_TAC [DECIDE ``1 <= x = ~(x = 0)``, DIMINDEX_NONZERO]
   )

val DIMINDEX_GT_0 =
   REWRITE_RULE [arithmeticTheory.NOT_ZERO_LT_ZERO] DIMINDEX_NONZERO

val DIMINDEX_FINITE_IMAGE = Q.prove(
   `dimindex(:'a finite_image) = dimindex(:'a)`,
   GEN_REWRITE_TAC LAND_CONV empty_rewrites [dimindex_def]
   THEN MP_TAC HAS_SIZE_FINITE_IMAGE
   THEN SIMP_TAC std_ss [FINITE_FINITE_IMAGE, HAS_SIZE]
   )

val finite_index = zDefine`
   finite_index = @f:num->'a. !x:'a. ?!n. n < dimindex(:'a) /\ (f n = x)`

val FINITE_INDEX_WORKS_FINITE = Q.prove(
   `FINITE (UNIV:'n->bool) ==>
    !i:'n. ?!n. n < dimindex(:'n) /\ (finite_index n = i)`,
   DISCH_TAC
   THEN ASM_REWRITE_TAC [finite_index, dimindex_def]
   THEN CONV_TAC SELECT_CONV
   THEN Q.SUBGOAL_THEN `(UNIV:'n->bool) HAS_SIZE CARD(UNIV:'n->bool)` MP_TAC
   THEN1 PROVE_TAC [HAS_SIZE]
   THEN DISCH_THEN (MP_TAC o MATCH_MP HAS_SIZE_INDEX)
   THEN ASM_REWRITE_TAC [HAS_SIZE, IN_UNIV]
   )

val FINITE_INDEX_WORKS = Q.prove(
   `!i:'a finite_image. ?!n. n < dimindex(:'a) /\ (finite_index n = i)`,
   MP_TAC (MATCH_MP FINITE_INDEX_WORKS_FINITE FINITE_FINITE_IMAGE)
   THEN PROVE_TAC [DIMINDEX_FINITE_IMAGE]
   )

val FINITE_INDEX_INJ = Q.prove(
   `!i j. i < dimindex(:'a) /\ j < dimindex(:'a) ==>
          ((finite_index i :'a = finite_index j) = (i = j))`,
   Q.ASM_CASES_TAC `FINITE(UNIV:'a->bool)`
   THEN ASM_REWRITE_TAC [dimindex_def]
   THENL [
      FIRST_ASSUM (MP_TAC o MATCH_MP FINITE_INDEX_WORKS_FINITE)
      THEN ASM_REWRITE_TAC [dimindex_def]
      THEN PROVE_TAC [],
      PROVE_TAC [DECIDE ``!a. a < 1 = (a = 0)``]
   ])

val FORALL_FINITE_INDEX =
   PROVE [FINITE_INDEX_WORKS]
      ``(!k:'n finite_image. P k) =
        (!i. i < dimindex(:'n) ==> P(finite_index i))``

(* ------------------------------------------------------------------------- *
 * Hence finite Cartesian products, with indexing and lambdas.               *
 * ------------------------------------------------------------------------- *)

val cart_tybij =
   SIMP_RULE std_ss []
     (define_new_type_bijections
        {name = "cart_tybij",
         ABS  = "mk_cart",
         REP  = "dest_cart",
         tyax = new_type_definition("cart",
                  Q.prove(`?f:'b finite_image->'a. (\f. T) f`, REWRITE_TAC[]))})

val () = add_infix_type {Prec = 60, ParseName = SOME "**", Name = "cart",
                         Assoc = HOLgrammars.RIGHT}

val fcp_index_def =
   Q.new_infixl_definition
      ("fcp_index", `$fcp_index x i = dest_cart x (finite_index i)`, 500)

val () = set_fixity "'" (Infixl 2000)
val () = overload_on ("'", Term`$fcp_index`)

(* ---------------------------------------------------------------------- *
 *  Establish arrays as an algebraic datatype, with constructor           *
 *  mk_cart, even though no user would want to define functions that way. *
 *                                                                        *
 *  When the datatype package handles function-spaces (recursing on       *
 *  the right), this will allow the datatype package to define types      *
 *  that recurse through arrays.                                          *
 * ---------------------------------------------------------------------- *)

val fcp_Axiom = Q.store_thm("fcp_Axiom",
   `!f : ('b finite_image -> 'a) -> 'c.
      ?g : 'a ** 'b -> 'c.  !h. g (mk_cart h) = f h`,
   STRIP_TAC THEN Q.EXISTS_TAC `f o dest_cart` THEN SRW_TAC [] [cart_tybij])

val fcp_ind = Q.store_thm("fcp_ind",
   `!P. (!f. P (mk_cart f)) ==> !a. P a`,
   SRW_TAC [] []
   THEN Q.SPEC_THEN `a` (SUBST1_TAC o SYM) (CONJUNCT1 cart_tybij)
   THEN SRW_TAC [] []
   )

(* could just call

     Prim_rec.define_case_constant fcp_Axiom

   but this gives the case constant the name cart_CASE *)

val fcp_case_def = new_specification("fcp_case_def", ["fcp_CASE"],
   Q.prove(
      `?cf. !h f. cf (mk_cart h) f = f h`,
      Q.X_CHOOSE_THEN `cf0` STRIP_ASSUME_TAC
         (SIMP_RULE (srw_ss()) [SKOLEM_THM] fcp_Axiom)
      THEN Q.EXISTS_TAC `\c f. cf0 f c`
      THEN BETA_TAC
      THEN ASM_REWRITE_TAC []
   ))

val fcp_tyinfo =
   TypeBasePure.gen_datatype_info
      {ax = fcp_Axiom, ind = fcp_ind, case_defs = [fcp_case_def]}

val _ = TypeBase.write fcp_tyinfo

local (* and here the palaver to make this persistent; this should be easier
         (even without the faff I went through with PP-blocks etc to make it
         look pretty) *)
   fun out pps =
      let
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
   val _ = adjoin_to_theory {sig_ps = NONE, struct_ps = SOME out}
end

val CART_EQ = Q.store_thm("CART_EQ",
   `!(x:'a ** 'b) y. (x = y) = (!i. i < dimindex(:'b) ==> (x ' i = y ' i))`,
   REPEAT GEN_TAC
   THEN SIMP_TAC std_ss [fcp_index_def, GSYM FORALL_FINITE_INDEX]
   THEN REWRITE_TAC [GSYM FUN_EQ_THM, ETA_AX]
   THEN PROVE_TAC [cart_tybij]
   )

val FCP = new_binder_definition("FCP",
   ``($FCP) = \g.  @(f:'a ** 'b). (!i. i < dimindex(:'b) ==> (f ' i = g i))``)

val FCP_BETA = Q.store_thm("FCP_BETA",
   `!i. i < dimindex(:'b) ==> (((FCP) g:'a ** 'b) ' i = g i)`,
   SIMP_TAC std_ss [FCP]
   THEN CONV_TAC SELECT_CONV
   THEN Q.EXISTS_TAC `mk_cart(\k. g(@i. i < dimindex(:'b) /\
                                  (finite_index i = k))):'a ** 'b`
   THEN SIMP_TAC std_ss [fcp_index_def, cart_tybij]
   THEN REPEAT STRIP_TAC
   THEN AP_TERM_TAC
   THEN MATCH_MP_TAC SELECT_UNIQUE
   THEN GEN_TAC
   THEN REWRITE_TAC []
   THEN PROVE_TAC [FINITE_INDEX_INJ, DIMINDEX_FINITE_IMAGE]
   )

val FCP_UNIQUE = Q.store_thm("FCP_UNIQUE",
   `!(f:'a ** 'b) g. (!i. i < dimindex(:'b) ==> (f ' i = g i)) = ((FCP) g = f)`,
   SIMP_TAC std_ss [CART_EQ, FCP_BETA] THEN PROVE_TAC[])

val FCP_ETA = Q.store_thm("FCP_ETA",
   `!g. (FCP i. g ' i) = g`,
   SIMP_TAC std_ss [CART_EQ, FCP_BETA])

val card_dimindex = save_thm("card_dimindex",
   METIS_PROVE [dimindex_def]
      ``FINITE (UNIV:'a->bool) ==> (CARD (UNIV:'a->bool) = dimindex(:'a))``)

(* ------------------------------------------------------------------------- *
 * Support for introducing finite index types                                *
 * ------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------
   Sums (for concatenation)
   ------------------------------------------------------------------------- *)

val sum_union = Q.prove(
   `UNIV:('a+'b)->bool = ISL UNION ISR`,
   REWRITE_TAC [FUN_EQ_THM, UNIV_DEF, UNION_DEF]
   THEN STRIP_TAC
   THEN ONCE_REWRITE_TAC [GSYM SPECIFICATION]
   THEN SIMP_TAC std_ss [GSPECIFICATION, IN_DEF, sumTheory.ISL_OR_ISR]
   )

val inl_inr_bij = Q.prove(
   `BIJ INL (UNIV:'a->bool) (ISL:'a + 'b -> bool) /\
    BIJ INR (UNIV:'b->bool) (ISR:'a + 'b -> bool)`,
   RW_TAC std_ss [UNIV_DEF, BIJ_DEF, INJ_DEF, SURJ_DEF, IN_DEF]
   THEN PROVE_TAC [sumTheory.INL, sumTheory.INR]
   )

val inl_inr_image = Q.prove(
   `((ISL:'a + 'b -> bool) = IMAGE INL (UNIV:'a->bool)) /\
    ((ISR:'a + 'b -> bool) = IMAGE INR (UNIV:'b->bool))`,
   RW_TAC std_ss [EXTENSION, IMAGE_DEF, IN_UNIV, GSPECIFICATION]
   THEN SIMP_TAC std_ss [IN_DEF]
   THEN Cases_on `x`
   THEN SIMP_TAC std_ss [sumTheory.ISL, sumTheory.ISR, sumTheory.sum_distinct]
   )

val isl_isr_finite = Q.prove(
   `(FINITE (ISL:'a + 'b -> bool) = FINITE (UNIV:'a->bool)) /\
    (FINITE (ISR:'a + 'b -> bool) = FINITE (UNIV:'b->bool))`,
   REWRITE_TAC [inl_inr_image]
   THEN CONJ_TAC
   THEN MATCH_MP_TAC INJECTIVE_IMAGE_FINITE
   THEN REWRITE_TAC [sumTheory.INR_INL_11]
   )

val isl_isr_univ = Q.prove(
   `(FINITE (UNIV:'a -> bool) ==>
      (CARD (ISL:'a + 'b -> bool) = CARD (UNIV:'a->bool))) /\
    (FINITE (UNIV:'b -> bool) ==>
      (CARD (ISR:'a + 'b -> bool) = CARD (UNIV:'b->bool)))`,
    METIS_TAC [FINITE_BIJ_CARD_EQ, isl_isr_finite, inl_inr_bij])

val isl_isr_inter = Q.prove(
   `(ISL:'a + 'b -> bool) INTER (ISR:'a + 'b -> bool) = {}`,
   RW_TAC std_ss [INTER_DEF, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION]
   THEN SIMP_TAC std_ss [IN_DEF]
   THEN Cases_on `x`
   THEN SIMP_TAC std_ss [sumTheory.ISR, sumTheory.ISL]
   )

val isl_isr_union = Q.prove(
   `FINITE (UNIV:'a -> bool) /\ FINITE (UNIV:'b -> bool) ==>
      (CARD ((ISL:'a + 'b -> bool) UNION (ISR:'a + 'b -> bool)) =
       CARD (ISL:'a + 'b -> bool) + CARD (ISR:'a + 'b -> bool))`,
   METIS_TAC [CARD_UNION, arithmeticTheory.ADD_0, CARD_EMPTY,
              isl_isr_inter, isl_isr_finite])

val index_sum = Q.store_thm("index_sum",
   `dimindex(:('a+'b)) =
      if FINITE (UNIV:'a->bool) /\ FINITE (UNIV:'b->bool) then
        dimindex(:'a) + dimindex(:'b)
      else
        1`,
   RW_TAC std_ss [dimindex_def, sum_union, isl_isr_union, isl_isr_univ,
                  FINITE_UNION]
   THEN METIS_TAC [isl_isr_finite]
   )

val finite_sum = Q.store_thm("finite_sum",
   `FINITE (UNIV:('a+'b)->bool) =
    FINITE (UNIV:'a->bool) /\ FINITE (UNIV:'b->bool)`,
   SIMP_TAC std_ss [FINITE_UNION, sum_union, isl_isr_finite])

(* ------------------------------------------------------------------------- *
 * bit0                                                                      *
 * ------------------------------------------------------------------------- *)

val () = Hol_datatype `bit0 = BIT0A of 'a | BIT0B of 'a`

val IS_BIT0A_def = qDefine`
   (IS_BIT0A (BIT0A x) = T) /\ (IS_BIT0A (BIT0B x) = F)`

val IS_BIT0B_def = qDefine`
   (IS_BIT0B (BIT0A x) = F) /\ (IS_BIT0B (BIT0B x) = T)`

val IS_BIT0A_OR_IS_BIT0B = Q.prove(
   `!x. IS_BIT0A x \/ IS_BIT0B x`,
   Cases THEN METIS_TAC [IS_BIT0A_def, IS_BIT0B_def])

val bit0_union = Q.prove(
   `UNIV:('a bit0)->bool = IS_BIT0A UNION IS_BIT0B`,
   REWRITE_TAC [FUN_EQ_THM, UNIV_DEF, UNION_DEF]
   THEN STRIP_TAC
   THEN ONCE_REWRITE_TAC [GSYM SPECIFICATION]
   THEN SIMP_TAC std_ss [GSPECIFICATION, IN_DEF, IS_BIT0A_OR_IS_BIT0B]
   )

val is_bit0a_bij = Q.prove(
   `BIJ BIT0A (UNIV:'a->bool) (IS_BIT0A:'a bit0->bool)`,
   RW_TAC std_ss [UNIV_DEF, BIJ_DEF, INJ_DEF, SURJ_DEF, IN_DEF, IS_BIT0A_def]
   THEN Cases_on `x`
   THEN FULL_SIMP_TAC std_ss [IS_BIT0A_def, IS_BIT0B_def]
   THEN METIS_TAC []
   )

val is_bit0b_bij = Q.prove(
   `BIJ BIT0B (UNIV:'a->bool) (IS_BIT0B:'a bit0->bool)`,
   RW_TAC std_ss [UNIV_DEF, BIJ_DEF, INJ_DEF, SURJ_DEF, IN_DEF, IS_BIT0B_def]
   THEN Cases_on `x`
   THEN FULL_SIMP_TAC std_ss [IS_BIT0A_def, IS_BIT0B_def]
   THEN METIS_TAC []
   )

val is_bit0a_image = Q.prove(
   `IS_BIT0A = IMAGE BIT0A (UNIV:'a->bool)`,
   RW_TAC std_ss [EXTENSION, IMAGE_DEF, IN_UNIV, GSPECIFICATION]
   THEN SIMP_TAC std_ss [IN_DEF]
   THEN Cases_on `x`
   THEN SIMP_TAC (srw_ss()) [IS_BIT0A_def, IS_BIT0B_def]
   )

val is_bit0b_image = Q.prove(
   `IS_BIT0B = IMAGE BIT0B (UNIV:'a->bool)`,
   RW_TAC std_ss [EXTENSION, IMAGE_DEF, IN_UNIV, GSPECIFICATION]
   THEN SIMP_TAC std_ss [IN_DEF]
   THEN Cases_on `x`
   THEN SIMP_TAC (srw_ss()) [IS_BIT0A_def, IS_BIT0B_def]
   )

val is_bit0a_finite = Q.prove(
   `FINITE (IS_BIT0A:'a bit0->bool) = FINITE (UNIV:'a->bool)`,
   REWRITE_TAC [is_bit0a_image]
   THEN MATCH_MP_TAC INJECTIVE_IMAGE_FINITE
   THEN SIMP_TAC (srw_ss()) []
   )

val is_bit0b_finite = Q.prove(
   `FINITE (IS_BIT0B:'a bit0->bool) = FINITE (UNIV:'a->bool)`,
   REWRITE_TAC [is_bit0b_image]
   THEN MATCH_MP_TAC INJECTIVE_IMAGE_FINITE
   THEN SIMP_TAC (srw_ss()) []
   )

val is_bit0a_card = Q.prove(
   `FINITE (UNIV:'a->bool) ==>
      (CARD (IS_BIT0A:'a bit0->bool) = CARD (UNIV:'a->bool))`,
   METIS_TAC [FINITE_BIJ_CARD_EQ, is_bit0a_finite, is_bit0a_bij])

val is_bit0b_card = Q.prove(
   `FINITE (UNIV:'a->bool) ==>
    (CARD (IS_BIT0B:'a bit0->bool) = CARD (UNIV:'a->bool))`,
   METIS_TAC [FINITE_BIJ_CARD_EQ, is_bit0b_finite, is_bit0b_bij])

val is_bit0a_is_bit0b_inter = Q.prove(
   `IS_BIT0A INTER IS_BIT0B = {}`,
   RW_TAC std_ss [INTER_DEF, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION]
   THEN Cases_on `x`
   THEN SIMP_TAC std_ss [IN_DEF, IS_BIT0A_def, IS_BIT0B_def]
   )

val is_bit0a_is_bit0b_union = Q.prove(
   `FINITE (UNIV:'a -> bool) ==>
     (CARD ((IS_BIT0A:'a bit0 -> bool) UNION (IS_BIT0B:'a bit0 -> bool)) =
      CARD (IS_BIT0A:'a bit0 -> bool) + CARD (IS_BIT0B:'a bit0 -> bool))`,
   STRIP_TAC
   THEN IMP_RES_TAC (GSYM is_bit0a_finite)
   THEN IMP_RES_TAC (GSYM is_bit0b_finite)
   THEN IMP_RES_TAC CARD_UNION
   THEN FULL_SIMP_TAC std_ss [is_bit0a_is_bit0b_inter, CARD_EMPTY]
   )

val index_bit0 = Q.store_thm("index_bit0",
   `dimindex(:('a bit0)) =
    if FINITE (UNIV:'a->bool) then 2 * dimindex(:'a) else 1`,
   RW_TAC std_ss [dimindex_def, bit0_union, is_bit0a_is_bit0b_union,
                  FINITE_UNION]
   THEN METIS_TAC [is_bit0a_finite, is_bit0a_card, is_bit0b_finite,
                   is_bit0b_card, arithmeticTheory.TIMES2]
   )

val finite_bit0 = Q.store_thm("finite_bit0",
   `FINITE (UNIV:'a bit0->bool) = FINITE (UNIV:'a->bool)`,
   SIMP_TAC std_ss [FINITE_UNION, is_bit0a_finite, is_bit0b_finite, bit0_union])

(* ------------------------------------------------------------------------- *
 * bit1                                                                      *
 * ------------------------------------------------------------------------- *)

val () = Hol_datatype `bit1 = BIT1A of 'a | BIT1B of 'a | BIT1C`

val IS_BIT1A_def = qDefine`
   (IS_BIT1A (BIT1A x) = T) /\ (IS_BIT1A (BIT1B x) = F) /\
   (IS_BIT1A (BIT1C) = F)`

val IS_BIT1B_def = qDefine`
   (IS_BIT1B (BIT1A x) = F) /\ (IS_BIT1B (BIT1B x) = T) /\
   (IS_BIT1B (BIT1C) = F)`

val IS_BIT1C_def = qDefine`
   (IS_BIT1C (BIT1A x) = F) /\ (IS_BIT1C (BIT1B x) = F) /\
   (IS_BIT1C (BIT1C) = T)`

val IS_BIT1A_OR_IS_BIT1B_OR_IS_BIT1C = Q.prove(
   `!x. IS_BIT1A x \/ IS_BIT1B x \/ IS_BIT1C x`,
   Cases THEN METIS_TAC [IS_BIT1A_def, IS_BIT1B_def, IS_BIT1C_def])

val bit1_union = Q.prove(
   `UNIV:('a bit1)->bool = IS_BIT1A UNION IS_BIT1B UNION IS_BIT1C`,
   REWRITE_TAC [FUN_EQ_THM, UNIV_DEF, UNION_DEF]
   THEN STRIP_TAC
   THEN ONCE_REWRITE_TAC [GSYM SPECIFICATION]
   THEN SIMP_TAC std_ss [GSPECIFICATION, IN_DEF]
   THEN METIS_TAC [IS_BIT1A_OR_IS_BIT1B_OR_IS_BIT1C]
   )

val is_bit1a_bij = Q.prove(
   `BIJ BIT1A (UNIV:'a->bool) (IS_BIT1A:'a bit1->bool)`,
   RW_TAC std_ss [UNIV_DEF, BIJ_DEF, INJ_DEF, SURJ_DEF, IN_DEF, IS_BIT1A_def]
   THEN Cases_on `x`
   THEN FULL_SIMP_TAC std_ss [IS_BIT1A_def, IS_BIT1B_def, IS_BIT1C_def]
   THEN METIS_TAC []
   )

val is_bit1b_bij = Q.prove(
   `BIJ BIT1B (UNIV:'a->bool) (IS_BIT1B:'a bit1->bool)`,
   RW_TAC std_ss [UNIV_DEF, BIJ_DEF, INJ_DEF, SURJ_DEF, IN_DEF, IS_BIT1B_def]
   THEN Cases_on `x`
   THEN FULL_SIMP_TAC std_ss [IS_BIT1A_def, IS_BIT1B_def, IS_BIT1C_def]
   THEN METIS_TAC []
   )

val is_bit1a_image = Q.prove(
   `IS_BIT1A = IMAGE BIT1A (UNIV:'a->bool)`,
   RW_TAC std_ss [EXTENSION, IMAGE_DEF, IN_UNIV, GSPECIFICATION]
   THEN SIMP_TAC std_ss [IN_DEF]
   THEN Cases_on `x`
   THEN SIMP_TAC (srw_ss()) [IS_BIT1A_def, IS_BIT1B_def, IS_BIT1C_def]
   )

val is_bit1b_image = Q.prove(
   `IS_BIT1B = IMAGE BIT1B (UNIV:'a->bool)`,
   RW_TAC std_ss [EXTENSION, IMAGE_DEF, IN_UNIV, GSPECIFICATION]
   THEN SIMP_TAC std_ss [IN_DEF]
   THEN Cases_on `x`
   THEN SIMP_TAC (srw_ss()) [IS_BIT1A_def, IS_BIT1B_def, IS_BIT1C_def]
   )

val is_bit1a_finite = Q.prove(
   `FINITE (IS_BIT1A:'a bit1->bool) = FINITE (UNIV:'a->bool)`,
   REWRITE_TAC [is_bit1a_image]
   THEN MATCH_MP_TAC INJECTIVE_IMAGE_FINITE
   THEN SIMP_TAC (srw_ss()) []
   )

val is_bit1b_finite = Q.prove(
   `FINITE (IS_BIT1B:'a bit1->bool) = FINITE (UNIV:'a->bool)`,
   REWRITE_TAC [is_bit1b_image]
   THEN MATCH_MP_TAC INJECTIVE_IMAGE_FINITE
   THEN SIMP_TAC (srw_ss()) []
   )

val is_bit1a_card = Q.prove(
   `FINITE (UNIV:'a->bool) ==>
    (CARD (IS_BIT1A:'a bit1->bool) = CARD (UNIV:'a->bool))`,
   METIS_TAC [FINITE_BIJ_CARD_EQ, is_bit1a_finite, is_bit1a_bij])

val is_bit1b_card = Q.prove(
   `FINITE (UNIV:'a->bool) ==>
    (CARD (IS_BIT1B:'a bit1->bool) = CARD (UNIV:'a->bool))`,
   METIS_TAC [FINITE_BIJ_CARD_EQ, is_bit1b_finite, is_bit1b_bij])

val is_bit1a_is_bit1b_inter = Q.prove(
   `IS_BIT1A INTER IS_BIT1B = {}`,
   RW_TAC std_ss [INTER_DEF, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION]
   THEN Cases_on `x`
   THEN SIMP_TAC std_ss [IN_DEF, IS_BIT1A_def, IS_BIT1B_def, IS_BIT1C_def])

val IS_BIT1C_EQ_BIT1C = Q.prove(
   `!x. IS_BIT1C x = (x = BIT1C)`,
   Cases THEN SIMP_TAC (srw_ss()) [IS_BIT1C_def])

val is_bit1c_sing = Q.prove(
   `SING IS_BIT1C`,
   REWRITE_TAC [SING_DEF]
   THEN Q.EXISTS_TAC `BIT1C`
   THEN SIMP_TAC std_ss [FUN_EQ_THM, IS_BIT1C_EQ_BIT1C]
   THEN METIS_TAC [IN_SING, SPECIFICATION]
   )

val is_bit1c_finite_card = REWRITE_RULE [SING_IFF_CARD1] is_bit1c_sing

val bit1_union_inter = Q.prove(
   `(IS_BIT1A UNION IS_BIT1B) INTER IS_BIT1C = {}`,
   RW_TAC std_ss [INTER_DEF, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION, IN_UNION]
   THEN Cases_on `x`
   THEN SIMP_TAC std_ss [IN_DEF, IS_BIT1A_def, IS_BIT1B_def, IS_BIT1C_def]
   )

val is_bit1a_is_bit1b_is_bit1c_union = Q.prove(
   `FINITE (UNIV:'a -> bool) ==>
    (CARD ((IS_BIT1A:'a bit1 -> bool) UNION (IS_BIT1B:'a bit1 -> bool) UNION
           (IS_BIT1C:'a bit1 -> bool)) =
     CARD (IS_BIT1A:'a bit1 -> bool) + CARD (IS_BIT1B:'a bit1 -> bool) + 1)`,
   STRIP_TAC
   THEN `FINITE (IS_BIT1A UNION IS_BIT1B)`
     by METIS_TAC [is_bit1a_finite, is_bit1b_finite, FINITE_UNION]
   THEN STRIP_ASSUME_TAC is_bit1c_finite_card
   THEN IMP_RES_TAC CARD_UNION
   THEN FULL_SIMP_TAC std_ss [bit1_union_inter, CARD_EMPTY]
   THEN NTAC 8 (POP_ASSUM (K ALL_TAC))
   THEN IMP_RES_TAC (GSYM is_bit1a_finite)
   THEN IMP_RES_TAC (GSYM is_bit1b_finite)
   THEN IMP_RES_TAC CARD_UNION
   THEN FULL_SIMP_TAC std_ss [is_bit1a_is_bit1b_inter, CARD_EMPTY]
   )

val index_bit1 = Q.store_thm("index_bit1",
   `dimindex(:('a bit1)) =
    if FINITE (UNIV:'a->bool) then 2 * dimindex(:'a) + 1 else 1`,
   RW_TAC std_ss [dimindex_def, bit1_union, is_bit1a_is_bit1b_is_bit1c_union,
                  FINITE_UNION]
   THEN METIS_TAC [is_bit1a_finite, is_bit1a_card, is_bit1c_finite_card,
                   is_bit1b_finite, is_bit1b_card, arithmeticTheory.TIMES2]
   )

val finite_bit1 = Q.store_thm("finite_bit1",
   `FINITE (UNIV:'a bit1->bool) = FINITE (UNIV:'a->bool)`,
   SIMP_TAC std_ss [FINITE_UNION, is_bit1a_finite, is_bit1b_finite,
                    is_bit1c_finite_card, bit1_union])

(* Delete temporary constants *)

val () = List.app Theory.delete_const
            ["IS_BIT0A", "IS_BIT0B", "IS_BIT1A", "IS_BIT1B", "IS_BIT1C"]

(* ------------------------------------------------------------------------ *
 * one                                                                      *
 * ------------------------------------------------------------------------ *)

val one_sing = Q.prove(
   `SING (UNIV:one->bool)`,
   REWRITE_TAC [SING_DEF]
   THEN Q.EXISTS_TAC `()`
   THEN SIMP_TAC std_ss [FUN_EQ_THM]
   THEN Cases
   THEN METIS_TAC [IN_SING, IN_UNIV, SPECIFICATION]
   )

val one_finite_card = REWRITE_RULE [SING_IFF_CARD1] one_sing

val index_one = Q.store_thm("index_one",
   `dimindex(:one) = 1`, METIS_TAC [dimindex_def, one_finite_card])

val finite_one = save_thm("finite_one", CONJUNCT2 one_finite_card)

(* ------------------------------------------------------------------------ *
 * FCP update                                                               *
 * ------------------------------------------------------------------------ *)

val FCP_ss = rewrites [FCP_BETA, FCP_ETA, CART_EQ]

val () = set_fixity ":+" (Infixl 325)

val FCP_UPDATE_def =
   Lib.with_flag (computeLib.auto_import_definitions, false)
      (xDefine "FCP_UPDATE")
      `$:+ a b = \m:'a ** 'b. (FCP c. if a = c then b else m ' c):'a ** 'b`

val FCP_UPDATE_COMMUTES = Q.store_thm ("FCP_UPDATE_COMMUTES",
   `!m a b c d. ~(a = b) ==> ((a :+ c) ((b :+ d) m) = (b :+ d) ((a :+ c) m))`,
   REPEAT strip_tac
   \\ rewrite_tac [FUN_EQ_THM]
   \\ srw_tac [FCP_ss] [FCP_UPDATE_def]
   \\ rw_tac std_ss []
   )

val FCP_UPDATE_EQ = Q.store_thm("FCP_UPDATE_EQ",
   `!m a b c. (a :+ c) ((a :+ b) m) = (a :+ c) m`,
   REPEAT strip_tac
   \\ rewrite_tac [FUN_EQ_THM]
   \\ srw_tac [FCP_ss] [FCP_UPDATE_def]
   )

val FCP_UPDATE_IMP_ID = Q.store_thm("FCP_UPDATE_IMP_ID",
   `!m a v. (m ' a = v) ==> ((a :+ v) m = m)`,
   srw_tac [FCP_ss] [FCP_UPDATE_def]
   \\ rw_tac std_ss []
   )

val APPLY_FCP_UPDATE_ID = Q.store_thm("APPLY_FCP_UPDATE_ID",
   `!m a. (a :+ (m ' a)) m = m`,
   srw_tac [FCP_ss] [FCP_UPDATE_def])

val FCP_APPLY_UPDATE_THM = Q.store_thm("FCP_APPLY_UPDATE_THM",
  `!(m:'a ** 'b) a w b. ((a :+ w) m) ' b =
       if b < dimindex(:'b) then
         if a = b then w else m ' b
       else
         FAIL (fcp_index) ^(mk_var("index out of range", bool)) ((a :+ w) m) b`,
  srw_tac [FCP_ss] [FCP_UPDATE_def, combinTheory.FAIL_THM])

(* ------------------------------------------------------------------------ *
 * A collection of list related operations                                  *
 * ------------------------------------------------------------------------ *)

val FCP_HD_def = Define `FCP_HD v = v ' 0`

val FCP_TL_def = Define `FCP_TL v = FCP i. v ' (SUC i)`

val FCP_CONS_def = Define`
   FCP_CONS h (v:'a ** 'b) = (0 :+ h) (FCP i. v ' (PRE i))`

val FCP_MAP_def = Define`
   FCP_MAP f (v:'a ** 'c) = (FCP i. f (v ' i)):'b ** 'c`

val FCP_EXISTS_def = zDefine`
   FCP_EXISTS P (v:'b ** 'a) = ?i. i < dimindex (:'a) /\ P (v ' i)`

val FCP_EVERY_def = zDefine`
   FCP_EVERY P (v:'b ** 'a) = !i. dimindex (:'a) <= i \/ P (v ' i)`

val FCP_CONCAT_def = Define`
   FCP_CONCAT (a:'a ** 'b) (b:'a ** 'c) =
   (FCP i. if i < dimindex(:'c) then
              b ' i
           else
              a ' (i - dimindex(:'c))): 'a ** ('b + 'c)`

val FCP_ZIP_def = Define`
   FCP_ZIP (a:'a ** 'b) (b:'c ** 'b) = (FCP i. (a ' i, b ' i)): ('a # 'c) ** 'b`

val V2L_def = Define `V2L (v:'a ** 'b) = GENLIST ($' v) (dimindex(:'b))`

val L2V_def = Define `L2V L = FCP i. EL i L`

val FCP_FOLD_def = Define `FCP_FOLD (f:'b -> 'a -> 'b) i v = FOLDL f i (V2L v)`

(* Some theorems about these operations *)

val LENGTH_V2L = Q.store_thm("LENGTH_V2L",
   `!v. LENGTH (V2L (v:'a ** 'b)) = dimindex (:'b)`,
   rw [V2L_def])

val EL_V2L = Q.store_thm("EL_V2L",
   `!i v. i < dimindex (:'b) ==> (EL i (V2L v) = (v:'a ** 'b)  ' i)`,
   rw [V2L_def])

val FCP_MAP = Q.store_thm("FCP_MAP",
   `!f v. FCP_MAP f v = L2V (MAP f (V2L v))`,
   srw_tac [FCP_ss] [FCP_MAP_def, V2L_def, L2V_def, listTheory.MAP_GENLIST])

val FCP_TL = Q.store_thm("FCP_TL",
   `!v. 1 < dimindex (:'b) /\ (dimindex(:'c) = dimindex(:'b) - 1) ==>
        (FCP_TL (v:'a ** 'b) = L2V (TL (V2L v)):'a ** 'c)`,
   REPEAT strip_tac
   \\ Cases_on `dimindex(:'b)`
   >- prove_tac [DECIDE ``1n < n ==> n <> 0``]
   \\ srw_tac [FCP_ss] [FCP_TL_def, V2L_def, L2V_def, listTheory.TL_GENLIST]
   )

val FCP_EXISTS = Q.store_thm("FCP_EXISTS",
   `!P v. FCP_EXISTS P v = EXISTS P (V2L v)`,
   rw [FCP_EXISTS_def, V2L_def, listTheory.EXISTS_GENLIST])

val FCP_EVERY = Q.store_thm("FCP_EVERY",
   `!P v. FCP_EVERY P v = EVERY P (V2L v)`,
   rw [FCP_EVERY_def, V2L_def, listTheory.EVERY_GENLIST]
   \\ metis_tac [arithmeticTheory.NOT_LESS]
   )

val FCP_HD = Q.store_thm("FCP_HD",
   `!v. FCP_HD v = HD (V2L v)`,
   rw [FCP_HD_def, V2L_def, DIMINDEX_GE_1, listTheory.HD_GENLIST_COR,
       DIMINDEX_GT_0])

val FCP_CONS = Q.store_thm("FCP_CONS",
  `!a v. FCP_CONS a (v:'a ** 'b) = L2V (a::V2L v):'a ** 'b + 1`,
  srw_tac [FCP_ss] [FCP_CONS_def, V2L_def, L2V_def, FCP_UPDATE_def]
  \\ pop_assum mp_tac
  \\ Cases_on `i`
  \\ lrw [index_sum, index_one, listTheory.EL_GENLIST]
  )

val V2L_L2V = Q.store_thm("V2L_L2V",
   `!x. (dimindex (:'b) = LENGTH x) ==> (V2L (L2V x:'a ** 'b) = x)`,
   rw [V2L_def, L2V_def, listTheory.LIST_EQ_REWRITE, FCP_BETA])

val NULL_V2L = Q.store_thm("NULL_V2L",
   `!v. ~NULL (V2L v)`,
   rw [V2L_def, listTheory.NULL_GENLIST, DIMINDEX_NONZERO])

val READ_TL = Q.store_thm("READ_TL",
  `!i a. i < dimindex (:'b) ==>
         (((FCP_TL a):'a ** 'b) ' i = (a:'a ** 'c) ' (SUC i))`,
  rw [FCP_TL_def, FCP_BETA])

val READ_L2V = Q.store_thm("READ_L2V",
  `!i a. i < dimindex (:'b) ==> ((L2V a:'a ** 'b) ' i = EL i a)`,
  rw [L2V_def, FCP_BETA])

val index_comp = Q.store_thm("index_comp",
  `!f n.
      (($FCP f):'a ** 'b) ' n =
      if n < dimindex (:'b) then
        f n
      else
        FAIL $' ^(mk_var("FCP out of bounds", bool))
             (($FCP f):'a ** 'b) n`,
  srw_tac [FCP_ss] [combinTheory.FAIL_THM])

val fcp_subst_comp = Q.store_thm("fcp_subst_comp",
  `!a b f. (x :+ y) ($FCP f):'a ** 'b =
         ($FCP (\c. if x = c then y else f c)):'a ** 'b`,
  srw_tac [FCP_ss] [FCP_UPDATE_def])

val () = computeLib.add_persistent_funs ["FCP_EXISTS", "FCP_EVERY"]

(* ------------------------------------------------------------------------- *)

val () = export_theory()
