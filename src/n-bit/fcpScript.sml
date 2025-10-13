(* ========================================================================= *)
(* FILE          : fcpScript.sml                                             *)
(* DESCRIPTION   : A port, from HOL light, of John Harrison's treatment of   *)
(*                 finite Cartesian products (TPHOLs 2005)                   *)
(* DATE          : 2005                                                      *)
(* ========================================================================= *)
Theory fcp
Ancestors
  arithmetic pred_set list iterate
Libs
  numLib hurdUtils mesonLib


(* ------------------------------------------------------------------------- *)
(*  NOTES for HOL-Light users (or HOL4 porters of HOL-Light theories)        *)
(*                                                                           *)
(*  FCP indexes in HOL-Light are ranged from 1 to ‘dimindex(:'N)’, while in  *)
(*  HOL4 they are ranged from ‘0’ to ‘dimindex(:'N) - 1’. Thus, whenever in  *)
(*  HOL-Light it says ‘1 <= i /\ i <= dimindex(:'N)’, here in HOL4 one says  *)
(*  ‘i < dimindex(:'N)’ instead. (as ‘0 <= i’ is always true for naturals.)  *)
(*                                                                           *)
(*  In particular, the frequently needed DIMINDEX_GE_1 in many FCP-related   *)
(*  proofs in HOL-Light, is not very useful here in HOL4. Porters may need   *)
(*  to use the new DIMINDEX_GT_0 instead, in some ported proofs.             *)
(*                                                                           *)
(*  The other difference is that, in HOL-Light, the (') operator is total:   *)
(*  ‘f ' i := 0’ if ‘1 <= i /\ i <= dimindex(:N)’ does not hold, while here  *)
(*  ‘f ' i’ is unspecified if ‘i >= dimindex(:'N)’. Thus for some theorems,  *)
(*  porters may need to add extra antecedents like ‘i < dimindex(:'N) ==> ’  *)
(*  to some FCP-related theorems.       -- Chun Tian (binghe), May 12, 2022  *)
(* ------------------------------------------------------------------------- *)

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

Theorem FINITE_IMAGE_IMAGE[local]:
    UNIV:'a finite_image->bool =
    IMAGE mk_finite_image
      (if FINITE(UNIV:'a->bool) then UNIV:'a->bool else {ARB})
Proof
   MP_TAC finite_image_tybij
   THEN COND_CASES_TAC
   THEN ASM_REWRITE_TAC []
   THEN REWRITE_TAC [EXTENSION, IN_IMAGE, IN_SING, IN_UNIV]
   THEN PROVE_TAC []
QED

(* ------------------------------------------------------------------------- *
 * Dimension of such a type, and indexing over it.                           *
 * ------------------------------------------------------------------------- *)

Definition dimindex_def[nocompute]:
   dimindex(:'a) = if FINITE (UNIV:'a->bool) then CARD (UNIV:'a->bool) else 1
End

Theorem NOT_FINITE_IMP_dimindex_1:
    ~FINITE univ(:'a) ==> (dimindex(:'a) = 1)
Proof
   METIS_TAC [dimindex_def]
QED

Theorem HAS_SIZE_FINITE_IMAGE[local]:
    (UNIV:'a finite_image->bool) HAS_SIZE dimindex(:'a)
Proof
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
QED

val CARD_FINITE_IMAGE =
   PROVE [HAS_SIZE_FINITE_IMAGE, HAS_SIZE]
      ``CARD (UNIV:'a finite_image->bool) = dimindex(:'a)``

val FINITE_FINITE_IMAGE =
   PROVE [HAS_SIZE_FINITE_IMAGE, HAS_SIZE]
      ``FINITE (UNIV:'a finite_image->bool)``

Theorem DIMINDEX_NONZERO[simp] =
   METIS_PROVE [HAS_SIZE_0, UNIV_NOT_EMPTY, HAS_SIZE_FINITE_IMAGE]
      ``~(dimindex(:'a) = 0)``

Theorem DIMINDEX_GE_1[simp]:
   1 <= dimindex(:'a)
Proof
  REWRITE_TAC [DECIDE ``1 <= x <=> ~(x = 0)``, DIMINDEX_NONZERO]
QED

(* |- 0 < dimindex(:'a) *)
Theorem DIMINDEX_GT_0[simp] =
   REWRITE_RULE [arithmeticTheory.NOT_ZERO_LT_ZERO] DIMINDEX_NONZERO

Theorem DIMINDEX_FINITE_IMAGE[local]:
    dimindex(:'a finite_image) = dimindex(:'a)
Proof
   GEN_REWRITE_TAC LAND_CONV empty_rewrites [dimindex_def]
   THEN MP_TAC HAS_SIZE_FINITE_IMAGE
   THEN SIMP_TAC std_ss [FINITE_FINITE_IMAGE, HAS_SIZE]
QED

Definition finite_index[nocompute]:
   finite_index = @f:num->'a. !x:'a. ?!n. n < dimindex(:'a) /\ (f n = x)
End

Theorem FINITE_INDEX_WORKS_FINITE[local]:
    FINITE (UNIV:'n->bool) ==>
    !i:'n. ?!n. n < dimindex(:'n) /\ (finite_index n = i)
Proof
   DISCH_TAC
   THEN ASM_REWRITE_TAC [finite_index, dimindex_def]
   THEN CONV_TAC SELECT_CONV
   THEN Q.SUBGOAL_THEN `(UNIV:'n->bool) HAS_SIZE CARD(UNIV:'n->bool)` MP_TAC
   THEN1 PROVE_TAC [HAS_SIZE]
   THEN DISCH_THEN (MP_TAC o MATCH_MP HAS_SIZE_INDEX)
   THEN ASM_REWRITE_TAC [HAS_SIZE, IN_UNIV]
QED

Theorem FINITE_INDEX_WORKS[local]:
    !i:'a finite_image. ?!n. n < dimindex(:'a) /\ (finite_index n = i)
Proof
   MP_TAC (MATCH_MP FINITE_INDEX_WORKS_FINITE FINITE_FINITE_IMAGE)
   THEN PROVE_TAC [DIMINDEX_FINITE_IMAGE]
QED

Theorem FINITE_INDEX_INJ[local]:
    !i j. i < dimindex(:'a) /\ j < dimindex(:'a) ==>
          ((finite_index i :'a = finite_index j) = (i = j))
Proof
   Q.ASM_CASES_TAC `FINITE(UNIV:'a->bool)`
   THEN ASM_REWRITE_TAC [dimindex_def]
   THENL [
      FIRST_ASSUM (MP_TAC o MATCH_MP FINITE_INDEX_WORKS_FINITE)
      THEN ASM_REWRITE_TAC [dimindex_def]
      THEN PROVE_TAC [],
      PROVE_TAC [DECIDE ``!a. a < 1 <=> (a = 0)``]
   ]
QED

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

Theorem fcp_Axiom:
    !f : ('b finite_image -> 'a) -> 'c.
      ?g : 'a ** 'b -> 'c.  !h. g (mk_cart h) = f h
Proof
   STRIP_TAC THEN Q.EXISTS_TAC `f o dest_cart` THEN SRW_TAC [] [cart_tybij]
QED

Theorem fcp_ind:
    !P. (!f. P (mk_cart f)) ==> !a. P a
Proof
   SRW_TAC [] []
   THEN Q.SPEC_THEN `a` (SUBST1_TAC o SYM) (CONJUNCT1 cart_tybij)
   THEN SRW_TAC [] []
QED

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

Theorem CART_EQ:
    !(x:'a ** 'b) y. (x = y) = (!i. i < dimindex(:'b) ==> (x ' i = y ' i))
Proof
   REPEAT GEN_TAC
   THEN SIMP_TAC std_ss [fcp_index_def, GSYM FORALL_FINITE_INDEX]
   THEN REWRITE_TAC [GSYM FUN_EQ_THM, ETA_AX]
   THEN PROVE_TAC [cart_tybij]
QED

val FCP = new_binder_definition("FCP",
   ``($FCP) = \g.  @(f:'a ** 'b). (!i. i < dimindex(:'b) ==> (f ' i = g i))``)

(* NOTE: generalizing ‘g’ will break blastLib.sml *)
Theorem FCP_BETA :
    !i. i < dimindex(:'b) ==> (((FCP) g:'a ** 'b) ' i = g i)
Proof
    SIMP_TAC std_ss [FCP]
 >> CONV_TAC SELECT_CONV
 >> Q.EXISTS_TAC `mk_cart(\k. g(@i. i < dimindex(:'b) /\
                                   (finite_index i = k))):'a ** 'b`
 >> SIMP_TAC std_ss [fcp_index_def, cart_tybij]
 >> REPEAT STRIP_TAC
 >> AP_TERM_TAC
 >> MATCH_MP_TAC SELECT_UNIQUE
 >> GEN_TAC
 >> REWRITE_TAC []
 >> PROVE_TAC [FINITE_INDEX_INJ, DIMINDEX_FINITE_IMAGE]
QED

Theorem FCP_UNIQUE:
    !(f:'a ** 'b) g. (!i. i < dimindex(:'b) ==> (f ' i = g i)) = ((FCP) g = f)
Proof
   SIMP_TAC std_ss [CART_EQ, FCP_BETA] THEN PROVE_TAC[]
QED

Theorem FCP_ETA:
    !g. (FCP i. g ' i) = g
Proof
   SIMP_TAC std_ss [CART_EQ, FCP_BETA]
QED

Theorem card_dimindex :
    FINITE (UNIV:'a->bool) ==> (CARD (UNIV:'a->bool) = dimindex(:'a))
Proof
    METIS_TAC [dimindex_def]
QED

(* ------------------------------------------------------------------------- *
 * Support for introducing finite index types                                *
 * ------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------
   Sums (for concatenation)
   ------------------------------------------------------------------------- *)

Theorem sum_union[local]:
    UNIV:('a+'b)->bool = ISL UNION ISR
Proof
   REWRITE_TAC [FUN_EQ_THM, UNIV_DEF, UNION_DEF]
   THEN STRIP_TAC
   THEN ONCE_REWRITE_TAC [GSYM SPECIFICATION]
   THEN SIMP_TAC std_ss [GSPECIFICATION, IN_DEF, sumTheory.ISL_OR_ISR]
QED

Theorem inl_inr_bij[local]:
    BIJ INL (UNIV:'a->bool) (ISL:'a + 'b -> bool) /\
    BIJ INR (UNIV:'b->bool) (ISR:'a + 'b -> bool)
Proof
   RW_TAC std_ss [UNIV_DEF, BIJ_DEF, INJ_DEF, SURJ_DEF, IN_DEF]
   THEN PROVE_TAC [sumTheory.INL, sumTheory.INR]
QED

Theorem inl_inr_image[local]:
    ((ISL:'a + 'b -> bool) = IMAGE INL (UNIV:'a->bool)) /\
    ((ISR:'a + 'b -> bool) = IMAGE INR (UNIV:'b->bool))
Proof
   RW_TAC std_ss [EXTENSION, IMAGE_DEF, IN_UNIV, GSPECIFICATION]
   THEN SIMP_TAC std_ss [IN_DEF]
   THEN Cases_on `x`
   THEN SIMP_TAC std_ss [sumTheory.ISL, sumTheory.ISR, sumTheory.sum_distinct]
QED

Theorem isl_isr_finite[local]:
    (FINITE (ISL:'a + 'b -> bool) = FINITE (UNIV:'a->bool)) /\
    (FINITE (ISR:'a + 'b -> bool) = FINITE (UNIV:'b->bool))
Proof
   REWRITE_TAC [inl_inr_image]
   THEN CONJ_TAC
   THEN MATCH_MP_TAC INJECTIVE_IMAGE_FINITE
   THEN REWRITE_TAC [sumTheory.INR_INL_11]
QED

Theorem isl_isr_univ[local]:
    (FINITE (UNIV:'a -> bool) ==>
      (CARD (ISL:'a + 'b -> bool) = CARD (UNIV:'a->bool))) /\
    (FINITE (UNIV:'b -> bool) ==>
      (CARD (ISR:'a + 'b -> bool) = CARD (UNIV:'b->bool)))
Proof
    METIS_TAC [FINITE_BIJ_CARD_EQ, isl_isr_finite, inl_inr_bij]
QED

Theorem isl_isr_inter[local]:
    (ISL:'a + 'b -> bool) INTER (ISR:'a + 'b -> bool) = {}
Proof
   RW_TAC std_ss [INTER_DEF, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION]
   THEN SIMP_TAC std_ss [IN_DEF]
   THEN Cases_on `x`
   THEN SIMP_TAC std_ss [sumTheory.ISR, sumTheory.ISL]
QED

Theorem isl_isr_union[local]:
    FINITE (UNIV:'a -> bool) /\ FINITE (UNIV:'b -> bool) ==>
      (CARD ((ISL:'a + 'b -> bool) UNION (ISR:'a + 'b -> bool)) =
       CARD (ISL:'a + 'b -> bool) + CARD (ISR:'a + 'b -> bool))
Proof
   METIS_TAC [CARD_UNION, arithmeticTheory.ADD_0, CARD_EMPTY,
              isl_isr_inter, isl_isr_finite]
QED

Theorem index_sum:
    dimindex(:('a+'b)) =
      if FINITE (UNIV:'a->bool) /\ FINITE (UNIV:'b->bool) then
        dimindex(:'a) + dimindex(:'b)
      else
        1
Proof
   RW_TAC std_ss [dimindex_def, sum_union, isl_isr_union, isl_isr_univ,
                  FINITE_UNION]
   THEN METIS_TAC [isl_isr_finite]
QED

Theorem finite_sum:
    FINITE (UNIV:('a+'b)->bool) <=>
    FINITE (UNIV:'a->bool) /\ FINITE (UNIV:'b->bool)
Proof
   SIMP_TAC std_ss [FINITE_UNION, sum_union, isl_isr_finite]
QED

(* ------------------------------------------------------------------------- *
 * bit0                                                                      *
 * ------------------------------------------------------------------------- *)

val () = Hol_datatype `bit0 = BIT0A of 'a | BIT0B of 'a`

Definition IS_BIT0A_def[nocompute]:
   (IS_BIT0A (BIT0A x) = T) /\ (IS_BIT0A (BIT0B x) = F)
End

Definition IS_BIT0B_def[nocompute]:
   (IS_BIT0B (BIT0A x) = F) /\ (IS_BIT0B (BIT0B x) = T)
End

Theorem IS_BIT0A_OR_IS_BIT0B[local]:
    !x. IS_BIT0A x \/ IS_BIT0B x
Proof
   Cases THEN METIS_TAC [IS_BIT0A_def, IS_BIT0B_def]
QED

Theorem bit0_union[local]:
    UNIV:('a bit0)->bool = IS_BIT0A UNION IS_BIT0B
Proof
   REWRITE_TAC [FUN_EQ_THM, UNIV_DEF, UNION_DEF]
   THEN STRIP_TAC
   THEN ONCE_REWRITE_TAC [GSYM SPECIFICATION]
   THEN SIMP_TAC std_ss [GSPECIFICATION, IN_DEF, IS_BIT0A_OR_IS_BIT0B]
QED

Theorem is_bit0a_bij[local]:
    BIJ BIT0A (UNIV:'a->bool) (IS_BIT0A:'a bit0->bool)
Proof
   RW_TAC std_ss [UNIV_DEF, BIJ_DEF, INJ_DEF, SURJ_DEF, IN_DEF, IS_BIT0A_def]
   THEN Cases_on `x`
   THEN FULL_SIMP_TAC std_ss [IS_BIT0A_def, IS_BIT0B_def]
   THEN METIS_TAC []
QED

Theorem is_bit0b_bij[local]:
    BIJ BIT0B (UNIV:'a->bool) (IS_BIT0B:'a bit0->bool)
Proof
   RW_TAC std_ss [UNIV_DEF, BIJ_DEF, INJ_DEF, SURJ_DEF, IN_DEF, IS_BIT0B_def]
   THEN Cases_on `x`
   THEN FULL_SIMP_TAC std_ss [IS_BIT0A_def, IS_BIT0B_def]
   THEN METIS_TAC []
QED

Theorem is_bit0a_image[local]:
    IS_BIT0A = IMAGE BIT0A (UNIV:'a->bool)
Proof
   RW_TAC std_ss [EXTENSION, IMAGE_DEF, IN_UNIV, GSPECIFICATION]
   THEN SIMP_TAC std_ss [IN_DEF]
   THEN Cases_on `x`
   THEN SIMP_TAC (srw_ss()) [IS_BIT0A_def, IS_BIT0B_def]
QED

Theorem is_bit0b_image[local]:
    IS_BIT0B = IMAGE BIT0B (UNIV:'a->bool)
Proof
   RW_TAC std_ss [EXTENSION, IMAGE_DEF, IN_UNIV, GSPECIFICATION]
   THEN SIMP_TAC std_ss [IN_DEF]
   THEN Cases_on `x`
   THEN SIMP_TAC (srw_ss()) [IS_BIT0A_def, IS_BIT0B_def]
QED

Theorem is_bit0a_finite[local]:
    FINITE (IS_BIT0A:'a bit0->bool) = FINITE (UNIV:'a->bool)
Proof
   REWRITE_TAC [is_bit0a_image]
   THEN MATCH_MP_TAC INJECTIVE_IMAGE_FINITE
   THEN SIMP_TAC (srw_ss()) []
QED

Theorem is_bit0b_finite[local]:
    FINITE (IS_BIT0B:'a bit0->bool) = FINITE (UNIV:'a->bool)
Proof
   REWRITE_TAC [is_bit0b_image]
   THEN MATCH_MP_TAC INJECTIVE_IMAGE_FINITE
   THEN SIMP_TAC (srw_ss()) []
QED

Theorem is_bit0a_card[local]:
    FINITE (UNIV:'a->bool) ==>
      (CARD (IS_BIT0A:'a bit0->bool) = CARD (UNIV:'a->bool))
Proof
   METIS_TAC [FINITE_BIJ_CARD_EQ, is_bit0a_finite, is_bit0a_bij]
QED

Theorem is_bit0b_card[local]:
    FINITE (UNIV:'a->bool) ==>
    (CARD (IS_BIT0B:'a bit0->bool) = CARD (UNIV:'a->bool))
Proof
   METIS_TAC [FINITE_BIJ_CARD_EQ, is_bit0b_finite, is_bit0b_bij]
QED

Theorem is_bit0a_is_bit0b_inter[local]:
    IS_BIT0A INTER IS_BIT0B = {}
Proof
   RW_TAC std_ss [INTER_DEF, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION]
   THEN Cases_on `x`
   THEN SIMP_TAC std_ss [IN_DEF, IS_BIT0A_def, IS_BIT0B_def]
QED

Theorem is_bit0a_is_bit0b_union[local]:
    FINITE (UNIV:'a -> bool) ==>
     (CARD ((IS_BIT0A:'a bit0 -> bool) UNION (IS_BIT0B:'a bit0 -> bool)) =
      CARD (IS_BIT0A:'a bit0 -> bool) + CARD (IS_BIT0B:'a bit0 -> bool))
Proof
   STRIP_TAC
   THEN IMP_RES_TAC (GSYM is_bit0a_finite)
   THEN IMP_RES_TAC (GSYM is_bit0b_finite)
   THEN IMP_RES_TAC CARD_UNION
   THEN FULL_SIMP_TAC std_ss [is_bit0a_is_bit0b_inter, CARD_EMPTY]
QED

Theorem index_bit0:
    dimindex(:('a bit0)) =
    if FINITE (UNIV:'a->bool) then 2 * dimindex(:'a) else 1
Proof
   RW_TAC std_ss [dimindex_def, bit0_union, is_bit0a_is_bit0b_union,
                  FINITE_UNION]
   THEN METIS_TAC [is_bit0a_finite, is_bit0a_card, is_bit0b_finite,
                   is_bit0b_card, arithmeticTheory.TIMES2]
QED

Theorem finite_bit0:
    FINITE (UNIV:'a bit0->bool) = FINITE (UNIV:'a->bool)
Proof
   SIMP_TAC std_ss [FINITE_UNION, is_bit0a_finite, is_bit0b_finite, bit0_union]
QED

(* ------------------------------------------------------------------------- *
 * bit1                                                                      *
 * ------------------------------------------------------------------------- *)

val () = Hol_datatype `bit1 = BIT1A of 'a | BIT1B of 'a | BIT1C`

Definition IS_BIT1A_def[nocompute]:
   (IS_BIT1A (BIT1A x) = T) /\ (IS_BIT1A (BIT1B x) = F) /\
   (IS_BIT1A (BIT1C) = F)
End

Definition IS_BIT1B_def[nocompute]:
   (IS_BIT1B (BIT1A x) = F) /\ (IS_BIT1B (BIT1B x) = T) /\
   (IS_BIT1B (BIT1C) = F)
End

Definition IS_BIT1C_def[nocompute]:
   (IS_BIT1C (BIT1A x) = F) /\ (IS_BIT1C (BIT1B x) = F) /\
   (IS_BIT1C (BIT1C) = T)
End

Theorem IS_BIT1A_OR_IS_BIT1B_OR_IS_BIT1C[local]:
    !x. IS_BIT1A x \/ IS_BIT1B x \/ IS_BIT1C x
Proof
   Cases THEN METIS_TAC [IS_BIT1A_def, IS_BIT1B_def, IS_BIT1C_def]
QED

Theorem bit1_union[local]:
    UNIV:('a bit1)->bool = IS_BIT1A UNION IS_BIT1B UNION IS_BIT1C
Proof
   REWRITE_TAC [FUN_EQ_THM, UNIV_DEF, UNION_DEF]
   THEN STRIP_TAC
   THEN ONCE_REWRITE_TAC [GSYM SPECIFICATION]
   THEN SIMP_TAC std_ss [GSPECIFICATION, IN_DEF]
   THEN METIS_TAC [IS_BIT1A_OR_IS_BIT1B_OR_IS_BIT1C]
QED

Theorem is_bit1a_bij[local]:
    BIJ BIT1A (UNIV:'a->bool) (IS_BIT1A:'a bit1->bool)
Proof
   RW_TAC std_ss [UNIV_DEF, BIJ_DEF, INJ_DEF, SURJ_DEF, IN_DEF, IS_BIT1A_def]
   THEN Cases_on `x`
   THEN FULL_SIMP_TAC std_ss [IS_BIT1A_def, IS_BIT1B_def, IS_BIT1C_def]
   THEN METIS_TAC []
QED

Theorem is_bit1b_bij[local]:
    BIJ BIT1B (UNIV:'a->bool) (IS_BIT1B:'a bit1->bool)
Proof
   RW_TAC std_ss [UNIV_DEF, BIJ_DEF, INJ_DEF, SURJ_DEF, IN_DEF, IS_BIT1B_def]
   THEN Cases_on `x`
   THEN FULL_SIMP_TAC std_ss [IS_BIT1A_def, IS_BIT1B_def, IS_BIT1C_def]
   THEN METIS_TAC []
QED

Theorem is_bit1a_image[local]:
    IS_BIT1A = IMAGE BIT1A (UNIV:'a->bool)
Proof
   RW_TAC std_ss [EXTENSION, IMAGE_DEF, IN_UNIV, GSPECIFICATION]
   THEN SIMP_TAC std_ss [IN_DEF]
   THEN Cases_on `x`
   THEN SIMP_TAC (srw_ss()) [IS_BIT1A_def, IS_BIT1B_def, IS_BIT1C_def]
QED

Theorem is_bit1b_image[local]:
    IS_BIT1B = IMAGE BIT1B (UNIV:'a->bool)
Proof
   RW_TAC std_ss [EXTENSION, IMAGE_DEF, IN_UNIV, GSPECIFICATION]
   THEN SIMP_TAC std_ss [IN_DEF]
   THEN Cases_on `x`
   THEN SIMP_TAC (srw_ss()) [IS_BIT1A_def, IS_BIT1B_def, IS_BIT1C_def]
QED

Theorem is_bit1a_finite[local]:
    FINITE (IS_BIT1A:'a bit1->bool) = FINITE (UNIV:'a->bool)
Proof
   REWRITE_TAC [is_bit1a_image]
   THEN MATCH_MP_TAC INJECTIVE_IMAGE_FINITE
   THEN SIMP_TAC (srw_ss()) []
QED

Theorem is_bit1b_finite[local]:
    FINITE (IS_BIT1B:'a bit1->bool) = FINITE (UNIV:'a->bool)
Proof
   REWRITE_TAC [is_bit1b_image]
   THEN MATCH_MP_TAC INJECTIVE_IMAGE_FINITE
   THEN SIMP_TAC (srw_ss()) []
QED

Theorem is_bit1a_card[local]:
    FINITE (UNIV:'a->bool) ==>
    (CARD (IS_BIT1A:'a bit1->bool) = CARD (UNIV:'a->bool))
Proof
   METIS_TAC [FINITE_BIJ_CARD_EQ, is_bit1a_finite, is_bit1a_bij]
QED

Theorem is_bit1b_card[local]:
    FINITE (UNIV:'a->bool) ==>
    (CARD (IS_BIT1B:'a bit1->bool) = CARD (UNIV:'a->bool))
Proof
   METIS_TAC [FINITE_BIJ_CARD_EQ, is_bit1b_finite, is_bit1b_bij]
QED

Theorem is_bit1a_is_bit1b_inter[local]:
    IS_BIT1A INTER IS_BIT1B = {}
Proof
   RW_TAC std_ss [INTER_DEF, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION]
   THEN Cases_on `x`
   THEN SIMP_TAC std_ss [IN_DEF, IS_BIT1A_def, IS_BIT1B_def, IS_BIT1C_def]
QED

Theorem IS_BIT1C_EQ_BIT1C[local]:
    !x. IS_BIT1C x = (x = BIT1C)
Proof
   Cases THEN SIMP_TAC (srw_ss()) [IS_BIT1C_def]
QED

Theorem is_bit1c_sing[local]:
    SING IS_BIT1C
Proof
   REWRITE_TAC [SING_DEF]
   THEN Q.EXISTS_TAC `BIT1C`
   THEN SIMP_TAC std_ss [FUN_EQ_THM, IS_BIT1C_EQ_BIT1C]
   THEN METIS_TAC [IN_SING, SPECIFICATION]
QED

val is_bit1c_finite_card = REWRITE_RULE [SING_IFF_CARD1] is_bit1c_sing

Theorem bit1_union_inter[local]:
    (IS_BIT1A UNION IS_BIT1B) INTER IS_BIT1C = {}
Proof
   RW_TAC std_ss [INTER_DEF, EXTENSION, NOT_IN_EMPTY, GSPECIFICATION, IN_UNION]
   THEN Cases_on `x`
   THEN SIMP_TAC std_ss [IN_DEF, IS_BIT1A_def, IS_BIT1B_def, IS_BIT1C_def]
QED

Theorem is_bit1a_is_bit1b_is_bit1c_union[local]:
    FINITE (UNIV:'a -> bool) ==>
    (CARD ((IS_BIT1A:'a bit1 -> bool) UNION (IS_BIT1B:'a bit1 -> bool) UNION
           (IS_BIT1C:'a bit1 -> bool)) =
     CARD (IS_BIT1A:'a bit1 -> bool) + CARD (IS_BIT1B:'a bit1 -> bool) + 1)
Proof
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
QED

Theorem index_bit1:
    dimindex(:('a bit1)) =
    if FINITE (UNIV:'a->bool) then 2 * dimindex(:'a) + 1 else 1
Proof
   RW_TAC std_ss [dimindex_def, bit1_union, is_bit1a_is_bit1b_is_bit1c_union,
                  FINITE_UNION]
   THEN METIS_TAC [is_bit1a_finite, is_bit1a_card, is_bit1c_finite_card,
                   is_bit1b_finite, is_bit1b_card, arithmeticTheory.TIMES2]
QED

Theorem finite_bit1:
    FINITE (UNIV:'a bit1->bool) = FINITE (UNIV:'a->bool)
Proof
   SIMP_TAC std_ss [FINITE_UNION, is_bit1a_finite, is_bit1b_finite,
                    is_bit1c_finite_card, bit1_union]
QED

(* Delete temporary constants *)

val () = List.app Theory.delete_const
            ["IS_BIT0A", "IS_BIT0B", "IS_BIT1A", "IS_BIT1B", "IS_BIT1C"]

(* ------------------------------------------------------------------------ *
 * one                                                                      *
 * ------------------------------------------------------------------------ *)

Theorem one_sing[local]:
    SING (UNIV:one->bool)
Proof
   REWRITE_TAC [SING_DEF]
   THEN Q.EXISTS_TAC `()`
   THEN SIMP_TAC std_ss [FUN_EQ_THM]
   THEN Cases
   THEN METIS_TAC [IN_SING, IN_UNIV, SPECIFICATION]
QED

val one_finite_card = REWRITE_RULE [SING_IFF_CARD1] one_sing

Theorem index_one:
    dimindex(:one) = 1
Proof METIS_TAC [dimindex_def, one_finite_card]
QED

Theorem finite_one = CONJUNCT2 one_finite_card

(* ------------------------------------------------------------------------ *
 * FCP update                                                               *
 * ------------------------------------------------------------------------ *)

val FCP_ss = rewrites [FCP_BETA, FCP_ETA, CART_EQ]

val () = set_fixity ":+" (Infixl 325)

Definition FCP_UPDATE_def[nocompute]:
  $:+ a b = \m:'a ** 'b. (FCP c. if a = c then b else m ' c):'a ** 'b
End

Theorem FCP_UPDATE_COMMUTES:
    !m a b c d. ~(a = b) ==> ((a :+ c) ((b :+ d) m) = (b :+ d) ((a :+ c) m))
Proof
   REPEAT strip_tac
   \\ rewrite_tac [FUN_EQ_THM]
   \\ srw_tac [FCP_ss] [FCP_UPDATE_def]
   \\ rw_tac std_ss []
QED

Theorem FCP_UPDATE_EQ:
    !m a b c. (a :+ c) ((a :+ b) m) = (a :+ c) m
Proof
   REPEAT strip_tac
   \\ rewrite_tac [FUN_EQ_THM]
   \\ srw_tac [FCP_ss] [FCP_UPDATE_def]
QED

Theorem FCP_UPDATE_IMP_ID:
    !m a v. (m ' a = v) ==> ((a :+ v) m = m)
Proof
   srw_tac [FCP_ss] [FCP_UPDATE_def]
   \\ rw_tac std_ss []
QED

Theorem APPLY_FCP_UPDATE_ID:
    !m a. (a :+ (m ' a)) m = m
Proof
   srw_tac [FCP_ss] [FCP_UPDATE_def]
QED

Theorem FCP_APPLY_UPDATE_THM:
   !(m:'a ** 'b) a w b. ((a :+ w) m) ' b =
       if b < dimindex(:'b) then
         if a = b then w else m ' b
       else
         FAIL (fcp_index) ^(mk_var("index out of range", bool)) ((a :+ w) m) b
Proof
  srw_tac [FCP_ss] [FCP_UPDATE_def, combinTheory.FAIL_THM]
QED

(* ------------------------------------------------------------------------ *
 * A collection of list related operations                                  *
 * ------------------------------------------------------------------------ *)

Definition FCP_HD_def:   FCP_HD v = v ' 0
End

Definition FCP_TL_def:   FCP_TL v = FCP i. v ' (SUC i)
End

Definition FCP_CONS_def:
   FCP_CONS h (v:'a ** 'b) = (0 :+ h) (FCP i. v ' (PRE i))
End

Definition FCP_MAP_def:
   FCP_MAP f (v:'a ** 'c) = (FCP i. f (v ' i)):'b ** 'c
End

Definition FCP_EXISTS_def[nocompute]:
   FCP_EXISTS P (v:'b ** 'a) = ?i. i < dimindex (:'a) /\ P (v ' i)
End

Definition FCP_EVERY_def[nocompute]:
   FCP_EVERY P (v:'b ** 'a) = !i. dimindex (:'a) <= i \/ P (v ' i)
End

Definition FCP_CONCAT_def :
   FCP_CONCAT (a:'a ** 'b) (b:'a ** 'c) =
   (FCP i. if i < dimindex(:'c) then
              b ' i
           else
              a ' (i - dimindex(:'c))): 'a ** ('b + 'c)
End

(* FCP_FST returns the "higher" dimensional part (:'a['b]) of ‘v :'a['b + 'c]’ *)
Definition FCP_FST_def :
   FCP_FST (v :'a ** ('b + 'c)) = (FCP i. v ' (i + dimindex (:'c))) :'a ** 'b
End

(* FCP_SND returns the "lower" dimensional part (:'a['c]) of ‘v :'a['b + 'c]’ *)
Definition FCP_SND_def :
   FCP_SND (v :'a ** ('b + 'c)) = (FCP i. v ' i) :'a ** 'c
End

Definition FCP_ZIP_def:
   FCP_ZIP (a:'a ** 'b) (b:'c ** 'b) = (FCP i. (a ' i, b ' i)): ('a # 'c) ** 'b
End

Definition V2L_def:   V2L (v:'a ** 'b) = GENLIST ($' v) (dimindex(:'b))
End

Definition L2V_def:   L2V L = FCP i. EL i L
End

Definition FCP_FOLD_def:   FCP_FOLD (f:'b -> 'a -> 'b) i v = FOLDL f i (V2L v)
End

(* Some theorems about these operations *)

Theorem LENGTH_V2L:
    !v. LENGTH (V2L (v:'a ** 'b)) = dimindex (:'b)
Proof
   rw [V2L_def]
QED

Theorem EL_V2L:
    !i v. i < dimindex (:'b) ==> (EL i (V2L v) = (v:'a ** 'b)  ' i)
Proof
   rw [V2L_def]
QED

Theorem FCP_MAP:
    !f v. FCP_MAP f v = L2V (MAP f (V2L v))
Proof
   srw_tac [FCP_ss] [FCP_MAP_def, V2L_def, L2V_def, listTheory.MAP_GENLIST]
QED

Theorem FCP_TL:
    !v. 1 < dimindex (:'b) /\ (dimindex(:'c) = dimindex(:'b) - 1) ==>
        (FCP_TL (v:'a ** 'b) = L2V (TL (V2L v)):'a ** 'c)
Proof
   REPEAT strip_tac
   \\ Cases_on `dimindex(:'b)`
   >- prove_tac [DECIDE ``1n < n ==> n <> 0``]
   \\ srw_tac [FCP_ss] [FCP_TL_def, V2L_def, L2V_def, listTheory.TL_GENLIST]
QED

Theorem FCP_EXISTS:
    !P v. FCP_EXISTS P v = EXISTS P (V2L v)
Proof
   rw [FCP_EXISTS_def, V2L_def, listTheory.EXISTS_GENLIST]
QED

Theorem FCP_EVERY:
    !P v. FCP_EVERY P v = EVERY P (V2L v)
Proof
   rw [FCP_EVERY_def, V2L_def, listTheory.EVERY_GENLIST]
   \\ metis_tac [arithmeticTheory.NOT_LESS]
QED

Theorem FCP_HD:
    !v. FCP_HD v = HD (V2L v)
Proof
   rw [FCP_HD_def, V2L_def, DIMINDEX_GE_1, listTheory.HD_GENLIST_COR,
       DIMINDEX_GT_0]
QED

Theorem FCP_CONS:
   !a v. FCP_CONS a (v:'a ** 'b) = L2V (a::V2L v):'a ** 'b + 1
Proof
  srw_tac [FCP_ss] [FCP_CONS_def, V2L_def, L2V_def, FCP_UPDATE_def]
  \\ pop_assum mp_tac
  \\ Cases_on `i`
  \\ lrw [index_sum, index_one, listTheory.EL_GENLIST]
QED

Theorem V2L_L2V:
    !x. (dimindex (:'b) = LENGTH x) ==> (V2L (L2V x:'a ** 'b) = x)
Proof
   rw [V2L_def, L2V_def, listTheory.LIST_EQ_REWRITE, FCP_BETA]
QED

Theorem NULL_V2L:
    !v. ~NULL (V2L v)
Proof
   rw [V2L_def, listTheory.NULL_GENLIST, DIMINDEX_NONZERO]
QED

Theorem READ_TL:
   !i a. i < dimindex (:'b) ==>
         (((FCP_TL a):'a ** 'b) ' i = (a:'a ** 'c) ' (SUC i))
Proof
  rw [FCP_TL_def, FCP_BETA]
QED

Theorem READ_L2V:
   !i a. i < dimindex (:'b) ==> ((L2V a:'a ** 'b) ' i = EL i a)
Proof
  rw [L2V_def, FCP_BETA]
QED

Theorem index_comp:
   !f n.
      (($FCP f):'a ** 'b) ' n =
      if n < dimindex (:'b) then
        f n
      else
        FAIL $' ^(mk_var("FCP out of bounds", bool))
             (($FCP f):'a ** 'b) n
Proof
  srw_tac [FCP_ss] [combinTheory.FAIL_THM]
QED

Theorem fcp_subst_comp:
   !a b f. (x :+ y) ($FCP f):'a ** 'b =
         ($FCP (\c. if x = c then y else f c)):'a ** 'b
Proof
  srw_tac [FCP_ss] [FCP_UPDATE_def]
QED

val () = computeLib.add_persistent_funs ["FCP_EXISTS", "FCP_EVERY"]

(* Connections between FCP_CONCAT, FCP_FST and FCP_SND *)
Theorem FCP_CONCAT_THM :
    !(a :'a['b]) (b :'a['c]).
        FINITE univ(:'b) /\ FINITE univ(:'c) ==>
       (FCP_FST (FCP_CONCAT a b) = a) /\ (FCP_SND (FCP_CONCAT a b) = b)
Proof
    RW_TAC std_ss [FCP_FST_def, FCP_SND_def]
 >| [ (* goal 1 (of 2) *)
      RW_TAC std_ss [CART_EQ, FCP_BETA] \\
      REWRITE_TAC [FCP_CONCAT_def, index_comp] >> simp [index_sum],
      (* goal 2 (of 2) *)
      RW_TAC std_ss [CART_EQ, FCP_BETA] \\
      REWRITE_TAC [FCP_CONCAT_def, index_comp] >> simp [index_sum] ]
QED

Theorem FCP_CONCAT_11 :
    !(a :'a['b]) (b :'a['c]) c d.
        FINITE univ(:'b) /\ FINITE univ(:'c) /\
       (FCP_CONCAT a b = FCP_CONCAT c d) ==> (a = c) /\ (b = d)
Proof
    rw [FCP_CONCAT_def, CART_EQ, index_sum, FCP_BETA] >> fs []
 >> qabbrev_tac ‘B = dimindex (:'b)’
 >> qabbrev_tac ‘C = dimindex (:'c)’
 >> ‘0 < B /\ 0 < C’ by rw [Abbr ‘B’, Abbr ‘C’]
 >| [ (* goal 1 (of 2) *)
      Q.PAT_X_ASSUM ‘!i. i < B + C ==> P’ (MP_TAC o Q.SPEC ‘i + C’) \\
     ‘C + i < dimindex(:'b + 'c)’ by rw [index_sum] \\
      simp [FCP_BETA],
      (* goal 2 (of 2) *)
      Q.PAT_X_ASSUM ‘!i. i < B + C ==> P’ (MP_TAC o Q.SPEC ‘i’) \\
     ‘i < dimindex(:'b + 'c)’ by rw [index_sum] \\
      simp [FCP_BETA] ]
QED

Theorem FCP_CONCAT_REDUCE :
    !(x :'a['b + 'c]). FINITE univ(:'b) /\ FINITE univ(:'c) ==>
                       FCP_CONCAT (FCP_FST x) (FCP_SND x) = x
Proof
    rw [FCP_CONCAT_def, FCP_FST_def, FCP_SND_def, CART_EQ]
 >> SRW_TAC [FCP_ss] []
 >> rfs [NOT_LESS, index_sum]
 >> ‘i - dimindex(:'c) < dimindex(:'b)’ by rw []
 >> SRW_TAC [FCP_ss] []
 >> ‘0 < dimindex(:'c)’ by PROVE_TAC [DIMINDEX_GT_0]
 >> rw []
QED

(* from HOL-Light's "Multivariate/vector.ml" *)
Theorem COND_COMPONENT :
    !b x y. (if b then x else y) ' i = if b then x ' i else y ' i
Proof
    PROVE_TAC []
QED

(* from HOL-Light's "Library/products.ml" *)
Theorem HAS_SIZE_CART :
    !P m. FINITE univ(:'N) /\
          (!i. i < dimindex(:'N) ==> {x | P i x} HAS_SIZE m i)
      ==> {v :'a['N] | !i. i < dimindex(:'N) ==> P i (v ' i)} HAS_SIZE
          nproduct {0 .. dimindex(:'N) - 1} m
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> qabbrev_tac ‘N = dimindex(:'N)’
 >> ‘0 < N’ by rw [Abbr ‘N’]
 >> Suff ‘!n. n < N  ==> {v:'a['N] | (!i. i < N /\ i <= n ==> P i (v ' i)) /\
                                     (!i. i < N /\ n < i ==> v ' i = ARB)}
                         HAS_SIZE nproduct {0 .. n} m’
 >- (DISCH_THEN (MP_TAC o Q.SPEC ‘N - 1’) \\
     simp [SUB_LESS_OR_EQ])
 >> INDUCT_TAC >> rw [NPRODUCT_CLAUSES_NUMSEG]
 >- (qabbrev_tac
      ‘s = {v:'a['N] | P 0 (v ' 0) /\ !i. i < N /\ 0 < i ==> v ' i = ARB}’ \\
     Know ‘s = IMAGE (\y. (FCP i. if i = 0 then y else ARB): 'a['N]) {x | P 0 x}’
     >- (rw [Once EXTENSION] \\
         EQ_TAC >> rw [FCP_BETA, Abbr ‘s’, CART_EQ] >| (* 3 subgoals *)
         [ (* goal 1 (of 3) *)
           Q.EXISTS_TAC ‘x ' 0’ >> rw [],
           (* goal 2 (of 3) *)
           Q.PAT_X_ASSUM ‘!i. i < N ==> x ' i = _’ (MP_TAC o Q.SPEC ‘0’) >> rw [],
           (* goal 3 (of 3) *)
           Q.PAT_X_ASSUM ‘!i. i < N ==> x ' i = _’ (MP_TAC o Q.SPEC ‘i’) >> rw [] ]) \\
     Rewr' \\
     MATCH_MP_TAC HAS_SIZE_IMAGE_INJ \\
     rw [CART_EQ, FCP_BETA] \\
     POP_ASSUM (MP_TAC o Q.SPEC ‘0’) >> rw [])
 (* stage work *)
 >> ‘n < N’ by rw [] >> FULL_SIMP_TAC std_ss []
 >> qabbrev_tac
     ‘s = {v:'a['N] |
           (!i. i < N /\ i <= SUC n ==> P i (v ' i)) /\
            !i. i < N /\ SUC n < i ==> v ' i = ARB}’
 >> qabbrev_tac ‘t = {(x,v) | x IN {x:'a | P (SUC n) x} /\
                              v IN {v:'a['N] | (!i. i < N /\ i <= n ==> P i (v ' i)) /\
                                               (!i. i < N /\ n < i ==> v ' i = ARB)}}’
 >> Know ‘s = IMAGE (\(x:'a,v:'a['N]). (FCP i. if i = SUC n then x else v ' i):'a['N]) t’
 >- (rw [Abbr ‘s’, Abbr ‘t’, Once EXTENSION] \\
     EQ_TAC >> rw [] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       Know ‘P (SUC n) ((x :'a['N]) ' (SUC n))’
       >- (FIRST_X_ASSUM MATCH_MP_TAC >> simp []) >> DISCH_TAC \\
       qabbrev_tac ‘y = x ' (SUC n)’ \\
       qabbrev_tac ‘v :'a['N] = FCP i. if i = SUC n then ARB else x ' i’ \\
       Q.EXISTS_TAC ‘(y,v)’ \\
       simp [CART_EQ, FCP_BETA, Abbr ‘y’, Abbr ‘v’] \\
       CONJ_TAC >- rw [] \\
       qabbrev_tac ‘v :'a['N] = FCP i. if i = SUC n then ARB else x ' i’ \\
       Q.EXISTS_TAC ‘v’ \\
       simp [CART_EQ, FCP_BETA, Abbr ‘v’],
       (* goal 2 (of 3) *)
       rename1 ‘P (SUC n) y’ \\
       simp [FCP_BETA] \\
       Cases_on ‘i = SUC n’ >> rw [],
       (* goal 3 (of 3) *)
       simp [FCP_BETA] ])
 >> Rewr'
 >> MATCH_MP_TAC HAS_SIZE_IMAGE_INJ
 >> rw []
 >- (gs [CART_EQ, FCP_BETA, Abbr ‘t’] \\
     CONJ_TAC >- (POP_ASSUM (MP_TAC o Q.SPEC ‘SUC n’) >> simp []) \\
     rw [] \\
     Cases_on ‘i = SUC n’ >- rw [] \\
     Q.PAT_X_ASSUM ‘!i. i < N ==> _’ (MP_TAC o Q.SPEC ‘i’) \\
     simp [])
 >> qunabbrev_tac ‘t’
 >> MATCH_MP_TAC HAS_SIZE_PRODUCT
 >> simp []
QED

Theorem CARD_CART :
    !P. FINITE univ(:'N) /\ (!i. i < dimindex(:'N) ==> FINITE {x | P i x}) ==>
        CARD {v :'a['N] | !i. i < dimindex(:'N) ==> P i (v ' i)} =
        nproduct {0 .. dimindex(:'N) - 1} (\i. CARD {x | P i x})
Proof
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(MESON[HAS_SIZE] “s HAS_SIZE n ==> CARD s = n”) THEN
  MATCH_MP_TAC HAS_SIZE_CART THEN
  simp[GSYM FINITE_HAS_SIZE]
QED

(* ----------------------------------------------------------------------
    More cardinality results for whole universe.
   ---------------------------------------------------------------------- *)

Theorem HAS_SIZE_CART_UNIV :
    !m. univ(:'a) HAS_SIZE m /\ FINITE univ(:'N) ==>
        univ(:'a['N]) HAS_SIZE m ** dimindex(:'N)
Proof
    Q.X_GEN_TAC ‘m’
 >> MP_TAC (Q.SPECL [‘\i x. T’, ‘\i. m’] HAS_SIZE_CART)
 >> rw []
 >> gs []
 >> qabbrev_tac ‘N = dimindex (:'N)’
 >> ‘0 < N’ by rw [Abbr ‘N’]
 >> qabbrev_tac ‘s = {0 .. N - 1}’
 >> Know ‘nproduct s (\i. m) = m ** CARD s’
 >- (MATCH_MP_TAC NPRODUCT_CONST >> rw [Abbr ‘s’, FINITE_NUMSEG])
 >> simp [Abbr ‘s’, CARD_NUMSEG]
 >> DISCH_THEN (art o wrap o SYM)
QED

Theorem CARD_CART_UNIV :
    FINITE univ(:'a) /\ FINITE univ(:'N) ==>
    CARD univ(:'a['N]) = CARD univ(:'a) ** dimindex(:'N)
Proof
  MESON_TAC[HAS_SIZE_CART_UNIV, HAS_SIZE]
QED

Theorem FINITE_CART_UNIV :
    FINITE univ(:'a) /\ FINITE univ(:'N) ==> FINITE univ(:'a['N])
Proof
  MESON_TAC[HAS_SIZE_CART_UNIV, HAS_SIZE]
QED
