(* ========================================================================= *)
(* Heuristic nonlinear arithmetic for reals (Phase 0).                       *)
(*                                                                           *)
(* Strategy: enrich hypothesis lists with square-nonneg and hypothesis-      *)
(* product theorems, then call the existing linear prover.                   *)
(*                                                                           *)
(*              (c) 2026, HOL4 contributors                                  *)
(* ========================================================================= *)

structure NLArith :> NLArith =
struct

open HolKernel boolLib liteLib

open RealArith0 RealArith RealField realSyntax

val ERR = mk_HOL_ERR "NLArith"

(* ------------------------------------------------------------------------- *)
(* Key theorems from realax theory.                                          *)
(* ------------------------------------------------------------------------- *)

(* |- !x. x * x >= &0 *)
val pth_square = DB.fetch "realax" "GEN_REAL_ARITH0_pth_square"

(* Nine conjuncts for multiplying (in)equalities:
   0: eq*eq  1: eq*ge  2: eq*gt  3: ge*eq
   4: ge*ge  5: ge*gt  6: gt*eq  7: gt*ge  8: gt*gt *)
val pth_mul_cjs =
  CONJUNCTS (DB.fetch "realax" "GEN_REAL_ARITH0_pth_mul")

val pth_ge_ge = List.nth(pth_mul_cjs, 4)  (* x>=0 /\ y>=0 ==> x*y>=0 *)
val pth_ge_gt = List.nth(pth_mul_cjs, 5)  (* x>=0 /\ y>0  ==> x*y>=0 *)
val pth_gt_ge = List.nth(pth_mul_cjs, 7)  (* x>0  /\ y>=0 ==> x*y>=0 *)
val pth_gt_gt = List.nth(pth_mul_cjs, 8)  (* x>0  /\ y>0  ==> x*y>0  *)

(* Polynomial normalization — uses the rational-coefficient versions
   from RealField so that enrichment theorems match the form produced
   by GEN_REAL_ARITH when called through RealField.GEN_REAL_ARITH. *)
val POLY_CONV     = RealField.REAL_POLY_CONV
val POLY_MUL_CONV = RealField.REAL_POLY_MUL_CONV

(* Maximum number of variables to consider for squaring *)
val max_sq_vars = 8

(* Maximum number of les hypotheses for pairwise products *)
val max_prod_les = 12

(* ------------------------------------------------------------------------- *)
(* Square generation: given t:real, return |- NORM(t * t) >= 0              *)
(* ------------------------------------------------------------------------- *)

fun mk_square_thm t =
  CONV_RULE (LAND_CONV POLY_CONV) (SPEC t pth_square)
  handle e => raise wrap_exn "NLArith" "mk_square_thm" e

(* ------------------------------------------------------------------------- *)
(* Product generation: given two (in)equality theorems, return product.      *)
(* Dispatches on the combination of >= and >.                                *)
(* Result: |- NORM(a * b) >= 0  or  |- NORM(a * b) > 0                      *)
(* ------------------------------------------------------------------------- *)

fun mk_product_thm th1 th2 =
  let
    val c1 = concl th1 and c2 = concl th2
    val is_ge1 = realSyntax.is_geq c1
    val is_gt1 = realSyntax.is_greater c1
    val is_ge2 = realSyntax.is_geq c2
    val is_gt2 = realSyntax.is_greater c2
    val pth =
      if is_ge1 andalso is_ge2 then pth_ge_ge
      else if is_ge1 andalso is_gt2 then pth_ge_gt
      else if is_gt1 andalso is_ge2 then pth_gt_ge
      else if is_gt1 andalso is_gt2 then pth_gt_gt
      else raise ERR "mk_product_thm" "unexpected inequality form"
    val th = MATCH_MP pth (CONJ th1 th2)
  in
    CONV_RULE (LAND_CONV POLY_MUL_CONV) th
  end

(* ------------------------------------------------------------------------- *)
(* Extract real-typed free variables from a list of terms.                   *)
(* Returns a deduplicated list, limited to max_sq_vars.                      *)
(* ------------------------------------------------------------------------- *)

fun real_free_vars tms =
  let
    val all_fvs = free_varsl tms
    val real_fvs = filter (fn v => type_of v = realSyntax.real_ty) all_fvs
    val deduped = op_mk_set aconv real_fvs
  in
    List.take(deduped, Int.min(length deduped, max_sq_vars))
  end

(* ------------------------------------------------------------------------- *)
(* Generate ordered pairs from a list.                                       *)
(* ------------------------------------------------------------------------- *)

fun ordered_pairs [] = []
  | ordered_pairs (x::xs) = map (fn y => (x,y)) xs @ ordered_pairs xs

(* ------------------------------------------------------------------------- *)
(* Enrichment: generate square-nonneg theorems for variables and their       *)
(* pairwise differences and sums.                                            *)
(* Returns: list of |- ... >= 0 theorems.                                    *)
(* Silently skips any that fail (e.g., type mismatch).                       *)
(* ------------------------------------------------------------------------- *)

fun enrich_squares vars =
  let
    (* Square each variable: |- v^2 >= 0 *)
    val sq_vars = mapfilter mk_square_thm vars
    (* Square differences: |- (vi - vj)^2 >= 0 *)
    val vp = ordered_pairs vars
    val sq_diffs = mapfilter
      (fn (x,y) => mk_square_thm (realSyntax.mk_minus(x,y))) vp
    (* Square sums: |- (vi + vj)^2 >= 0 *)
    val sq_sums = mapfilter
      (fn (x,y) => mk_square_thm (realSyntax.mk_plus(x,y))) vp
  in
    sq_vars @ sq_diffs @ sq_sums
  end

(* ------------------------------------------------------------------------- *)
(* Enrichment: generate pairwise products of les hypotheses.                 *)
(* Given [|- a>=0, |- b>=0, ...], produce [|- a*b>=0, ...].                 *)
(* Returns: list of new le theorems.                                         *)
(* ------------------------------------------------------------------------- *)

fun enrich_products les =
  let
    val les' = List.take(les, Int.min(length les, max_prod_les))
    val pairs = ordered_pairs les'
  in
    mapfilter (fn (a,b) => mk_product_thm a b) pairs
  end

(* Also generate products involving lts *)
fun enrich_cross_products les lts =
  let
    val les' = List.take(les, Int.min(length les, max_prod_les))
    val lts' = List.take(lts, Int.min(length lts, max_prod_les))
    (* le * lt → le *)
    val le_lt = mapfilter
      (fn le => mapfilter (fn lt => mk_product_thm le lt) lts') les'
      |> List.concat
    (* lt * lt → lt *)
    val lt_lt_pairs = ordered_pairs lts'
    val lt_lt = mapfilter (fn (a,b) => mk_product_thm a b) lt_lt_pairs
  in
    (le_lt, lt_lt)   (* (new les, new lts) *)
  end

(* ------------------------------------------------------------------------- *)
(* NLA_PROVER: drop-in replacement for REAL_LINEAR_PROVER.                   *)
(*                                                                           *)
(* Strategy:                                                                 *)
(*   1. Try linear prover directly.                                          *)
(*   2. Enrich with squares of variables/differences/sums and products       *)
(*      of les hypothesis pairs, then retry.                                 *)
(*   3. Also add cross-products (les * lts), retry.                          *)
(* ------------------------------------------------------------------------- *)

fun NLA_PROVER translator (eqs, les, lts) =
  (* Strategy 1: linear *)
  REAL_LINEAR_PROVER translator (eqs, les, lts)
  handle HOL_ERR _ =>
  let
    val all_polys = map (lhand o concl) (eqs @ les @ lts)
    val vars = real_free_vars all_polys
    val sq_thms = enrich_squares vars
    val prod_thms = enrich_products les
    val les1 = les @ sq_thms @ prod_thms
  in
    (* Strategy 2: squares + le*le products *)
    REAL_LINEAR_PROVER translator (eqs, les1, lts)
    handle HOL_ERR _ =>
    let
      (* Strategy 3: cross-products and le*sq products *)
      val sq_x_les = mapfilter
        (fn sq => mapfilter (fn le => mk_product_thm le sq) les) sq_thms
        |> List.concat
      val (cross_les, cross_lts) = enrich_cross_products les lts
      val les2 = les1 @ sq_x_les @ cross_les
      val lts2 = lts @ cross_lts
    in
      REAL_LINEAR_PROVER translator (eqs, les2, lts2)
    end
  end

(* ------------------------------------------------------------------------- *)
(* REAL_NLA: conversion that proves nonlinear real arithmetic goals.          *)
(* Like REAL_ARITH but handles squares, products, AM-GM style goals.         *)
(* ------------------------------------------------------------------------- *)

local
  val dec_conv = QCONV (ONCE_DEPTH_CONV (REWR_CONV markerTheory.unint_def))
  val core = RealField.GEN_REAL_ARITH NLA_PROVER
in
  fun REAL_NLA tm =
    let val th0 = dec_conv tm
        val tm0 = rhs (concl th0)
    in
      EQ_MP (SYM th0) (core tm0)
    end
end

(* ------------------------------------------------------------------------- *)
(* Tactic versions.                                                          *)
(* ------------------------------------------------------------------------- *)

val (NLA_TAC, NLA_ASM_TAC) = mk_real_arith_tac REAL_NLA

end (* structure NLArith *)
