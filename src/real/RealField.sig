(* ========================================================================= *)
(* Calculation with rational-valued reals. (HOL-Light's calc_rat.ml)         *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

signature RealField =
sig
   include Abbrev
   type positivstellensatz = RealArith.positivstellensatz

   (* One-step conversions for real operator with rational literals *)
  val REAL_RAT_LE_CONV     : conv
  val REAL_RAT_LT_CONV     : conv
  val REAL_RAT_GE_CONV     : conv
  val REAL_RAT_GT_CONV     : conv
  val REAL_RAT_EQ_CONV     : conv
  val REAL_RAT_SGN_CONV    : conv
  val REAL_RAT_NEG_CONV    : conv
  val REAL_RAT_ABS_CONV    : conv
  val REAL_RAT_INV_CONV    : conv
  val REAL_RAT_ADD_CONV    : conv
  val REAL_RAT_SUB_CONV    : conv
  val REAL_RAT_MUL_CONV    : conv
  val REAL_RAT_DIV_CONV    : conv
  val REAL_RAT_POW_CONV    : conv
  val REAL_RAT_MAX_CONV    : conv
  val REAL_RAT_MIN_CONV    : conv

   (* Deep reduce-based conversions for all real operators *)
  val REAL_RAT_REDUCE_CONV : conv

   (* Polynomial (semi-ring) conversions for real operators *)
  val REAL_POLY_NEG_CONV   : conv
  val REAL_POLY_ADD_CONV   : conv
  val REAL_POLY_SUB_CONV   : conv
  val REAL_POLY_MUL_CONV   : conv
  val REAL_POLY_POW_CONV   : conv
  val REAL_POLY_CONV       : conv

  val GEN_REAL_ARITH       :
     ((thm list * thm list * thm list -> positivstellensatz -> thm) ->
       thm list * thm list * thm list -> thm) -> term -> thm

   (* Final version of REAL_ARITH, etc. *)
  val REAL_ARITH           : term -> thm
  val REAL_ARITH_TAC       : tactic
  val REAL_ASM_ARITH_TAC   : tactic

   (* Basic ring and ideal conversions. *)
  val REAL_RING            : term -> thm
  val real_ideal_cofactors : term list -> term -> term list
  val REAL_IDEAL_CONV      : term list -> term -> thm

   (* A simple "field" rule. *)
  val REAL_FIELD           : term -> thm
  val REAL_FIELD_TAC       : tactic
  val REAL_ASM_FIELD_TAC   : tactic
end
