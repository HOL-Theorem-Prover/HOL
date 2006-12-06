(* ========================================================================= *)
(* ELLIPTIC CURVE THEORY TOOLS                                               *)
(* ========================================================================= *)

structure ellipticTools :> ellipticTools =
struct

open HolKernel Parse boolLib bossLib fieldTools ellipticTheory;

(* ------------------------------------------------------------------------- *)
(* Syntax operations.                                                        *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Pretty printing.                                                          *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* AC normalization.                                                         *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Proof tools.                                                              *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Subtype context.                                                          *)
(* ------------------------------------------------------------------------- *)

val context = field_context;
val context = subtypeTools.add_reduction2 curve_field context;
val context = subtypeTools.add_reduction2 curve_a1_carrier context;
val context = subtypeTools.add_reduction2 curve_a2_carrier context;
val context = subtypeTools.add_reduction2 curve_a3_carrier context;
val context = subtypeTools.add_reduction2 curve_a4_carrier context;
val context = subtypeTools.add_reduction2 curve_a6_carrier context;
val context = subtypeTools.add_reduction2 curve_zero_carrier context;
val context = subtypeTools.add_reduction2 curve_neg_carrier context;
val context = subtypeTools.add_reduction2 curve_double_carrier context;
val context = subtypeTools.add_reduction2 curve_add_carrier context;
val context = subtypeTools.add_rewrite2 curve_double_zero context;
val context = subtypeTools.add_rewrite2 curve_add_lzero context;
val context = subtypeTools.add_rewrite2 curve_add_lneg context;
val context = subtypeTools.add_rewrite2 curve_add_rzero context;
val context = subtypeTools.add_rewrite2 curve_add_rneg context;
(***
val context = subtypeTools.add_reduction2 curve_group context;
val context = subtypeTools.add_rewrite2 example_prime_def context;
val context = subtypeTools.add_rewrite2 example_field_def context;
val context = subtypeTools.add_reduction2 example_curve context;
***)

val elliptic_context = context;

end
