structure ratRingLib :> ratRingLib =
struct

open HolKernel Parse boolLib;

(* interactive mode
app load ["ringLib","ratTheory","ratRingTheory","ratLib"]
*)

open ringLib ratTheory ratRingTheory ratSyntax ratLib;

(*--------------------------------------------------------------------------
 * is_computable_frac, is_computable_rat
 *--------------------------------------------------------------------------*)

fun is_computable_frac t =
	mem t [``frac_0``,``frac_1``] orelse
	((is_comb t) andalso (is_comb (rator t))) andalso
		let
			val rator_tm = rator (rator t);
			val nmr_tm = rand (rator t);
			val dnm_tm = rand t;
		in
			(rator_tm=``frac_save``) andalso (intSyntax.is_int_literal nmr_tm) andalso (numSyntax.is_numeral dnm_tm)
		end;

fun is_computable_rat t =
	mem t [``rat_0``,``rat_1``] orelse
	(* ((is_comb t) andalso (rator t)=``rat_of_num``) andalso (numSyntax.is_numeral (rand t)) orelse *)
	((is_comb t) andalso (rator t)=``abs_rat``) andalso (is_computable_frac (rand t));

(* test cases:
is_computable_rat ``abs_rat f1``
is_computable_rat ``abs_rat frac_1``
is_computable_rat ``abs_rat (abs_frac(3,4))``
is_computable_rat ``abs_rat (frac_save 3 3)``*)

(*--------------------------------------------------------------------------
 * ring declaration
 *--------------------------------------------------------------------------*)

val _ = ringLib.declare_ring
    { RingThm = rat_ring_thms,
      IsConst = is_computable_rat,
      Rewrites = (ratLib.int_rewrites @ ratLib.rat_rewrites) };

(*--------------------------------------------------------------------------
 * define ring conversions, tactics and rules
 *--------------------------------------------------------------------------*)

val PRE_CONV = RAT_PRECALC_CONV;
val POST_CONV = RAT_POSTCALC_CONV;

val RAT_RING_NORM_CONV = PRE_CONV THENC ringLib.RING_NORM_CONV THENC POST_CONV;
val RAT_RING_CONV = PRE_CONV THENC ringLib.RING_CONV THENC POST_CONV;

val RAT_RING_NORM_TAC = CONV_TAC RAT_RING_NORM_CONV;
val RAT_RING_TAC = CONV_TAC RAT_RING_CONV;

val RAT_RING_NORM_RULE = CONV_RULE RAT_RING_NORM_CONV;
val RAT_RING_RULE = CONV_RULE RAT_RING_CONV;

(*==========================================================================
 * end of structure
 *==========================================================================*)
end;
