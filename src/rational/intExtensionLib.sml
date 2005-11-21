(***************************************************************************
 *
 *  intExtensionLib.sml
 *  
 *  Jens Brandt
 *  
 ***************************************************************************)

structure intExtensionLib :> intExtensionLib =
struct

open HolKernel boolLib Parse bossLib;

(* interactive mode
app load ["pairTheory", "pairLib", "integerTheory","intLib",
	"ringLib", "integerRingTheory","integerRingLib",
	"fracTheory","fracUtils", "intExtensionTheory"];
*)

open
	arithmeticTheory
	pairTheory pairLib integerTheory intLib
	ringLib integerRingTheory integerRingLib
	intExtensionTheory;

(*--------------------------------------------------------------------------
 *  INT_SGN_CASES_TAC: term -> tactic
 *
 *     A ?- P
 *   ========================  INT_SGN_CASES_TAC t1
 *     A, (SGN t1 = ~1) ?- P
 *     A, (SGN t1 =  0) ?- P
 *     A, (SGN t1 =  1) ?- P
 *--------------------------------------------------------------------------*)

val INT_SGN_CASES_TAC = fn term1 =>
	MATCH_MP_TAC (SPEC term1 INT_SGN_CASES) THEN REPEAT CONJ_TAC THEN STRIP_TAC
handle HOL_ERR _ => raise ERR "INT_SGN_CASES_TAC" "";

(*--------------------------------------------------------------------------
 *  INT_CALCEQ_TAC : tactic
 *--------------------------------------------------------------------------*)

val INT_CALCEQ_TAC =
	RW_TAC int_ss [] THEN
	INT_RING_TAC;

(*==========================================================================
 * end of structure
 *==========================================================================*)
end;
