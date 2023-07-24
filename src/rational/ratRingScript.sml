(***************************************************************************
 *
 *  Theory of ring properties of rational numbers.
 *
 *  Jens Brandt, November 2005
 *
 ***************************************************************************)

open HolKernel boolLib Parse bossLib;

(* interactive mode
app load [
        "integerTheory", "ratTheory", "ringLib", "schneiderUtils";
*)

open
        integerTheory ratTheory EVAL_ringLib schneiderUtils;

val _ = new_theory "ratRing";

(*--------------------------------------------------------------------------
 *  RAT_IS_RING: thm
 *  |- is_ring (ring rat_0 rat_1 rat_add rat_mul rat_ainv)
 *--------------------------------------------------------------------------*)

Theorem RAT_IS_RING: is_ring (ring 0q 1q rat_add rat_mul rat_ainv)
Proof
  RW_TAC intLib.int_ss[
      EVAL_ringTheory.is_ring_def, EVAL_ringTheory.ring_accessors,
      RAT_ADD_ASSOC, RAT_MUL_ASSOC,
      RAT_ADD_LID, RAT_MUL_LID,
      RAT_ADD_RINV,
      RAT_RDISTRIB] THEN
  MAP_FIRST MATCH_ACCEPT_TAC [
      RAT_ADD_COMM, RAT_MUL_COMM
    ]
QED

val rat_ring_thms =
  EVAL_ringLib.store_ring { Name = "rat", Theory = RAT_IS_RING };

(*==========================================================================
 * end of theory
 *==========================================================================*)

val _ = export_theory();
