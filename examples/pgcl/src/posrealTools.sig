(* ========================================================================= *)
(* Tools for reasoning about positive reals (posreals).                      *)
(* ========================================================================= *)

signature posrealTools =
sig

  (* Case splitting posreals into finite and infinite *)
  val pcases    : Tactic.tactic
  val pcases_on : Term.term frag list -> Tactic.tactic

  (* Case splitting posreals into zero, finite non-zero and infinite *)
  val pcases3    : Tactic.tactic
  val pcases3_on : Term.term frag list -> Tactic.tactic

  (* Useful rewrites for basic posreal arithmetic *)
  val posreal_SS : simpLib.ssdata
  val posreal_ss : simpLib.simpset                (* real + posreal *)

  (* A calculator for rational posreals *)
  val posreal_reduce_SS : simpLib.ssdata
  val posreal_reduce_ss : simpLib.simpset         (* reduce + posreal_reduce *)

  (* AC normalizer for multiplication *)
  val permute_mul_conv : Abbrev.conv

end
