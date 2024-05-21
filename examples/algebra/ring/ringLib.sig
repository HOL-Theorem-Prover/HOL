(* ========================================================================= *)
(*  A decision procedure for the universal theory of rings                   *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(* ========================================================================= *)

signature ringLib =
sig

  include Abbrev

  val RING_RULE : term -> thm
  val RING_TAC  : tactic
end
