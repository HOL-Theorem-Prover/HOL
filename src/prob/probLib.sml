(* ========================================================================= *)
(* Bring in the entire development of "baby" probability theory.             *)
(*                                                                           *)
(*       Joe Hurd, University of Cambridge Computer Laboratory               *)
(*            (c) Copyright, University of Cambridge 2000                    *)
(* ========================================================================= *)


structure probLib :> probLib =
struct
  type term = Term.term
  type thm = Thm.thm

  local open prob_uniformTheory in end;

  open prob_canonTools boolean_sequenceTools prob_pseudoTools
       prob_uniformTools;

end;
