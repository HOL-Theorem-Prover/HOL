(* =====================================================================*)
(* FILE          : set_ind.sig                                          *)
(* DESCRIPTION   : Signature for an implementation of induction for     *)
(*                 sets. Translated from hol88.                         *)
(*                                                                      *)
(* Changes       : Oct. 1997, to abstract out the particular theorem    *)
(*                 -- this allows Set_ind to be compiled before being   *)
(*                 used in processing of setScript.                     *)
(* =====================================================================*)

signature Set_ind =
sig
   val SET_INDUCT_TAC : Thm.thm -> Abbrev.tactic
end;
