(* --------------------------------------------------------------------- *)
(* 		Copyright (c) Jim Grundy 1992				*)
(*									*)
(* Jim Grundy, hereafter referred to as "the Author', retains the	*)
(* copyright and all other legal rights to the Software contained in	*)
(* this file, hereafter referred to as "the Software'.			*)
(* 									*)
(* The Software is made available free of charge on an "as is' basis.	*)
(* No guarantee, either express or implied, of maintenance, reliability	*)
(* or suitability for any purpose is made by the Author.		*)
(* 									*)
(* The user is granted the right to make personal or internal use	*)
(* of the Software provided that both:					*)
(* 1. The Software is not used for commercial gain.			*)
(* 2. The user shall not hold the Author liable for any consequences	*)
(*    arising from use of the Software.					*)
(* 									*)
(* The user is granted the right to further distribute the Software	*)
(* provided that both:							*)
(* 1. The Software and this statement of rights is not modified.	*)
(* 2. The Software does not form part or the whole of a system 		*)
(*    distributed for commercial gain.					*)
(* 									*)
(* The user is granted the right to modify the Software for personal or	*)
(* internal use provided that all of the following conditions are	*)
(* observed:								*)
(* 1. The user does not distribute the modified software. 		*)
(* 2. The modified software is not used for commercial gain.		*)
(* 3. The Author retains all rights to the modified software.		*)
(*									*)
(* Anyone seeking a licence to use this software for commercial purposes*)
(* is invited to contact the Author.					*)
(* ---------------------------------------------------------------------*)
(* CONTENTS: functions for dealing with paired universal quantification.*)
(* ---------------------------------------------------------------------*)
(*$Id$*)

(* ------------------------------------------------------------------------- *)
(* Paired Specialisation:                                                    *)
(*    A |- !p.t                                                              *)
(*  ------------- PSPEC c [where c is free for p in t]                       *)
(*   A |- t[c/p]                                                             *)
(* ------------------------------------------------------------------------- *)

signature Pair_forall =
sig
   type term = Term.term
   type thm  = Thm.thm
   type tactic = Abbrev.tactic

	val PSPEC: term -> thm -> thm
	val PSPECL: term list -> thm -> thm
	val IPSPEC: term -> thm -> thm
	val IPSPECL: term list -> thm -> thm
	val PSPEC_PAIR: thm -> term * thm
	val PSPEC_ALL: thm -> thm
	val GPSPEC: thm -> thm
	val PSPEC_TAC: term * term -> tactic
	val PGEN: term -> thm -> thm
	val PGENL: term list -> thm -> thm
	val P_PGEN_TAC: term -> tactic
	val PGEN_TAC: tactic
	val FILTER_PGEN_TAC: term -> tactic
end;
