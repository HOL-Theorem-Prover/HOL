(* ---------------------------------------------------------------------*)
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
(* CONTENTS: functions for paired existential quantifications.          *)
(* ---------------------------------------------------------------------*)
(*$Id$*)

signature Pair_exists =
    sig
   type term  = Term.term
   type thm   = Thm.thm
   type goal  = Abbrev.goal
   type conv  = Abbrev.conv
   type tactic = Abbrev.tactic

	val PEXISTS_CONV : term -> thm
	val PSELECT_RULE : thm -> thm
	val PSELECT_CONV : term -> thm
	val PEXISTS_RULE : thm -> thm
	val PSELECT_INTRO : thm -> thm
	val PSELECT_ELIM : thm -> term * thm -> thm
	val PEXISTS : term * term -> thm -> thm
	val PCHOOSE : term * thm -> thm -> thm
	val P_PCHOOSE_THEN 
	  : term
	    -> (thm -> term list * term -> goal list * (thm list -> thm))
	       -> thm -> tactic
	val PCHOOSE_THEN 
	    : (thm -> term list * term -> goal list * (thm list -> thm))
               -> thm -> tactic
	val P_PCHOOSE_TAC : term -> thm -> tactic
	val PCHOOSE_TAC : thm -> tactic
	val PEXISTS_TAC : term -> tactic
	val PEXISTENCE : thm -> thm
	val PEXISTS_UNIQUE_CONV : term -> thm
	val P_PSKOLEM_CONV : term -> conv
	val PSKOLEM_CONV : term -> thm
end;
