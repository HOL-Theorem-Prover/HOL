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
(* CONTENTS: Functions which are common to both paried universal and	*)
(*           existential quantifications and which rely on more		*)
(*           primitive functions from all.ml and exi.ml.		*)
(* ---------------------------------------------------------------------*)
(*$Id$*)

(* ------------------------------------------------------------------------- *)
(* Paired stripping tactics, same as basic ones, but they use PGEN_TAC       *)
(* and PCHOOSE_THEN rather than GEN_TAC and CHOOSE_THEN                      *)
(* ------------------------------------------------------------------------- *)

signature Pair_both2 =
    sig
   type term  = Term.term
   type thm   = Thm.thm
   type conv = Abbrev.conv
   type tactic = Abbrev.tactic
   type thm_tactic = Abbrev.thm_tactic
   type thm_tactical = Abbrev.thm_tactical

	val PSTRIP_THM_THEN : thm_tactical
	val PSTRIP_ASSUME_TAC : thm_tactic
	val PSTRUCT_CASES_TAC : thm_tactic
	val PSTRIP_GOAL_THEN : thm_tactic -> tactic
	val FILTER_PSTRIP_THEN : thm_tactic -> term -> tactic
	val PSTRIP_TAC : tactic
	val FILTER_PSTRIP_TAC : term -> tactic
	val PEXT : thm -> thm
	val P_FUN_EQ_CONV : term -> conv
	val MK_PABS : thm -> thm
	val HALF_MK_PABS : thm -> thm
	val MK_PFORALL : thm -> thm
	val MK_PEXISTS : thm -> thm
	val MK_PSELECT : thm -> thm
	val PFORALL_EQ : term -> thm -> thm
	val PEXISTS_EQ : term -> thm -> thm
	val PSELECT_EQ : term -> thm -> thm
	val LIST_MK_PFORALL : term list -> thm -> thm
	val LIST_MK_PEXISTS : term list -> thm -> thm
	val PEXISTS_IMP : term -> thm -> thm
	val SWAP_PFORALL_CONV : conv
	val SWAP_PEXISTS_CONV : conv
	val PART_PMATCH : (term -> term) -> thm -> term -> thm
	val PMATCH_MP_TAC : thm_tactic
	val PMATCH_MP : thm -> thm -> thm
    end;

