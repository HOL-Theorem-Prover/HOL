(* ===================================================================== *)
(* VERSION       : 1.0                                                   *)
(* FILE          : tactics.sml                                           *)
(* DESCRIPTION   : General purpose tactics for obj library.              *)
(*                                                                       *)
(* AUTHOR        : Peter Vincent Homeier                                 *)
(* DATE          : October 19, 2000                                      *)
(* COPYRIGHT     : Copyright (c) 2000 by Peter Vincent Homeier           *)
(*                                                                       *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* This file contains new tactics of general usefulness.                 *)
(* --------------------------------------------------------------------- *)

signature tactics =
sig

type term = Term.term
type thm = Thm.thm
type hol_type = Type.hol_type
type tactic  = Abbrev.tactic
type conv = Abbrev.conv
type thm_tactic = Abbrev.thm_tactic




val print_newline : unit -> unit
val print_theorem : thm -> unit
val print_terms : term list -> unit
val print_all_thm : thm -> unit
val print_theorems : thm list -> unit
val print_goal : (term list * term) -> unit

val print_theory_size : unit -> unit

val pthm : thm -> thm

val pairf : ('a -> 'b) -> ('c -> 'd) -> ('a * 'c) -> ('b * 'd)
val test : ('a -> 'b) -> 'a -> 'a
val try : ('a -> 'a) -> 'a -> 'a



val ONE_ONE_DEF : thm
val ONTO_DEF    : thm

(* These operators transform implications to collect antecedents into
  a single conjunction, or else to reverse this and spread them into
  a sequence of individual implications.  Each has type thm->thm.
*)

val AND2IMP : thm -> thm
val IMP2AND : thm -> thm

(*
val TACTIC_ERR{function,message} =
    Exception.mk_HOL_ERR "Tactic" function message
*)

val failwith : string -> 'a
val fail : unit -> 'a


(* Here are some useful tactics, that are not included in the standard HOL: *)

val PRINT_TAC : tactic
val POP_TAC : tactic
val ETA_TAC : term -> tactic
val EXT_TAC : term -> tactic
val CHECK_TAC : tactic
val FALSE_TAC : tactic
val MP_IMP_TAC : thm -> tactic
val UNASSUME_THEN : thm_tactic -> term -> tactic
val CONTRAPOS_TAC : tactic
val FORALL_EQ_TAC : tactic
val EXISTS_EQ_TAC : tactic
val EXISTS_VAR : (term * term) -> thm -> thm
val FIND_EXISTS_TAC : tactic
val UNBETA_TAC : term -> tactic

val UNDISCH_ALL_TAC : tactic
val UNDISCH_LAST_TAC : tactic
val DEFINE_NEW_VAR : term -> tactic

val LIST_INDUCT_TAC : tactic
val DOUBLE_LIST_INDUCT_TAC : tactic
val LENGTH_LIST_INDUCT_TAC : tactic
val FORALL_SYM_CONV : conv

val NOT_AP_TERM_TAC : term -> tactic

val APP_let_CONV : conv
val LIFT_let_TAC : tactic
val STRIP_let_TAC : tactic
val USE_IMP_EQ_matches
    : thm -> term -> (term * term) list * (hol_type * hol_type) list
val USE_IMP_matches
    : thm -> term -> (term * term) list * (hol_type * hol_type) list
val SUB_matches : (term -> 'a) -> term -> 'a
val ONCE_DEPTH_matches : (term -> 'a) -> term -> 'a
val ONCE_DEPTH_USE_IMP_EQ_matches
    : thm -> term -> (term * term) list * (hol_type * hol_type) list
val ONCE_DEPTH_USE_IMP_matches
    : thm -> term -> (term * term) list * (hol_type * hol_type) list
val USE_IMP_THEN : thm_tactic -> thm -> tactic
val USE_IMP_TAC : thm -> tactic
val USE_IMP_AND_THEN : thm_tactic -> thm -> tactic -> tactic
val USE_THEN : thm_tactic -> thm -> tactic
val USE_TAC : thm -> tactic
val USE_AND_THEN : thm_tactic -> thm -> tactic -> tactic

val RES2_THEN : thm_tactic -> tactic
val IMP_RES2_THEN : thm_tactic -> thm -> tactic
val IMP_RES_M_THEN : thm_tactic -> thm -> tactic
val RES_M_THEN : thm_tactic -> tactic

val REWRITE_THM : thm -> tactic
val ASM_REWRITE_THM : thm -> tactic
val ONCE_REWRITE_THM : thm -> tactic
val IMP_RES_REWRITE_TAC : thm -> tactic
val RES_REWRITE_TAC : tactic

val REWRITE_ASSUM_TAC : thm list -> tactic
val REWRITE_ALL_TAC : thm list -> tactic
val ASM_REWRITE_ALL_TAC : thm list -> tactic
val ONCE_REWRITE_ASSUM_TAC : thm list -> tactic
val ONCE_REWRITE_ALL_TAC : thm list -> tactic
val ONCE_ASM_REWRITE_ALL_TAC : thm list -> tactic

val REWRITE_ALL_THM : thm -> tactic
val ASM_REWRITE_ALL_THM : thm -> tactic
val ONCE_REWRITE_ALL_THM : thm -> tactic
val ONCE_ASM_REWRITE_ALL_THM : thm -> tactic

val UNIFY_VARS_TAC : tactic

val EVERY1 : tactic list -> tactic

end (* sig *)
