(* ===================================================================== *)
(* FILE          : rewrite.sig                                           *)
(* DESCRIPTION   : Signature for the rewriting routines. Translated from *)
(*                 hol88.                                                *)
(*                                                                       *)
(* AUTHOR        : (c) Larry Paulson, University of Cambridge, for hol88 *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* REVISED       : November 1994, to encapsulate the type of rewrite     *)
(*                 rules. (KLS)                                          *)
(* ===================================================================== *)


signature Rewrite0 =
sig

type term = Term.term
type thm = Thm.thm
type conv = Abbrev.conv;
type tactic = Abbrev.tactic;

type rewrites
val mk_rewrites    : thm -> thm list
val add_rewrites   : rewrites -> thm list -> rewrites
val dest_rewrites  : rewrites -> thm list
val net_of         : rewrites -> conv Net.net
val empty_rewrites : rewrites

val implicit_rewrites     : unit -> rewrites
val set_implicit_rewrites : rewrites -> unit
val add_implicit_rewrites : thm list -> unit

val pp_rewrites   : Portable.ppstream -> rewrites -> unit
val bool_rewrites : rewrites
val monitoring    : bool ref

val REWRITES_CONV    : rewrites -> conv
val GEN_REWRITE_CONV : (conv -> conv) -> rewrites -> thm list -> conv
val GEN_REWRITE_RULE : (conv -> conv) -> rewrites -> thm list -> thm -> thm
val GEN_REWRITE_TAC  : (conv -> conv) -> rewrites -> thm list -> tactic

val REWRITE_CONV      : thm list -> conv
val PURE_REWRITE_CONV : thm list -> conv
val ONCE_REWRITE_CONV : thm list -> conv
val PURE_ONCE_REWRITE_CONV : thm list -> conv

val PURE_REWRITE_RULE : thm list -> thm -> thm
val REWRITE_RULE : thm list -> thm -> thm
val PURE_ONCE_REWRITE_RULE : thm list -> thm -> thm
val ONCE_REWRITE_RULE : thm list -> thm -> thm
val PURE_ASM_REWRITE_RULE : thm list -> thm -> thm
val ASM_REWRITE_RULE : thm list -> thm -> thm
val PURE_ONCE_ASM_REWRITE_RULE : thm list -> thm -> thm
val ONCE_ASM_REWRITE_RULE : thm list -> thm -> thm

val PURE_REWRITE_TAC : thm list -> tactic
val REWRITE_TAC : thm list -> tactic
val PURE_ONCE_REWRITE_TAC : thm list -> tactic
val ONCE_REWRITE_TAC : thm list -> tactic
val PURE_ASM_REWRITE_TAC : thm list -> tactic
val ASM_REWRITE_TAC : thm list -> tactic
val PURE_ONCE_ASM_REWRITE_TAC : thm list -> tactic
val ONCE_ASM_REWRITE_TAC : thm list -> tactic

val FILTER_PURE_ASM_REWRITE_RULE :(term -> bool) -> thm list -> thm -> thm
val FILTER_ASM_REWRITE_RULE :(term -> bool) -> thm list -> thm -> thm
val FILTER_PURE_ONCE_ASM_REWRITE_RULE :(term -> bool) -> thm list -> thm -> thm
val FILTER_ONCE_ASM_REWRITE_RULE :(term -> bool) -> thm list -> thm -> thm
val FILTER_PURE_ASM_REWRITE_TAC :(term -> bool) -> thm list -> tactic 
val FILTER_ASM_REWRITE_TAC :(term -> bool) -> thm list -> tactic
val FILTER_PURE_ONCE_ASM_REWRITE_TAC :(term -> bool) -> thm list -> tactic
val FILTER_ONCE_ASM_REWRITE_TAC :(term -> bool) -> thm list -> tactic

val SUBST_MATCH : thm -> thm -> thm
end;
