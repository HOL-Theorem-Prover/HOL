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


signature Rewrite =
sig

type rewrites
val mk_rewrites : Thm.thm -> Thm.thm list
val add_rewrites : rewrites -> Thm.thm list -> rewrites
val dest_rewrites : rewrites -> Thm.thm list
val empty_rewrites : rewrites

val implicit_rewrites : unit -> rewrites
val set_implicit_rewrites : rewrites -> unit
val add_implicit_rewrites : Thm.thm list -> unit

val pp_rewrites : Portable_PrettyPrint.ppstream -> rewrites -> unit
val bool_rewrites : rewrites

val REWRITES_CONV : rewrites -> Abbrev.conv
val GEN_REWRITE_CONV : (Abbrev.conv -> Abbrev.conv)
                         -> rewrites -> Thm.thm list -> Abbrev.conv
val GEN_REWRITE_RULE : (Abbrev.conv -> Abbrev.conv) 
                         -> rewrites -> Thm.thm list -> Thm.thm -> Thm.thm
val GEN_REWRITE_TAC : (Abbrev.conv -> Abbrev.conv) 
                        -> rewrites -> Thm.thm list -> Abbrev.tactic

val PURE_REWRITE_CONV : Thm.thm list -> Abbrev.conv
val REWRITE_CONV : Thm.thm list -> Abbrev.conv
val PURE_ONCE_REWRITE_CONV : Thm.thm list -> Abbrev.conv
val ONCE_REWRITE_CONV : Thm.thm list -> Abbrev.conv

val PURE_REWRITE_RULE : Thm.thm list -> Thm.thm -> Thm.thm
val REWRITE_RULE : Thm.thm list -> Thm.thm -> Thm.thm
val PURE_ONCE_REWRITE_RULE : Thm.thm list -> Thm.thm -> Thm.thm
val ONCE_REWRITE_RULE : Thm.thm list -> Thm.thm -> Thm.thm
val PURE_ASM_REWRITE_RULE : Thm.thm list -> Thm.thm -> Thm.thm
val ASM_REWRITE_RULE : Thm.thm list -> Thm.thm -> Thm.thm
val PURE_ONCE_ASM_REWRITE_RULE : Thm.thm list -> Thm.thm -> Thm.thm
val ONCE_ASM_REWRITE_RULE : Thm.thm list -> Thm.thm -> Thm.thm

val PURE_REWRITE_TAC : Thm.thm list -> Abbrev.tactic
val REWRITE_TAC : Thm.thm list -> Abbrev.tactic
val PURE_ONCE_REWRITE_TAC : Thm.thm list -> Abbrev.tactic
val ONCE_REWRITE_TAC : Thm.thm list -> Abbrev.tactic
val PURE_ASM_REWRITE_TAC : Thm.thm list -> Abbrev.tactic
val ASM_REWRITE_TAC : Thm.thm list -> Abbrev.tactic
val PURE_ONCE_ASM_REWRITE_TAC : Thm.thm list -> Abbrev.tactic
val ONCE_ASM_REWRITE_TAC : Thm.thm list -> Abbrev.tactic

val FILTER_PURE_ASM_REWRITE_RULE 
    :(Term.term -> bool) -> Thm.thm list -> Thm.thm -> Thm.thm
val FILTER_ASM_REWRITE_RULE 
    :(Term.term -> bool) -> Thm.thm list -> Thm.thm -> Thm.thm
val FILTER_PURE_ONCE_ASM_REWRITE_RULE 
    :(Term.term -> bool) -> Thm.thm list -> Thm.thm -> Thm.thm
val FILTER_ONCE_ASM_REWRITE_RULE 
    :(Term.term -> bool) -> Thm.thm list -> Thm.thm -> Thm.thm
val FILTER_PURE_ASM_REWRITE_TAC 
    :(Term.term -> bool) -> Thm.thm list -> Abbrev.tactic 
val FILTER_ASM_REWRITE_TAC 
    :(Term.term -> bool) -> Thm.thm list -> Abbrev.tactic
val FILTER_PURE_ONCE_ASM_REWRITE_TAC 
    :(Term.term -> bool) -> Thm.thm list -> Abbrev.tactic
val FILTER_ONCE_ASM_REWRITE_TAC 
    :(Term.term -> bool) -> Thm.thm list -> Abbrev.tactic

val SUBST_MATCH : Thm.thm -> Thm.thm -> Thm.thm
end;
