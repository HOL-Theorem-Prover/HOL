signature BasicProvers =
sig
  include Abbrev
  type simpset = simpLib.simpset

  (* Eliminate v = M or M = v from hypotheses *)

  val VAR_EQ_TAC      : tactic

  (* First order automatic proof *)

  val PROVE           : thm list -> term -> thm
  val PROVE_TAC       : thm list -> tactic
  val GEN_PROVE_TAC   : int -> int -> int -> thm list -> tactic

  (* Simplification *)

  val bool_ss         : simpset
  val srw_ss          : unit -> simpset
  val Abbr            : term quotation -> thm
  val LEAVE_LETS      : thm

  val RW_TAC          : simpset -> thm list -> tactic
  val NORM_TAC        : simpset -> thm list -> tactic
  val SRW_TAC         : simpLib.ssfrag list -> thm list -> tactic
  val augment_srw_ss  : simpLib.ssfrag list -> unit
  val diminish_srw_ss : string list -> simpLib.ssfrag list
  val export_rewrites : string list -> unit
  val thy_ssfrag      : string -> simpLib.ssfrag

  (* LET manoeuvres *)
  val LET_ELIM_TAC    : tactic
  val new_let_thms    : thm list -> unit

  (* Compound automated reasoners. *)

  val PRIM_STP_TAC    : simpset -> tactic -> tactic
  val STP_TAC         : simpset -> tactic -> tactic

  (* Other reasoning support. *)
  val SPOSE_NOT_THEN    : (thm -> tactic) -> tactic

  val by                : term quotation * tactic -> tactic  (* infix *)
  val on                : (thm -> tactic) * (term quotation * tactic) -> tactic
                          (* infix *)

  datatype tmkind
      = Free of term
      | Bound of term list * term
      | Alien of term;

  val tmkind_tyof       : tmkind -> hol_type
  val prim_find_subterm : term list -> term -> goal -> tmkind
  val find_subterm      : term quotation -> goal -> tmkind
  val primInduct        : tmkind -> tactic -> tactic
  val Cases             : tactic
  val Induct            : tactic
  val Cases_on          : term quotation -> tactic
  val Induct_on         : term quotation -> tactic

  val PURE_TOP_CASE_TAC : tactic      (* The top-most case-split *)
  val PURE_CASE_TAC     : tactic      (* The smallest case-split *)
  val CASE_SIMP_CONV    : conv        (* The case rewrites in the typebase *)
  val CASE_TAC          : tactic      (* PURE_CASE_TAC THEN simplification *)

end
