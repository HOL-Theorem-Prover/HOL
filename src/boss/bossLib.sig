signature bossLib =
sig
  include Abbrev
  type ssdata = simpLib.ssdata
  type simpset = simpLib.simpset

  (* Make definitions *)

  val Hol_datatype : hol_type quotation -> unit
  val Define       : term quotation -> thm
  val xDefine      : string -> term quotation -> thm
  val Hol_defn     : string -> term quotation -> defn
  val Hol_reln     : term quotation -> thm * thm * thm
  val WF_REL_TAC   : term quotation -> tactic

  (* Case-splitting and induction operations *)

  val Cases             : tactic
  val Induct            : tactic
  val recInduct         : thm -> tactic
  val Cases_on          : term quotation -> tactic
  val Induct_on         : term quotation -> tactic
  val measureInduct_on  : term quotation -> tactic
  val completeInduct_on : term quotation -> tactic
  val CASE_TAC          : tactic

  (* Proof automation *)

  val PROVE          : thm list -> term -> thm   (* First order *)
  val DECIDE         : term -> thm               (* Cooperating dec. procs *)
  val PROVE_TAC      : thm list -> tactic
  val DECIDE_TAC     : tactic

  (* Simplification *)

  val ++             : simpset * ssdata -> simpset    (* infix *)
  val &&             : simpset * thm list -> simpset  (* infix *)
  val pure_ss        : simpset
  val bool_ss        : simpset
  val std_ss         : simpset           (* bool + option + pair + sum *)
  val arith_ss       : simpset
  val list_ss        : simpset
  val srw_ss         : unit -> simpset
  val ARITH_ss       : ssdata            (* arithmetic d.p. + some rewrites *)
  val type_rws       : string -> thm list
  val rewrites       : thm list -> ssdata
  val augment_srw_ss : ssdata list -> unit

  val Cong           : thm -> thm
  val AC             : thm -> thm -> thm

  val SIMP_CONV      : simpset -> thm list -> conv
  val SIMP_RULE      : simpset -> thm list -> thm -> thm
  val SIMP_TAC       : simpset -> thm list -> tactic
  val ASM_SIMP_TAC   : simpset -> thm list -> tactic
  val FULL_SIMP_TAC  : simpset -> thm list -> tactic
  val RW_TAC         : simpset -> thm list -> tactic
  val SRW_TAC        : ssdata list -> thm list -> tactic

  val EVAL           : term -> thm   (* Call-by-value evaluation *)
  val EVAL_RULE      : thm -> thm
  val EVAL_TAC       : tactic

  (* Miscellaneous *)

  val ZAP_TAC        : simpset -> thm list -> tactic
  val SPOSE_NOT_THEN : (thm -> tactic) -> tactic
  val by             : term quotation * tactic -> tactic   (* infix *)

end
