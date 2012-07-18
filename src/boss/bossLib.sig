signature bossLib =
sig
  include Abbrev
  type ssfrag = simpLib.ssfrag
  type simpset = simpLib.simpset

  (* Make definitions *)

  (* new types *)
  val Hol_datatype : hol_type quotation -> unit

  (* new functions *)
  val Define       : term quotation -> thm
  val zDefine      : term quotation -> thm
  val xDefine      : string -> term quotation -> thm
  val tDefine      : string -> term quotation -> tactic -> thm
  val WF_REL_TAC   : term quotation -> tactic
  val Hol_defn     : string -> term quotation -> defn

  (* new (inductive) relations *)
  val Hol_reln     : term quotation -> thm * thm * thm
  val xHol_reln    : string -> term quotation -> thm * thm * thm
  val export_mono  : string -> unit

  (* Case-splitting and induction operations *)

  val Cases             : tactic
  val Induct            : tactic
  val recInduct         : thm -> tactic
  val Cases_on          : term quotation -> tactic
  val Induct_on         : term quotation -> tactic
  val PairCases_on      : term quotation -> tactic
  val measureInduct_on  : term quotation -> tactic
  val completeInduct_on : term quotation -> tactic
  val CASE_TAC          : tactic

  (* Proof automation *)

  val PROVE          : thm list -> term -> thm   (* First order *)
  val METIS_PROVE    : thm list -> term -> thm   (* First order *)
  val DECIDE         : term -> thm               (* Cooperating dec. procs *)
  val PROVE_TAC      : thm list -> tactic
  val METIS_TAC      : thm list -> tactic
  val DECIDE_TAC     : tactic

  (* Simplification *)

  val ++              : simpset * ssfrag -> simpset    (* infix *)
  val &&              : simpset * thm list -> simpset  (* infix *)
  val pure_ss         : simpset
  val bool_ss         : simpset
  val std_ss          : simpset           (* bool + option + pair + sum *)
  val arith_ss        : simpset
  val old_arith_ss    : simpset
  val list_ss         : simpset
  val srw_ss          : unit -> simpset
  val ARITH_ss        : ssfrag            (* arithmetic d.p. + some rewrites *)
  val old_ARITH_ss    : ssfrag
  val type_rws        : hol_type -> thm list
  val rewrites        : thm list -> ssfrag
  val augment_srw_ss  : ssfrag list -> unit
  val diminish_srw_ss : string list -> ssfrag list
  val export_rewrites : string list -> unit
  val limit           : int -> simpset -> simpset

  (* use these in simplifier's argument list *)
  val SimpLHS        : thm
  val SimpRHS        : thm
  val SimpL          : term -> thm
  val SimpR          : term -> thm

  val Cong           : thm -> thm
  val AC             : thm -> thm -> thm

  val SIMP_CONV         : simpset -> thm list -> conv
  val SIMP_RULE         : simpset -> thm list -> thm -> thm
  val SIMP_TAC          : simpset -> thm list -> tactic
  val ASM_SIMP_TAC      : simpset -> thm list -> tactic
  val FULL_SIMP_TAC     : simpset -> thm list -> tactic
  val REV_FULL_SIMP_TAC : simpset -> thm list -> tactic
  val RW_TAC            : simpset -> thm list -> tactic
  val SRW_TAC           : ssfrag list -> thm list -> tactic

  (* Call-by-value evaluation *)
  val EVAL           : term -> thm
  val EVAL_RULE      : thm -> thm
  val EVAL_TAC       : tactic

  (* Miscellaneous *)

  val ZAP_TAC        : simpset -> thm list -> tactic
  val SPOSE_NOT_THEN : (thm -> tactic) -> tactic
  val by             : term quotation * tactic -> tactic   (* infix *)
  val cheat          : tactic

  (* Abbreviations  (see also Q structure) *)

  val Abbr             : term quotation -> thm
  val UNABBREV_ALL_TAC : tactic
  val REABBREV_TAC     : tactic
  val WITHOUT_ABBREVS  : tactic -> tactic

end
