signature BasicProvers =
sig
  include Abbrev
  type simpset = simpLib.simpset

  (* Eliminate v = M or M = v from hypotheses *)

  val VAR_EQ_TAC      : tactic
  val var_eq_tac      : tactic

  (* First order automatic proof *)

  val PROVE           : thm list -> term -> thm
  val PROVE_TAC       : thm list -> tactic
  val prove_tac       : thm list -> tactic
  val GEN_PROVE_TAC   : int -> int -> int -> thm list -> tactic

  (* Simplification *)

  val bool_ss         : simpset
  val srw_ss          : unit -> simpset
  val Abbr            : term quotation -> thm
  val LEAVE_LETS      : thm

  val RW_TAC          : simpset -> thm list -> tactic
  val rw_tac          : simpset -> thm list -> tactic
  val NORM_TAC        : simpset -> thm list -> tactic
  val PRIM_SRW_TAC    : simpset -> simpLib.ssfrag list -> thm list -> tactic
  val SRW_TAC         : simpLib.ssfrag list -> thm list -> tactic
  val srw_tac         : simpLib.ssfrag list -> thm list -> tactic
  val augment_srw_ss  : simpLib.ssfrag list -> unit
  val diminish_srw_ss : string list -> unit
  val export_rewrites : string list -> unit
  val delsimps        : string list -> unit
  val temp_delsimps   : string list -> unit
  val thy_ssfrag      : string -> simpLib.ssfrag
  val thy_simpset     : string -> simpset option
  val temp_setsimpset : simpset -> unit
  val merge_simpsets  : string list -> simpset
  datatype srw_update = ADD_SSFRAG of simpLib.ssfrag | REMOVE_RWT of string
  val simpset_state   : unit -> simpset * bool * srw_update list
  val logged_update   : {thyname : string} -> (simpset -> simpset) -> unit
  val logged_addfrags : {thyname : string} -> simpLib.ssfrag list -> unit
  val do_logged_updates : {theories : string list} -> unit
  val apply_logged_updates : {theories : string list} -> (simpset -> simpset)
  val augment_with_typebase : TypeBasePure.typeBase -> simpset -> simpset
  val temp_set_simpset_ancestry : string list -> unit
  val set_simpset_ancestry : string list -> unit
  val recreate_sset_at_parentage : string list -> unit

  (* update stateful simpset for duration of function call and then restore;
     has same locking guarantees as underlying AncestryData.with_temp_value *)
  val with_simpset_updates : (simpset -> simpset) -> ('a -> 'b) -> ('a -> 'b)
  val mk_tacmod : string -> Manager.tacmodifier

  val make_simpset_derived_value :
      (simpset -> 'a -> 'a) -> 'a -> {get : unit -> 'a, set : 'a -> unit}

  (* LET and Abbrev manoeuvres *)
  val LET_ELIM_TAC    : tactic
  val new_let_thms    : thm list -> unit
  val TIDY_ABBREVS    : tactic

  (* Compound automated reasoners. *)

  val PRIM_STP_TAC    : simpset -> tactic -> tactic
  val STP_TAC         : simpset -> tactic -> tactic

  (* Other reasoning support. *)
  val SPOSE_NOT_THEN    : (thm -> tactic) -> tactic
  val spose_not_then    : (thm -> tactic) -> tactic

  val by                : term quotation * tactic -> tactic  (* infix *)
  val byA               : term quotation * tactic -> tactic
  val suffices_by       : term quotation * tactic -> tactic  (* infix *)
  val on                : (thm -> tactic) * (term quotation * tactic) -> tactic
                          (* infix *)
  val subgoal           : term quotation -> tactic
  val sg                : term quotation -> tactic

  datatype tmkind
      = Free of term
      | Bound of term list * term
      | Alien of term

  val dest_tmkind       : tmkind -> term
  val prim_find_subterm : term list -> term -> goal -> tmkind
  val find_subterm      : term quotation -> goal -> tmkind
  val primInduct        : tmkind -> tactic -> tactic
  val Cases             : tactic
  val Induct            : tactic
  val namedCases        : string list -> tactic
  val update_induction  : thm -> unit

  val tmCases_on        : term -> string list -> tactic
  val Cases_on          : term quotation -> tactic
  val Induct_on         : term quotation -> tactic
  val namedCases_on     : term quotation -> string list -> tactic

  val PURE_TOP_CASE_TAC : tactic  (* top-most case-split *)
  val PURE_CASE_TAC     : tactic  (* smallest case-split (concl) *)
  val PURE_FULL_CASE_TAC: tactic  (* smallest case-split  (goal) *)

  val PURE_CASE_SIMP_CONV : thm list -> conv
  val CASE_SIMP_CONV    : conv     (* Apply case rewrites in theTypeBase *)

  val CASE_TAC          : tactic   (* PURE_CASE_TAC then simplification *)
  val TOP_CASE_TAC      : tactic   (* PURE_TOP_CASE_TAC then simplification *)
  val FULL_CASE_TAC     : tactic   (* PURE_FULL_CASE_TAC then simplification *)
  val full_case_tac     : tactic
  val EVERY_CASE_TAC    : tactic   (* Repeat FULL_CASE_TAC *)
  val every_case_tac    : tactic

end
