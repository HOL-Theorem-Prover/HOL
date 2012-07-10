signature subtypeTools =
sig

  (* Types *)
  type 'a thunk = 'a HurdUseful.thunk
  type hol_type = HurdUseful.hol_type
  type term = HurdUseful.term
  type thm = HurdUseful.thm
  type conv = HurdUseful.conv
  type rule = HurdUseful.rule
  type tactic = HurdUseful.tactic
  type thm_tactic = HurdUseful.thm_tactic
  type thm_tactical = HurdUseful.thm_tactical
  type vars = HurdUseful.vars
  type vterm = HurdUseful.vterm
  type vthm = HurdUseful.vthm
  type type_subst = HurdUseful.type_subst
  type substitution = HurdUseful.substitution
  type raw_substitution = HurdUseful.raw_substitution
  type ho_substitution = HurdUseful.ho_substitution
  type ho_raw_substitution = HurdUseful.ho_raw_substitution

  (* General *)
  val dest_in : term -> term * term
  val is_in : term -> bool
  val mk_subset : term * term -> term
  val dest_subset : term -> term * term
  val is_subset : term -> bool
  val term_to_vterm : term -> vterm

  (* SUBTYPE CHECKER *)

  (* Types *)
  type subtype_context
  datatype subtype_context_element =
    SC_SUBTYPE of thm
  | SC_SIMPLIFICATION of thm
  | SC_JUDGEMENT of thm

  (* Tuning parameters *)
  val cache_subtypes : bool ref
  val subtype_depth : int ref

  (* Subtype context operations *)
  val new_subtype_context : unit -> subtype_context
  val subtype_context_add_fact : vthm -> subtype_context -> subtype_context
  val subtype_context_add :
    subtype_context_element -> subtype_context -> subtype_context

  (* Entry points for tools *)
  val SUBTYPE_CHECK : bool -> int -> subtype_context -> term -> vthm list
  val SUBTYPE_MATCH :
    int -> subtype_context -> vterm -> (substitution * vthm) list
  val SUBTYPE_PROVE : int -> subtype_context -> term -> thm

  (* Entry points for users *)
  val SUBTYPE_CONV_DEPTH : int -> subtype_context -> conv
  val SUBTYPE_CONV : subtype_context -> conv
  val SUBTYPE_TAC : subtype_context -> tactic

  (* CONTEXTUAL REWRITER *)

  (* Types *)
  type context
  type c_rewr
  type c_rule
  datatype context_element =
    C_THM of thm
  | C_REWR of vterm * c_rewr
  | C_CONG of thm
  | C_RULE of vterm * c_rule
  | C_SUBTYPE of subtype_context_element
  | C_FORWARDS of thm

  (* Tuning parameters *)
  val simplify_max_traversals : int ref
  val simplify_max_depth : int ref
  val simplify_max_rewrites : int ref
  val simplify_subtype_depth : int ref
  val simplify_forwards : int ref

  (* Context operations *)
  val pattern_rewr : term * (conv -> (term -> thm) -> conv) -> vterm * c_rewr
  val pattern_rule : term * (vthm -> vthm list) -> vterm * c_rule
  val new_context : unit -> context
  val pp_context : ppstream -> context -> unit
  val context_subtypes : context -> subtype_context
  val context_add_fact : vthm -> context -> context
  val context_add_element : context_element -> context -> context
  val context_add_elements : context_element list -> context -> context

  (* Entry points for users *)
  (* just adds assumptions: useful for finding out what's going wrong *)
  val PRESIMPLIFY_TAC : context -> thm list -> tactic
  (* for general use: *)
  val SIMPLIFY_CONV : context -> conv
  val SIMPLIFY_TAC : context -> thm list -> tactic
  val ASM_SIMPLIFY_TAC : context -> thm list -> tactic
  (* slower but tries to prove every set membership subterm in the goal term: *)
  val SIMPLIFY_CONV' : context -> conv
  val SIMPLIFY_TAC' : context -> thm list -> tactic
  val ASM_SIMPLIFY_TAC' : context -> thm list -> tactic
  (* gives (SIMPLIFY_TAC, ASM_SIMPLIFY_TAC, SIMPLIFY_TAC', ASM_SIMPLIFY_TAC') *)
  val SIMPLIFY_TACS :
    context ->
    (thm list -> tactic) * (thm list -> tactic) *
    (thm list -> tactic) * (thm list -> tactic)

  (* CONTEXTUAL REWRITING MODULES *)

  (* Types *)
  type precontext

  (* Operations *)
  val empty_precontext : precontext
  val pp_precontext : ppstream -> precontext -> unit
  val precontext_add : string * context_element list -> precontext -> precontext
  val precontext_compile : precontext -> context
  val precontext_merge : precontext -> precontext -> precontext
  val precontext_mergel : precontext list -> precontext

end
