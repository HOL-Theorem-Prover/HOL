signature ho_basicTools =
sig

  (* Types *)
  type 'a thunk = 'a HurdUseful.thunk
  type term = HurdUseful.term
  type thm = HurdUseful.thm
  type conv = HurdUseful.conv
  type rule = HurdUseful.rule
  type tactic = HurdUseful.tactic
  type thm_tactic = HurdUseful.thm_tactic
  type thm_tactical = HurdUseful.thm_tactical
  type vars = HurdUseful.vars
  type substitution = HurdUseful.substitution
  type raw_substitution = HurdUseful.raw_substitution
  type ho_substitution = HurdUseful.ho_substitution
  type ho_raw_substitution = HurdUseful.ho_raw_substitution

  (* Simple higher-order patterns *)
  val dest_ho_pat : term list -> term -> term * int list
  val is_ho_pat : term list -> term -> bool
  val mk_ho_pat : term list -> term * int list -> term

  (* Matching *)
  val ho_pat_match : term list -> term list -> term -> term * thm thunk
  val ho_raw_match :
    term * int list ->
    term list * term -> raw_substitution -> ho_raw_substitution
  val fo_raw_match :
    term * int list -> term list * term -> raw_substitution -> raw_substitution

  val ho_match_bvs : term list * term -> term list * term -> ho_substitution
  val ho_match : term -> term -> ho_substitution
  val var_ho_match_bvs :
    vars -> term list * term -> term list * term -> ho_substitution
  val var_ho_match : vars -> term -> term -> ho_substitution

  (* Rewriting *)
  val ho_subst_REWR : thm -> ho_substitution -> thm
  val ho_REWR_CONV : thm -> conv
  val ho_REWRITE_CONV : thm list -> conv
  val ho_REWRITE_TAC : thm list -> tactic
  val ho_subst_COND_REWR : thm -> (term -> thm) -> ho_substitution -> thm
  val ho_COND_REWR_CONV : thm -> (term -> thm) -> term -> thm

end

