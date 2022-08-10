signature ho_basicTools =
sig

  (* Types *)
  type 'a thunk = 'a hurdUtils.thunk
  type term = hurdUtils.term
  type thm = hurdUtils.thm
  type conv = hurdUtils.conv
  type rule = hurdUtils.rule
  type tactic = hurdUtils.tactic
  type thm_tactic = hurdUtils.thm_tactic
  type thm_tactical = hurdUtils.thm_tactical
  type vars = hurdUtils.vars
  type substitution = hurdUtils.substitution
  type raw_substitution = hurdUtils.raw_substitution
  type ho_substitution = hurdUtils.ho_substitution
  type ho_raw_substitution = hurdUtils.ho_raw_substitution

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

