signature unifyTools =
sig

  (* Types *)
  type 'a thunk = 'a hurdUtils.thunk
  type hol_type = hurdUtils.hol_type
  type term = hurdUtils.term
  type thm = hurdUtils.thm
  type conv = hurdUtils.conv
  type rule = hurdUtils.rule
  type tactic = hurdUtils.tactic
  type thm_tactic = hurdUtils.thm_tactic
  type thm_tactical = hurdUtils.thm_tactical
  type vars = hurdUtils.vars
  type vterm = hurdUtils.vterm
  type type_subst = hurdUtils.type_subst
  type substitution = hurdUtils.substitution
  type raw_substitution = hurdUtils.raw_substitution
  type ho_substitution = hurdUtils.ho_substitution
  type ho_raw_substitution = hurdUtils.ho_raw_substitution

  (* type unification *)
  val var_type_unify : hol_type list -> hol_type -> hol_type -> type_subst
  val type_unify : hol_type -> hol_type -> type_subst
  val sep_var_type_unify :
    hol_type list * hol_type ->
    hol_type list * hol_type -> type_subst * type_subst
  val sep_type_unify : hol_type -> hol_type -> type_subst * type_subst

  (* term unification *)
  val unify_bvs : term list * term -> term list * term -> substitution
  val unify : term -> term -> substitution
  val var_unify : vars -> term -> term -> substitution
  val sep_var_unify : vterm -> vterm -> substitution * substitution
  val sep_unify : term -> term -> substitution * substitution

end

