signature unifyTools =
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
  type type_subst = HurdUseful.type_subst
  type substitution = HurdUseful.substitution
  type raw_substitution = HurdUseful.raw_substitution
  type ho_substitution = HurdUseful.ho_substitution
  type ho_raw_substitution = HurdUseful.ho_raw_substitution

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

