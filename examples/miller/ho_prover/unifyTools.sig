signature unifyTools =
sig

  (* Types *)
  type 'a thunk = 'a ho_proverUseful.thunk
  type hol_type = ho_proverUseful.hol_type
  type term = ho_proverUseful.term
  type thm = ho_proverUseful.thm
  type conv = ho_proverUseful.conv
  type rule = ho_proverUseful.rule
  type tactic = ho_proverUseful.tactic
  type thm_tactic = ho_proverUseful.thm_tactic
  type thm_tactical = ho_proverUseful.thm_tactical
  type vars = ho_proverUseful.vars
  type vterm = ho_proverUseful.vterm
  type type_subst = ho_proverUseful.type_subst
  type substitution = ho_proverUseful.substitution
  type raw_substitution = ho_proverUseful.raw_substitution
  type ho_substitution = ho_proverUseful.ho_substitution
  type ho_raw_substitution = ho_proverUseful.ho_raw_substitution

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

