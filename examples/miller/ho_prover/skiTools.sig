signature skiTools =
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

  (* Conversion to combinators {S,K,I} *)
  val SKI_CONV : conv

  (* ski term unification *)
  val ski_unify : vars -> term -> term -> substitution

  (* ski term discriminators *)
  type 'a ski_discrim
  val empty_ski_discrim : 'a ski_discrim
  val ski_discrim_size : 'a ski_discrim -> int
  val dest_ski_discrim : 'a ski_discrim -> (vterm * 'a) list
  val ski_discrim_add : vterm * 'a -> 'a ski_discrim -> 'a ski_discrim
  val ski_discrim_addl : (vterm * 'a) list -> 'a ski_discrim -> 'a ski_discrim
  val mk_ski_discrim : (vterm * 'a) list -> 'a ski_discrim
  val ski_discrim_match : 'a ski_discrim -> term -> (substitution * 'a) list
  val ski_discrim_unify : 'a ski_discrim -> vterm -> (substitution * 'a) list

end

