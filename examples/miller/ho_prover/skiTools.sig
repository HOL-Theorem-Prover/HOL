signature skiTools =
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

