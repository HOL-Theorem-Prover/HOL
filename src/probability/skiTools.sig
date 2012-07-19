signature skiTools =
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

