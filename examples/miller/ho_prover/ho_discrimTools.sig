signature ho_discrimTools =
sig

  (* Types *)
  type 'a thunk = 'a ho_proverUseful.thunk
  type term = ho_proverUseful.term
  type thm = ho_proverUseful.thm
  type conv = ho_proverUseful.conv
  type rule = ho_proverUseful.rule
  type tactic = ho_proverUseful.tactic
  type thm_tactic = ho_proverUseful.thm_tactic
  type thm_tactical = ho_proverUseful.thm_tactical
  type vars = ho_proverUseful.vars
  type vterm = ho_proverUseful.vterm
  type substitution = ho_proverUseful.substitution
  type raw_substitution = ho_proverUseful.raw_substitution
  type ho_substitution = ho_proverUseful.ho_substitution
  type ho_raw_substitution = ho_proverUseful.ho_raw_substitution

  (* term discriminators *)
  type 'a discrim
  val empty_discrim : 'a discrim
  val discrim_size : 'a discrim -> int
  val dest_discrim : 'a discrim -> (term * 'a) list
  val discrim_add : term * 'a -> 'a discrim -> 'a discrim
  val mk_discrim : (term * 'a) list -> 'a discrim
  val discrim_ho_match : 'a discrim -> term -> (ho_substitution * 'a) list
  val discrim_fo_match : 'a discrim -> term -> (substitution * 'a) list

  (* vterm discriminators *)
  type 'a vdiscrim
  val empty_vdiscrim : 'a vdiscrim
  val vdiscrim_size : 'a vdiscrim -> int
  val dest_vdiscrim : 'a vdiscrim -> (vterm * 'a) list
  val vdiscrim_add : vterm * 'a -> 'a vdiscrim -> 'a vdiscrim
  val mk_vdiscrim : (vterm * 'a) list -> 'a vdiscrim
  val vdiscrim_ho_match : 'a vdiscrim -> term -> (ho_substitution * 'a) list
  val vdiscrim_fo_match : 'a vdiscrim -> term -> (substitution * 'a) list

  (* Ordered vterm discriminators *)
  type 'a ovdiscrim
  val empty_ovdiscrim : 'a ovdiscrim
  val ovdiscrim_size : 'a ovdiscrim -> int
  val dest_ovdiscrim : 'a ovdiscrim -> (vterm * 'a) list
  val ovdiscrim_add : vterm * 'a -> 'a ovdiscrim -> 'a ovdiscrim
  val mk_ovdiscrim : (vterm * 'a) list -> 'a ovdiscrim
  val ovdiscrim_ho_match : 'a ovdiscrim -> term -> (ho_substitution * 'a) list
  val ovdiscrim_fo_match : 'a ovdiscrim -> term -> (substitution * 'a) list

end

