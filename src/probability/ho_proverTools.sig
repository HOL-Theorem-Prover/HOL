signature ho_proverTools =
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

  (* types *)
  type factdb
  type fact_rule;

  (* Fact rules *)
  val no_frule : fact_rule
  val all_frule : fact_rule
  val empty_frule : fact_rule
  val orelse_frule : fact_rule * fact_rule -> fact_rule
  val then_frule : fact_rule * fact_rule -> fact_rule
  val try_frule : fact_rule -> fact_rule
  val join_frule : fact_rule * fact_rule -> fact_rule
  val repeat_frule : fact_rule -> fact_rule
  val joinl_frule : fact_rule list -> fact_rule
  val first_frule : fact_rule list -> fact_rule

  val fresh_vars_frule : fact_rule
  val rewrite_frule : vthm list -> fact_rule
  val once_rewrite_frule : vthm list -> fact_rule
  val basic_rewrite_frule : fact_rule
  val neg_frule : fact_rule
  val true_frule : fact_rule
  val false_frule : fact_rule
  val disj_frule : fact_rule
  val conj_frule : fact_rule
  val forall_frule : fact_rule
  val exists_frule : fact_rule
  val bool_frule : fact_rule
  val equal_frule : fact_rule
  val merge_frule : fact_rule
  val basic_cnf_frule : fact_rule
  val biresolution_frule : factdb -> fact_rule
  val k1_frule : fact_rule
  val s1_frule : fact_rule
  val equality_frule : fact_rule
  val paramodulation_frule : factdb -> fact_rule

  (* Fact databases *)
  val null_factdb : factdb
  val empty_factdb : factdb
  val factdb_size : factdb -> int
  val factdb_add_vthm : vthm -> factdb -> factdb
  val factdb_add_vthms : vthm list -> factdb -> factdb
  val factdb_add_thm : thm -> factdb -> factdb
  val factdb_add_thms : thm list -> factdb -> factdb
  val factdb_add_norm : fact_rule -> factdb -> factdb
  val mk_factdb : thm list -> factdb

  (* Entry points for tools *)
  val meson_refute_reduce_depth : factdb -> fact_rule -> int -> thm
  val meson_refute_reduce_deepen :
    factdb -> fact_rule -> int -> int -> int -> thm
  val meson_prove_reduce_depth :
    factdb -> fact_rule -> int -> vterm -> (substitution * vthm) list
  val ho_refute : factdb -> thm
  val ho_prove : factdb -> vterm -> (substitution * vthm) list

  (* Entry points for users *)
  val ho_PROVE_TAC : thm list -> tactic
  val ho_PROVE : thm list -> term -> thm

end

