signature vars_as_resourceSyntax =
sig

include Abbrev;

val VAR_RES_COND_HOARE_TRIPLE_term : term
val VAR_RES_FRAME_SPLIT_term : term
val VAR_RES_HOARE_TRIPLE_term : term
val VAR_RES_IS_PURE_PROPOSITION_term : term
val VAR_RES_IS_STACK_IMPRECISE___USED_VARS_term : term
val VAR_RES_IS_STACK_IMPRECISE_term : term
val VAR_RES_PROP_IS_EQUIV_FALSE_term : term
val var_res_best_local_action_term : term
val var_res_bool_proposition_term : term
val var_res_cond_best_local_action_term : term
val var_res_exp_binop_term : term
val var_res_exp_const_term : term
val var_res_exp_var_term : term
val var_res_exp_varlist_update_term : term
val var_res_implies_unequal_term : term
val var_res_mk_call_by_value_arg : (term * term) * term -> term
val var_res_mk_local_var : term * term -> term
val var_res_pred_bin_term : term;
val var_res_prog_aquire_lock_input_term : term
val var_res_prog_aquire_lock_internal_term : term
val var_res_prog_aquire_lock_term : term
val var_res_prog_assign_term : term
val var_res_prog_best_local_action_term : term
val var_res_prog_call_by_value_arg_term : term
val var_res_prog_cond_best_local_action_term : term
val var_res_prog_eval_expressions_term : term
val var_res_prog_local_var_term : term
val var_res_prog_parallel_procedure_call_term : term
val var_res_prog_procedure_call_term : term
val var_res_prog_quant_best_local_action_term : term
val var_res_prog_release_lock_input_term : term
val var_res_prog_release_lock_internal_term : term
val var_res_prog_release_lock_term : term
val var_res_prop___var_eq_const_BAG_term : term
val var_res_prop_binexpression_cond_term : term
val var_res_prop_binexpression_term : term
val var_res_prop_equal_term : term
val var_res_prop_implies_eq_term : term
val var_res_prop_implies_term : term
val var_res_prop_input_ap_distinct_term : term
val var_res_prop_input_ap_term : term
val var_res_prop_input_distinct_term : term
val var_res_prop_internal_term : term
val var_res_prop_stack_true_term : term
val var_res_prop_term : term
val var_res_prop_unequal_term : term
val var_res_prop_varlist_update_term : term
val var_res_strip_local_vars : term -> (term * term option) list * term

val dest_VAR_RES_COND_HOARE_TRIPLE : term -> term * term * term * term
val dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND : term -> term * term * term * term * term
val dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND_location : term -> term * term option * term * term * term * (unit -> thm)
val VAR_RES_COND_HOARE_TRIPLE___location_inc_CONV : conv
val dest_VAR_RES_FRAME_SPLIT : term -> term * term * term * term * term * term * term * term
val dest_VAR_RES_HOARE_TRIPLE : term -> term * term * term * term * term
val dest_VAR_RES_IS_PURE_PROPOSITION : term -> term * term
val dest_VAR_RES_IS_STACK_IMPRECISE : term -> term
val dest_VAR_RES_IS_STACK_IMPRECISE___USED_VARS : term -> term * term
val dest_VAR_RES_PROP_IS_EQUIV_FALSE : term -> term * term * term * term
val dest_var_res_best_local_action : term -> term * term * term
val dest_var_res_bool_proposition : term -> term * term
val dest_var_res_cond_best_local_action : term -> term * term * term
val dest_var_res_cond_proposition : hol_type -> hol_type
val dest_var_res_exp_binop : term -> term * term
val dest_var_res_exp_const : term -> term
val dest_var_res_exp_var : term -> term
val dest_var_res_exp_varlist_update : term -> term * term
val dest_var_res_expr_type : hol_type -> hol_type * hol_type;
val dest_var_res_ext_state_type : hol_type -> hol_type * hol_type;
val dest_var_res_implies_unequal : term -> term * term * term * term
val dest_var_res_prog_aquire_lock : term -> term * term * term * term
val dest_var_res_prog_aquire_lock_input : term -> term * term * term * term
val dest_var_res_prog_aquire_lock_internal : term -> term * term * term * term
val dest_var_res_prog_assign : term -> term * term
val dest_var_res_prog_best_local_action : term -> term * term
val dest_var_res_prog_call_by_value_arg : term -> term * term * term
val dest_var_res_prog_cond_best_local_action : term -> term * term
val dest_var_res_prog_eval_expressions : term -> term * term
val dest_var_res_prog_local_var : term -> term * term
val dest_var_res_prog_parallel_procedure_call : term -> term * term * term * term
val dest_var_res_prog_procedure_call : term -> term * term
val dest_var_res_prog_quant_best_local_action : term -> term * term
val dest_var_res_prog_release_lock : term -> term * term * term
val dest_var_res_prog_release_lock_input : term -> term * term * term
val dest_var_res_prog_release_lock_internal : term -> term * term * term
val dest_var_res_prop : term -> term * term * term * term
val dest_var_res_prop___propL : term -> term * term * term * term * term list
val dest_var_res_prop_binexpression : term -> term * term * term * term * term
val dest_var_res_prop_binexpression_cond : term -> term * term * term * term * term * term
val dest_var_res_prop_equal : term -> term * term * term
val dest_var_res_prop_implies : term -> term * term * term * term * term
val dest_var_res_prop_implies_eq : term -> term * term * term * term * term * term
val dest_var_res_prop_input_ap_distinct : term -> term * term * term * term;
val dest_var_res_prop_input_distinct : term -> term * term * term * term;
val dest_var_res_prop_internal : term -> term * term * term * term * term * term * term * term
val dest_var_res_prop_stack_true : term -> term
val dest_var_res_prop_unequal : term -> term * term * term
val dest_var_res_prop_varlist_update : term -> term * term
val dest_var_res_proposition : hol_type -> hol_type
val dest_var_res_state_type : hol_type -> hol_type * hol_type;
val is_VAR_RES_COND_HOARE_TRIPLE : term -> bool
val is_VAR_RES_FRAME_SPLIT : term -> bool
val is_VAR_RES_HOARE_TRIPLE : term -> bool
val is_VAR_RES_IS_PURE_PROPOSITION : term -> bool
val is_VAR_RES_IS_STACK_IMPRECISE : term -> bool
val is_VAR_RES_IS_STACK_IMPRECISE___USED_VARS : term -> bool
val is_VAR_RES_PROP_IS_EQUIV_FALSE : term -> bool
val is_var_res_best_local_action : term -> bool
val is_var_res_bool_proposition : term -> bool
val is_var_res_cond_best_local_action : term -> bool
val is_var_res_exp_binop : term -> bool
val is_var_res_exp_const : term -> bool
val is_var_res_exp_var : term -> bool
val is_var_res_exp_varlist_update : term -> bool
val is_var_res_implies_unequal : term -> bool
val is_var_res_implies_unequal_sym : term -> term -> term -> bool
val is_var_res_prog_aquire_lock : term -> bool
val is_var_res_prog_aquire_lock_input : term -> bool
val is_var_res_prog_aquire_lock_internal : term -> bool
val is_var_res_prog_assign : term -> bool
val is_var_res_prog_best_local_action : term -> bool
val is_var_res_prog_call_by_value_arg : term -> bool
val is_var_res_prog_cond_best_local_action : term -> bool
val is_var_res_prog_eval_expressions : term -> bool
val is_var_res_prog_local_var : term -> bool
val is_var_res_prog_parallel_procedure_call : term -> bool
val is_var_res_prog_procedure_call : term -> bool
val is_var_res_prog_quant_best_local_action : term -> bool
val is_var_res_prog_release_lock : term -> bool
val is_var_res_prog_release_lock_input : term -> bool
val is_var_res_prog_release_lock_internal : term -> bool
val is_var_res_prop : term -> bool
val is_var_res_prop_binexpression : term -> bool
val is_var_res_prop_binexpression_cond : term -> bool
val is_var_res_prop_equal : term -> bool
val is_var_res_prop_implies : term -> bool
val is_var_res_prop_implies_eq : term -> bool
val is_var_res_prop_input_ap_distinct : term -> bool;
val is_var_res_prop_input_distinct : term -> bool;
val is_var_res_prop_internal : term -> bool
val is_var_res_prop_stack_true : term -> bool
val is_var_res_prop_unequal : term -> bool
val is_var_res_prop_varlist_update : term -> bool
val mk_VAR_RES_COND_HOARE_TRIPLE : term * term * term * term -> term
val mk_VAR_RES_IS_PURE_PROPOSITION : term -> term -> term
val mk_VAR_RES_IS_STACK_IMPRECISE___USED_VARS : term -> term -> term
val mk_var_res_exp_const : term -> hol_type -> term
val mk_var_res_exp_var : term -> hol_type -> term
val mk_var_res_expr_type : hol_type -> hol_type
val string2num_var : string -> term
val var_res_mk_const : string -> term;
val var_res_mk_local_vars : (term * term option) list -> term -> term

end

