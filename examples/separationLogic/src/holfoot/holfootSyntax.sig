signature holfootSyntax =
sig

include Abbrev;

val holfoot_heap_ty : hol_type;
val holfoot_stack_ty : hol_type;
val holfoot_state_ty : hol_type;


val string2holfoot_tag : string -> term
val string2holfoot_var : string -> term

val holfoot_mk_call_by_value_arg : (string * term) * term -> term
val holfoot_mk_const : string -> term
val holfoot_mk_local_var : string * term -> term
val holfoot_mk_var_abs : string * term -> term


val holfoot_separation_combinator_term : term
val holfoot_empty_prop_bag_term : term
val holfoot_exp_null_term : term
val holfoot_disjoint_fmap_union_term : term
val holfoot_ap_bigstar_list_term : term
val holfoot_ap_binexpression_term : term
val holfoot_ap_bintree_term : term
val holfoot_ap_tree_term : term
val holfoot_ap_data_tree_term : term
val holfoot_ap_data_list_seg_term : term
val holfoot_ap_data_list_term : term
val holfoot_ap_eq_cond_term : term
val holfoot_ap_equal_term : term
val holfoot_ap_false_term : term
val holfoot_ap_ge_term : term
val holfoot_ap_gt_term : term
val holfoot_ap_le_term : term
val holfoot_ap_lt_term : term
val holfoot_ap_points_to_term : term
val holfoot_ap_star_term : term
val holfoot_ap_unequal_term : term
val holfoot_bool_proposition_term : term
val holfoot_exp_add_term : term
val holfoot_exp_binop_term : term;
val holfoot_exp_const_term : term
val holfoot_exp_mult_term : term
val holfoot_exp_div_term : term
val holfoot_exp_mod_term : term
val holfoot_exp_exp_term : term
val holfoot_exp_sub_term : term
val holfoot_exp_var_term : term
val holfoot_pred_and_term : term
val holfoot_pred_bin_term : term
val holfoot_pred_eq_term : term
val holfoot_pred_false_term : term
val holfoot_pred_ge_term : term
val holfoot_pred_gt_term : term 
val holfoot_pred_le_term : term
val holfoot_pred_lt_term : term 
val holfoot_pred_neg_term : term
val holfoot_pred_neq_term : term
val holfoot_pred_or_term : term
val holfoot_pred_true_term : term
val holfoot_prog_assign_term : term
val holfoot_prog_block_term : term
val holfoot_prog_cond_term : term
val holfoot_prog_dispose_term  : term
val holfoot_prog_field_assign_term : term
val holfoot_prog_field_lookup_term : term
val holfoot_prog_new_term  : term
val holfoot_prog_parallel_procedure_call_term : term
val holfoot_prog_procedure_call_term : term
val holfoot_prog_while_term : term
val holfoot_prog_with_resource_term : term
val holfoot_prop_input_ap_distinct_term : term
val holfoot_prop_input_ap_term : term
val holfoot_stack_true_term : term
val holfoot_tag_term  : term
val holfoot_var_term  : term


val dest_holfoot_ap_bintree : term -> term * term
val dest_holfoot_ap_tree : term -> term * term
val dest_holfoot_ap_data_tree : term -> term * term * term
val dest_holfoot_ap_data_list : term -> term * term * term
val dest_holfoot_ap_data_list_seg : term -> term * term * term * term
val dest_holfoot_prog_dispose : term -> term
val dest_holfoot_prog_field_assign : term -> term * term * term
val dest_holfoot_prog_field_lookup : term -> term * term * term
val dest_holfoot_prog_new : term -> term
val dest_holfoot_tag : term -> term
val dest_holfoot_var : term -> term
val is_holfoot_ap_bintree : term -> bool
val is_holfoot_ap_tree : term -> bool
val is_holfoot_ap_data_tree : term -> bool
val is_holfoot_ap_data_list : term -> bool
val is_holfoot_ap_data_list_seg : term -> bool
val is_holfoot_prog_dispose : term -> bool
val is_holfoot_prog_field_assign : term -> bool
val is_holfoot_prog_field_lookup : term -> bool
val is_holfoot_prog_new : term -> bool
val is_holfoot_tag : term -> bool
val is_holfoot_var : term -> bool
val dest_holfoot_ap_points_to : term -> term * term
val is_holfoot_ap_points_to : term -> bool
val is_holfoot_exp_null : term -> bool

val holfoot_implies_in_heap_term : term 
val dest_holfoot_implies_in_heap : term -> term * term * term
val is_holfoot_implies_in_heap   : term -> bool
val holfoot_implies_in_heap_or_null_term : term 
val dest_holfoot_implies_in_heap_or_null : term -> term * term * term
val is_holfoot_implies_in_heap_or_null   : term -> bool


val HOLFOOT_SPECIFICATION_term : term
val holfoot_lock_invariant_term : term;
val HOLFOOT_LOCK_ENV_MAP_term : term;
val holfoot_prog_best_local_action_term : term
val holfoot_prog_quant_best_local_action_term : term
val holfoot_empty_xenv_penv : term * term

end

