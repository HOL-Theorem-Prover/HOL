signature smallfootSyntax =
sig
  include Abbrev


  val COND_PROP___ADD_COND_term : term;
  val COND_PROP___EXISTS_term : term;
  val COND_PROP___STRONG_EXISTS_term : term;
  val FASL_PROGRAM_HOARE_TRIPLE_term : term
  val FASL_PROGRAM_IS_ABSTRACTION_term : term
  val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_term : term;
  val SMALLFOOT_AP_PERMISSION_UNIMPORTANT_term : term;
  val SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE_term : term;
  val SMALLFOOT_COND_HOARE_TRIPLE_term : term
  val SMALLFOOT_COND_PROP___EQUIV_term : term;
  val SMALLFOOT_COND_PROP___IMP_term : term;
  val SMALLFOOT_HOARE_TRIPLE_term : term
  val SMALLFOOT_IS_STRONG_STACK_PROPOSITION_term : term
  val SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE_term : term;
  val SMALLFOOT_PROP_IMPLIES_term : term
  val SMALLFOOT_SING_PROCEDURE_SPEC_term : term
  val SMALLFOOT_SPECIFICATION_term : term
  val fasl_prog_best_local_action_term : term
  val fasl_prog_block_term : term
  val fasl_prog_cond_term : term
  val fasl_prog_seq_term : term
  val fasl_prog_while_with_invariant_term : term
  val smallfoot_ae_const_term : term
  val smallfoot_ae_null_term : term
  val smallfoot_ae_var_term : term
  val smallfoot_ae_var_update_term : term;
  val smallfoot_ap_bigstar_list_term : term;
  val smallfoot_ap_bigstar_term : term;
  val smallfoot_ap_bintree_term : term
  val smallfoot_ap_cond_term : term
  val smallfoot_ap_emp_term : term
  val smallfoot_ap_empty_heap_cond_term : term;
  val smallfoot_ap_equal_cond_term : term
  val smallfoot_ap_equal_term : term
  val smallfoot_ap_exp_is_defined_term : term;
  val smallfoot_ap_false_term : term
  val smallfoot_ap_greater_term : term
  val smallfoot_ap_greatereq_term : term
  val smallfoot_ap_implies_ae_equal_term : term
  val smallfoot_ap_less_term : term
  val smallfoot_ap_lesseq_term : term
  val smallfoot_ap_data_list_seg_term : term
  val smallfoot_ap_data_list_term : term
  val smallfoot_ap_points_to_term : term
  val smallfoot_ap_stack_true_term : term;
  val smallfoot_ap_star_term : term
  val smallfoot_ap_unequal_cond_term : term
  val smallfoot_ap_unequal_term : term
  val smallfoot_ap_unknown_term : term
  val smallfoot_ap_var_update_term : term;
  val smallfoot_choose_const_best_local_action_term : term
  val smallfoot_cond_best_local_action_term : term
  val smallfoot_cond_choose_const_best_local_action_term : term
  val smallfoot_env_term : term
  val smallfoot_input_preserve_names_wrapper_term : term
  val smallfoot_p_add_term : term
  val smallfoot_p_and_term : term
  val smallfoot_p_const_term : term
  val smallfoot_p_equal_term : term
  val smallfoot_p_expression_eval_term : term
  val smallfoot_p_greater_term : term
  val smallfoot_p_greatereq_term : term
  val smallfoot_p_less_term : term
  val smallfoot_p_lesseq_term : term
  val smallfoot_p_neg_term : term
  val smallfoot_p_or_term : term
  val smallfoot_p_sub_term : term
  val smallfoot_p_unequal_term : term
  val smallfoot_p_var_term : term
  val smallfoot_parallel_proc_call_abstraction_term : term
  val smallfoot_proc_call_abstraction_term : term
  val smallfoot_prog_aquire_resource_internal_term : term;
  val smallfoot_prog_aquire_resource_term : term;
  val smallfoot_prog_assign_term : term
  val smallfoot_prog_best_local_action_term : term
  val smallfoot_prog_block_term : term
  val smallfoot_prog_cond_term : term
  val smallfoot_prog_dispose_term : term
  val smallfoot_prog_field_assign_term : term
  val smallfoot_prog_field_lookup_term : term
  val smallfoot_prog_local_var_term : term
  val smallfoot_prog_new_term : term
  val smallfoot_prog_parallel_procedure_call_term : term
  val smallfoot_prog_parallel_term : term
  val smallfoot_prog_procedure_call_term : term;
  val smallfoot_prog_release_resource_internal_term : term;
  val smallfoot_prog_release_resource_term : term;
  val smallfoot_prog_val_arg_term : term
  val smallfoot_prog_while_term : term
  val smallfoot_prog_while_with_invariant_term : term
  val smallfoot_prog_with_resource_term : term;
  val smallfoot_prop_input_ap_distinct_term : term
  val smallfoot_prop_input_ap_term : term
  val smallfoot_prop_input_term : term
  val smallfoot_prop_internal_ap_term : term
  val smallfoot_prop_internal_term : term
  val smallfoot_prop_term : term
  val smallfoot_slp_new_var___PROP_COND_term : term;
  val smallfoot_tag_term : term
  val smallfoot_var_term : term
  val smallfoot_xenv_term : term
  


  val FEMPTY_tm : term
  val FUPDATE_tm : term
  val FEVERY_term : term

  val dest_FEVERY : term -> term * term
  val is_FEVERY : term -> bool
  val dest_FUPDATE : term -> term * term
  val is_FUPDATE : term -> bool




  val smallfoot_a_expression_type : hol_type
  val smallfoot_a_proposition_type : hol_type
  val smallfoot_p_expression_type : hol_type
  val smallfoot_p_proposition_type : hol_type
  val smallfoot_prog_type : hol_type
  val smallfoot_tag_type : hol_type
  val smallfoot_var_type : hol_type





  val dest_BAG_EVERY : term -> term * term;
  val dest_BAG_IMAGE : term -> term * term;
  val dest_COND_PROP___ADD_COND : term -> term * term;
  val dest_COND_PROP___EXISTS : term -> term * term;
  val dest_COND_PROP___STRONG_EXISTS : term -> term * term;
  val dest_FASL_PROGRAM_HOARE_TRIPLE : term -> term * term * term * term * term
  val dest_FASL_PROGRAM_IS_ABSTRACTION : term -> term * term * term * term
  val dest_FASL_PROG_SEQ : term -> term * term
  val dest_SMALLFOOT_AP_PERMISSION_UNIMPORTANT : term -> term;
  val dest_SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS : term -> term * term;
  val dest_SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE : term -> term * term * term;
  val dest_SMALLFOOT_COND_HOARE_TRIPLE : term -> term * term * term
  val dest_SMALLFOOT_COND_PROP___EQUIV : term -> term * term;
  val dest_SMALLFOOT_COND_PROP___IMP : term -> term * term;
  val dest_SMALLFOOT_HOARE_TRIPLE : term -> term * term * term * term * term
  val dest_SMALLFOOT_IS_STRONG_STACK_PROPOSITION : term -> term;
  val dest_SMALLFOOT_PROP_IMPLIES : term -> term * term * term * term *  term * term * term * term
  val dest_SMALLFOOT_SING_PROCEDURE_SPEC : term -> term * term * term * term * term * term * term * term 
  val dest_SMALLFOOT_SPECIFICATION : term -> term * term
  val dest_fasl_prog_best_local_action : term -> term * term
  val dest_fasl_prog_block : term -> term
  val dest_fasl_prog_cond : term -> term * term * term
  val dest_fasl_prog_while_with_invariant : term -> term * term * term
  val dest_finite_map : term -> (term * term) list * term option
  val dest_local_vars : term -> (term * term option) list * term
  val dest_smallfoot_ae_const : term -> term
  val dest_smallfoot_ae_const_null : term -> term
  val dest_smallfoot_ae_var : term -> term
  val dest_smallfoot_ae_var_update : term -> term * term * term;
  val dest_smallfoot_ap_bintree : term -> term * term * term
  val dest_smallfoot_ap_compare : term -> term * term
  val dest_smallfoot_ap_cond : term -> term * term * term * term
  val dest_smallfoot_ap_empty_heap_cond : term -> term;
  val dest_smallfoot_ap_equal : term -> term * term
  val dest_smallfoot_ap_equal_cond : term -> term * term * term
  val dest_smallfoot_ap_exp_is_defined : term -> term;
  val dest_smallfoot_ap_implies_ae_equal : term -> term * term * term
  val dest_smallfoot_ap_data_list : term -> term * term * term
  val dest_smallfoot_ap_data_list_seg : term -> term * term * term * term;
  val dest_smallfoot_ap_data_list_seg_or_list : term -> term * term * term * term;
  val dest_smallfoot_ap_data_list_seg_or_list_or_bintree : term -> term * term;
  val dest_smallfoot_ap_points_to : term -> term * term
  val dest_smallfoot_ap_spatial : term -> term
  val dest_smallfoot_ap_spatial___no_data_list_seg : term -> term
  val dest_smallfoot_ap_unequal : term -> term * term
  val dest_smallfoot_ap_unequal_cond : term -> term * term * term
  val dest_smallfoot_ap_unknown : term -> string;
  val dest_smallfoot_ap_var_update : term -> term * term * term;
  val dest_smallfoot_choose_const_best_local_action : term -> term * term * term * term * term
  val dest_smallfoot_cond_best_local_action : term -> term * term 
  val dest_smallfoot_cond_choose_const_best_local_action : term -> term * term * term * term * term
  val dest_smallfoot_parallel_proc_call_abstraction : term -> term * term * term * term * term * term * term * term * term * term
  val dest_smallfoot_proc_call_abstraction : term -> term * term * term * term * term
  val dest_smallfoot_prog_assign : term -> term * term
  val dest_smallfoot_prog_best_local_action : term -> term * term
  val dest_smallfoot_prog_block : term -> term;
  val dest_smallfoot_prog_cond : term -> term * term * term;
  val dest_smallfoot_prog_dispose : term -> term
  val dest_smallfoot_prog_field_assign : term -> term * term * term
  val dest_smallfoot_prog_field_lookup : term -> term * term * term
  val dest_smallfoot_prog_local_var : term -> term * term
  val dest_smallfoot_prog_new : term -> term 
  val dest_smallfoot_prog_parallel : term -> term * term
  val dest_smallfoot_prog_parallel_procedure_call : term -> term * term * term * term * term * term
  val dest_smallfoot_prog_procedure_call : term -> term * term * term
  val dest_smallfoot_prog_release_resource : term -> term * term;
  val dest_smallfoot_prog_val_arg : term -> term * term * term
  val dest_smallfoot_prog_while_with_invariant : term -> term * term * term * term
  val dest_smallfoot_prog_with_resource : term -> term * term * term;
  val dest_smallfoot_prop : term -> term * term * term
  val dest_smallfoot_prop_input : term -> term * term * term list * term
  val dest_smallfoot_prop_internal : term -> term * term * term * term * term * term * term * term
  val dest_smallfoot_prop_internal_ap : term -> term * term * term * term * term
  val dest_smallfoot_slp_new_var___PROP_COND : term -> term * term * term * term;
  val dest_smallfoot_tag : term -> term
  val dest_smallfoot_var : term -> term
  val is_BAG_EVERY : term -> bool;
  val is_BAG_IMAGE : term -> bool;
  val is_COND_PROP___ADD_COND : term -> bool;
  val is_COND_PROP___EXISTS : term -> bool;
  val is_COND_PROP___STRONG_EXISTS : term -> bool;
  val is_EMPTY_BAG : term -> bool;
  val is_FASL_PROGRAM_HOARE_TRIPLE : term -> bool
  val is_FASL_PROGRAM_IS_ABSTRACTION : term -> bool
  val is_FASL_PROG_SEQ : term -> bool
  val is_SMALLFOOT_AP_PERMISSION_UNIMPORTANT : term -> bool;
  val is_SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS : term -> bool;
  val is_SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE : term -> bool;
  val is_SMALLFOOT_COND_HOARE_TRIPLE : term -> bool
  val is_SMALLFOOT_COND_PROP___EQUIV : term -> bool;
  val is_SMALLFOOT_COND_PROP___IMP : term -> bool;
  val is_SMALLFOOT_HOARE_TRIPLE : term -> bool
  val is_SMALLFOOT_IS_STRONG_STACK_PROPOSITION : term -> bool;
  val is_SMALLFOOT_PROP_IMPLIES : term -> bool
  val is_SMALLFOOT_SING_PROCEDURE_SPEC : term -> bool
  val is_SMALLFOOT_SPECIFICATION : term -> bool
  val is_fasl_prog_best_local_action : term ->  bool
  val is_fasl_prog_block : term -> bool
  val is_fasl_prog_cond : term -> bool
  val is_fasl_prog_while_with_invariant : term -> bool
  val is_smallfoot_ae_const : term -> bool
  val is_smallfoot_ae_const_null : term -> bool
  val is_smallfoot_ae_null : term -> bool
  val is_smallfoot_ae_null_or_const_zero : term -> bool;
  val is_smallfoot_ae_var : term -> bool
  val is_smallfoot_ae_var_update : term -> bool;
  val is_smallfoot_ap_bintree : term -> bool
  val is_smallfoot_ap_compare : term -> bool
  val is_smallfoot_ap_cond : term -> bool;
  val is_smallfoot_ap_empty_heap_cond : term -> bool;
  val is_smallfoot_ap_equal : term -> bool
  val is_smallfoot_ap_equal_cond : term -> bool
  val is_smallfoot_ap_exp_is_defined : term -> bool;
  val is_smallfoot_ap_implies_ae_equal : term -> bool
  val is_smallfoot_ap_data_list : term -> bool
  val is_smallfoot_ap_data_list_seg : term -> bool
  val is_smallfoot_ap_data_list_seg_or_list : term -> bool
  val is_smallfoot_ap_data_list_seg_or_list_or_bintree : term -> bool
  val is_smallfoot_ap_points_to : term -> bool
  val is_smallfoot_ap_spatial : term -> bool
  val is_smallfoot_ap_spatial___no_data_list_seg : term -> bool
  val is_smallfoot_ap_unequal : term -> bool
  val is_smallfoot_ap_unequal_cond : term -> bool
  val is_smallfoot_ap_unknown : term -> bool
  val is_smallfoot_ap_var_update : term -> bool;
  val is_smallfoot_choose_const_best_local_action : term -> bool
  val is_smallfoot_cond_best_local_action : term -> bool
  val is_smallfoot_cond_choose_const_best_local_action : term -> bool
  val is_smallfoot_parallel_proc_call_abstraction : term -> bool
  val is_smallfoot_proc_call_abstraction : term -> bool
  val is_smallfoot_prog_assign : term -> bool
  val is_smallfoot_prog_best_local_action : term ->  bool
  val is_smallfoot_prog_block : term -> bool;
  val is_smallfoot_prog_cond : term -> bool;
  val is_smallfoot_prog_dispose : term -> bool
  val is_smallfoot_prog_field_assign : term -> bool
  val is_smallfoot_prog_field_lookup : term -> bool
  val is_smallfoot_prog_local_var : term -> bool
  val is_smallfoot_prog_new : term -> bool
  val is_smallfoot_prog_parallel : term -> bool
  val is_smallfoot_prog_parallel_procedure_call : term -> bool
  val is_smallfoot_prog_procedure_call : term -> bool
  val is_smallfoot_prog_release_resource : term -> bool;
  val is_smallfoot_prog_val_arg : term -> bool
  val is_smallfoot_prog_while_with_invariant : term -> bool
  val is_smallfoot_prog_with_resource : term -> bool;
  val is_smallfoot_prop : term -> bool
  val is_smallfoot_prop_input : term -> bool
  val is_smallfoot_prop_internal : term -> bool
  val is_smallfoot_prop_internal_ap : term -> bool
  val is_smallfoot_slp_new_var___PROP_COND : term -> bool;
  val is_smallfoot_var : term -> bool


  val mk_BAG_IMAGE : term -> term -> term;
  val mk_FASL_PROGRAM_IS_ABSTRACTION : term * term * term * term -> term
  val mk_SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS : term -> term -> term;
  val mk_fasl_prog_block : term -> term
  val mk_fasl_prog_cond : term * term * term -> term
  val mk_fasl_prog_while_with_invariant : term * term * term  -> term
  val mk_smallfoot_ap_equal_cond : term * term * term -> term;
  val mk_smallfoot_ap_unequal_cond : term * term * term -> term;
  val mk_smallfoot_ap_unknown : string -> term;
  val mk_smallfoot_prog_while_with_invariant : term * term * term * term -> term


  val save_dest_pair : term -> term * term
  val smallfoot_mk_local_var : string * term -> term
  val smallfoot_mk_val_arg : (string * term) * term -> term
  val smallfoot_mk_var_abs : string * term -> term


  val string2smallfoot_var : string -> term
  val string2smallfoot_tag : string -> term
  val string2smallfoot_const : string -> term



end
