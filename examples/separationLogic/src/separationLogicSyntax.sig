signature separationLogicSyntax =
sig

include Abbrev;

val safe_dest_pair : term -> term * term

val FEMPTY_tm : term
val FUPDATE_tm : term
val strip_finite_map : term -> (term * term) list * term option

val list2tuple1 : 'a list -> 'a
val list2tuple2 : 'a list -> 'a * 'a
val list2tuple3 : 'a list -> 'a * 'a * 'a
val list2tuple4 : 'a list -> 'a * 'a * 'a * 'a
val list2tuple5 : 'a list -> 'a * 'a * 'a * 'a * 'a
val list2tuple6 : 'a list -> 'a * 'a * 'a * 'a * 'a * 'a
val list2tuple7 : 'a list -> 'a * 'a * 'a * 'a * 'a * 'a * 'a
val list2tuple8 : 'a list -> 'a * 'a * 'a * 'a * 'a * 'a * 'a * 'a
val list2tuple9 : 'a list -> 'a * 'a * 'a * 'a * 'a * 'a * 'a * 'a * 'a

val strip_comb_num : int -> term -> term -> term list
val strip_comb_1 : term -> term -> term
val strip_comb_2 : term -> term -> term * term
val strip_comb_3 : term -> term -> term * term * term
val strip_comb_4 : term -> term -> term * term * term * term
val strip_comb_5 : term -> term -> term * term * term * term * term
val strip_comb_6 : term -> term -> term * term * term * term * term * term
val strip_comb_7 : term -> term -> term * term * term * term * term * term * term
val strip_comb_8 : term -> term -> term * term * term * term * term * term * term * term
val strip_comb_9 : term -> term -> term * term * term * term * term * term * term * term * term

val asl_prog_parallel_term : term
val dest_asl_prog_parallel : term -> term * term
val is_asl_prog_parallel : term -> bool

val asl_prog_seq_term : term
val dest_asl_prog_seq : term -> term * term
val is_asl_prog_seq : term -> bool

val asl_prog_block_term : term
val dest_asl_prog_block : term -> term
val is_asl_prog_block : term -> bool
val mk_asl_prog_block : term -> term

val asl_prog_assume_term : term
val dest_asl_prog_assume : term -> term
val is_asl_prog_assume   : term -> bool

val asl_prog_cond_term : term
val dest_asl_prog_cond : term -> term * term * term
val is_asl_prog_cond : term -> bool
val mk_asl_prog_cond : term * term * term -> term

val asl_prog_while_term : term
val dest_asl_prog_while : term -> term * term
val is_asl_prog_while : term -> bool
val mk_asl_prog_while : term * term -> term


val asl_prog_cond_critical_section_term : term
val dest_asl_prog_cond_critical_section : term -> term * term * term
val is_asl_prog_cond_critical_section : term -> bool

val asl_prog_best_local_action_term : term
val dest_asl_prog_best_local_action : term -> term * term
val is_asl_prog_best_local_action : term -> bool

val ASL_PROGRAM_HOARE_TRIPLE_term : term
val dest_ASL_PROGRAM_HOARE_TRIPLE : term -> term * term * term * term * term
val is_ASL_PROGRAM_HOARE_TRIPLE : term -> bool

val ASL_PROGRAM_IS_ABSTRACTION_term : term
val dest_ASL_PROGRAM_IS_ABSTRACTION : term -> term * term * term * term
val is_ASL_PROGRAM_IS_ABSTRACTION : term -> bool
val mk_ASL_PROGRAM_IS_ABSTRACTION : term * term * term * term -> term

val ASL_SPECIFICATION_term : term

val COND_PROP___IMP_term : term
val dest_COND_PROP___IMP : term -> term * term
val is_COND_PROP___IMP : term -> bool

val COND_PROP___EQUIV_term : term
val dest_COND_PROP___EQUIV : term -> term * term
val is_COND_PROP___EQUIV : term -> bool

val COND_PROP___STRONG_EXISTS_term : term
val dest_COND_PROP___STRONG_EXISTS : term -> term * term
val is_COND_PROP___STRONG_EXISTS : term -> bool

val COND_PROP___EXISTS_term : term
val dest_COND_PROP___EXISTS : term -> term * term
val is_COND_PROP___EXISTS : term -> bool

val COND_PROP___ADD_COND_term : term
val dest_COND_PROP___ADD_COND : term -> term * term
val is_COND_PROP___ADD_COND : term -> bool

val asl_cond_star_term : term
val dest_asl_cond_star : term -> term * term * term
val is_asl_cond_star   : term -> bool

val asl_pred_false_term  : term
val asl_pred_true_term   : term
val asl_pred_neg_term    : term
val asl_pred_and_term    : term
val asl_pred_or_term     : term
val asl_pred_prim_term   : term


val asl_exists_term       : term
val asl_exists_list_term  : term
val fasl_star_term        : term
val asl_star_term         : term
val asl_bigstar_list_term : term
val asl_trivial_cond_term : term
val asl_emp_term          : term
val asl_false_term        : term
val is_asl_false          : term -> bool
val dest_asl_trival_cond  : term -> term * term
val is_asl_trivial_cond   : term -> bool
val dest_asl_star         : term -> term * term * term
val strip_asl_star        : term -> term list
val is_asl_star           : term -> bool
val dest_asl_exists       : term -> term * term
val is_asl_exists         : term -> bool
val dest_asl_exists_list  : term -> term * term
val is_asl_exists_list    : term -> bool


val asl_comment_loop_invariant_term : term
val dest_asl_comment_loop_invariant : term -> term * term;
val is_asl_comment_loop_invariant : term -> bool;


val asl_comment_block_spec_term : term
val dest_asl_comment_block_spec : term -> term * term;
val is_asl_comment_block_spec : term -> bool;

val asl_comment_loop_spec_term : term
val dest_asl_comment_loop_spec : term -> term * term;
val is_asl_comment_loop_spec : term -> bool;

val asl_comment_loop_unroll_term : term
val dest_asl_comment_loop_unroll : term -> term * term;
val is_asl_comment_loop_unroll   : term -> bool;

val asl_comment_location_term : term
val dest_asl_comment_location : term -> term * term
val save_dest_asl_comment_location : term -> term * term * (unit -> thm)
val is_asl_comment_location : term -> bool
val mk_asl_comment_location : term * term -> term
val empty_label_list : term
val dest_list_asl_comment_location : term -> term * term
val save_dest_list_asl_comment_location : term -> term * term * (unit -> thm)

val asl_comment_assert_term : term
val dest_asl_comment_assert : term -> term
val is_asl_comment_assert   : term -> bool;

val asl_comment_location_string_term : term
val dest_asl_comment_location_string : term -> term * term
val is_asl_comment_location_string : term -> bool

val asl_comment_location2_term : term
val dest_asl_comment_location2 : term -> term * term
val save_dest_asl_comment_location2 : term -> term * term * (unit -> thm)
val is_asl_comment_location2 : term -> bool
val mk_asl_comment_location2 : term * term -> term

val asl_comment_abstraction_term : term
val dest_asl_comment_abstraction : term -> term * term
val is_asl_comment_abstraction : term -> bool

val dest_asl_comment : term -> term * term * term * thm

val asl_procedure_call_preserve_names_wrapper_term : term;
val dest_asl_procedure_call_preserve_names_wrapper : term -> term * term * term * term
val is_asl_procedure_call_preserve_names_wrapper   : term -> bool
val dest_ASL_SPECIFICATION : term -> term * term * term;
val is_ASL_SPECIFICATION : term -> bool;


val asl_prog_choice_term : term;
val dest_asl_prog_choice : term -> term * term;
val is_asl_prog_choice : term -> bool;

val asl_prog_diverge_term : term;
val asl_prog_fail_term : term;


end

