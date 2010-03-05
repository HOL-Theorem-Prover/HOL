structure holfootSyntax :> holfootSyntax =
struct

(*
quietdec := true;
loadPath := (Globals.HOLDIR ^ "/examples/separationLogic/src") :: 
            (Globals.HOLDIR ^ "/examples/separationLogic/src/holfoot") :: 
            !loadPath;

map load ["finite_mapTheory", "vars_as_resourceTheory", "holfootTheory"];
show_assums := true;
*)

open HolKernel Parse boolSyntax
open vars_as_resourceTheory
open vars_as_resourceSyntax
open holfootTheory;
open separationLogicSyntax

(*
quietdec := false;
*)

fun holfoot_mk_const n = 
   prim_mk_const {Name = n, Thy = "holfoot"}

val holfoot_heap_ty =  Type `:holfoot_heap`;
val holfoot_stack_ty = Type `:holfoot_stack`;
val holfoot_state_ty = Type `:holfoot_state`;
val holfoot_var_ty = Type `:holfoot_var`;
val holfoot_tag_ty = Type `:holfoot_tag`;
val holfoot_a_expression_ty = Type `:holfoot_a_expression`;
val holfoot_a_proposition_ty = Type `:holfoot_a_proposition`;



(*****************************************************************
 VARS & TAGS
 ****************************************************************)

val holfoot_var_term = holfoot_mk_const "holfoot_var"
val holfoot_tag_term = holfoot_mk_const "holfoot_tag"

fun string2holfoot_var s =
  mk_comb (holfoot_var_term, stringLib.fromMLstring s);

fun string2holfoot_tag s =
  mk_comb (holfoot_tag_term, stringLib.fromMLstring s);

(*
  val t = string2holfoot_tag "t";
*)
val dest_holfoot_tag = strip_comb_1 holfoot_tag_term;
val is_holfoot_tag = can dest_holfoot_tag

(*
  val t = string2holfoot_var "x";
*)
val dest_holfoot_var = strip_comb_1 holfoot_var_term;
val is_holfoot_var = can dest_holfoot_var
fun holfoot_var2string t =
   stringLib.fromHOLstring (dest_holfoot_var t)



(*****************************************************************
 PROGRAMS
 ****************************************************************)

(*
  val var = "x";
  val term = ``holfoot_prog_dispose (var_res_exp_var (holfoot_var "x"))``
  val expr = ``5:num``
*)
fun holfoot_mk_var_abs (var, term) =
  let
     val sm_var_term = string2holfoot_var var;
     val var_term = variant (free_vars term) (mk_var (var, Type `:holfoot_var`));
     val term1 = subst [sm_var_term |-> var_term] term;
     val term2 = mk_abs (var_term, term1)
  in
     term2
  end;


fun holfoot_mk_local_var (var,term) =
   mk_icomb (var_res_prog_local_var_term, holfoot_mk_var_abs (var, term));

fun holfoot_mk_call_by_value_arg ((var,expr),term) =
   list_mk_icomb (var_res_prog_call_by_value_arg_term, [holfoot_mk_var_abs (var, term), expr]);



val holfoot_prog_new_term = holfoot_mk_const "holfoot_prog_new";
val dest_holfoot_prog_new = strip_comb_1 holfoot_prog_new_term;
val is_holfoot_prog_new = (can dest_holfoot_prog_new);


val holfoot_prog_dispose_term = holfoot_mk_const "holfoot_prog_dispose";
val dest_holfoot_prog_dispose = strip_comb_1 holfoot_prog_dispose_term;
val is_holfoot_prog_dispose = (can dest_holfoot_prog_dispose);


val holfoot_prog_field_lookup_term = holfoot_mk_const "holfoot_prog_field_lookup";
val dest_holfoot_prog_field_lookup = strip_comb_3 holfoot_prog_field_lookup_term
val is_holfoot_prog_field_lookup = (can dest_holfoot_prog_field_lookup);


val holfoot_prog_field_assign_term = holfoot_mk_const "holfoot_prog_field_assign";
val dest_holfoot_prog_field_assign = strip_comb_3 holfoot_prog_field_assign_term;
val is_holfoot_prog_field_assign = (can dest_holfoot_prog_field_assign);

val holfoot_prog_procedure_call_term =
``var_res_prog_procedure_call:string -> 
    (holfoot_var list # holfoot_a_expression list) -> holfoot_program``

val holfoot_prog_parallel_procedure_call_term =
``var_res_prog_parallel_procedure_call:
    string -> (holfoot_var list # holfoot_a_expression list) -> 
    string -> (holfoot_var list # holfoot_a_expression list) -> 
    holfoot_program``

val holfoot_prog_assign_term = ``var_res_prog_assign:holfoot_var -> holfoot_a_expression -> holfoot_program``
val holfoot_prog_block_term = ``fasl_prog_block : holfoot_program list -> holfoot_program``;
val holfoot_prog_cond_term = ``fasl_prog_cond:holfoot_state fasl_predicate -> holfoot_program -> holfoot_program -> holfoot_program``
val holfoot_prog_with_resource_term = 
   ``fasl_prog_cond_critical_section:string->holfoot_state fasl_predicate->holfoot_program->holfoot_program``
val dest_holfoot_prog_with_resource = strip_comb_3 holfoot_prog_with_resource_term;
val is_holfoot_prog_with_resource = can dest_holfoot_prog_with_resource

val holfoot_prog_while_term = 
   ``fasl_prog_while:holfoot_state fasl_predicate->holfoot_program->holfoot_program``


val holfoot_exp_const_term = ``var_res_exp_const:num -> holfoot_a_expression``;
val holfoot_exp_var_term = ``var_res_exp_var:holfoot_var -> holfoot_a_expression``;
val holfoot_exp_binop_term = ``(var_res_exp_binop :(num -> num -> num) ->
                     holfoot_a_expression ->
                     holfoot_a_expression ->
                     holfoot_a_expression)``;

val holfoot_exp_op_term = ``(var_res_exp_op :(num list -> num) ->
                     holfoot_a_expression list ->
                     holfoot_a_expression)``;

val holfoot_exp_add_term = mk_comb (holfoot_exp_binop_term, numSyntax.plus_tm)
val holfoot_exp_sub_term = mk_comb (holfoot_exp_binop_term, numSyntax.minus_tm)
val holfoot_exp_mult_term = mk_comb (holfoot_exp_binop_term, numSyntax.mult_tm)
val holfoot_exp_div_term = mk_comb (holfoot_exp_binop_term, numSyntax.div_tm)
val holfoot_exp_mod_term = mk_comb (holfoot_exp_binop_term, numSyntax.mod_tm)
val holfoot_exp_exp_term = mk_comb (holfoot_exp_binop_term, numSyntax.exp_tm)
open numSyntax

val holfoot_prog_best_local_action_term =
   ``var_res_prog_best_local_action : holfoot_a_proposition -> holfoot_a_proposition ->
        holfoot_program``

val holfoot_prog_quant_best_local_action_term =
   ``var_res_prog_quant_best_local_action : ('a -> holfoot_a_proposition) -> ('a -> holfoot_a_proposition) ->
        holfoot_program``

fun inst_tyvar_with_holfoot_state t =
   inst [hd (type_vars_in_term t) |-> holfoot_state_ty] t;

val holfoot_pred_false_term = inst_tyvar_with_holfoot_state fasl_pred_false_term;
val holfoot_pred_true_term = inst_tyvar_with_holfoot_state fasl_pred_true_term;
val holfoot_pred_neg_term = inst_tyvar_with_holfoot_state fasl_pred_neg_term;
val holfoot_pred_and_term = inst_tyvar_with_holfoot_state fasl_pred_and_term;
val holfoot_pred_or_term = inst_tyvar_with_holfoot_state fasl_pred_or_term;

val holfoot_pred_bin_term = ``(var_res_pred_bin :(num -> num -> bool) ->
                     holfoot_a_expression ->
                     holfoot_a_expression ->
                     holfoot_state fasl_predicate)``;

val holfoot_pred_term = ``(var_res_pred :(num list -> bool) ->
                     holfoot_a_expression list ->
                     holfoot_state fasl_predicate)``;

val holfoot_pred_eq_term = mk_comb (holfoot_pred_bin_term, ``($=):num->num->bool``);
val holfoot_pred_neq_term = mk_comb (holfoot_pred_bin_term, ``\x1:num x2. ~(x1 = x2)``);
val holfoot_pred_lt_term = mk_comb (holfoot_pred_bin_term, ``($<):num->num->bool``);
val holfoot_pred_le_term = mk_comb (holfoot_pred_bin_term, ``($<=):num->num->bool``);
val holfoot_pred_gt_term = mk_comb (holfoot_pred_bin_term, ``($>):num->num->bool``);
val holfoot_pred_ge_term = mk_comb (holfoot_pred_bin_term, ``($>=):num->num->bool``);


val holfoot_separation_combinator_term = ``holfoot_separation_combinator``
val holfoot_disjoint_fmap_union_term = ``DISJOINT_FMAP_UNION :holfoot_heap bin_option_function``;
val holfoot_stack_true_term = ``(var_res_prop_stack_true DISJOINT_FMAP_UNION):holfoot_a_proposition``
val holfoot_bool_proposition_term = ``(var_res_bool_proposition DISJOINT_FMAP_UNION):bool->holfoot_a_proposition``
val holfoot_ap_binexpression_term = ``(var_res_prop_binexpression DISJOINT_FMAP_UNION T):(num->num->bool)->holfoot_a_expression->holfoot_a_expression->holfoot_a_proposition``
val holfoot_ap_lt_term = mk_comb (holfoot_ap_binexpression_term, ``($<):num->num->bool``);
val holfoot_ap_le_term = mk_comb (holfoot_ap_binexpression_term, ``($<=):num->num->bool``);
val holfoot_ap_gt_term = mk_comb (holfoot_ap_binexpression_term, ``($>):num->num->bool``);
val holfoot_ap_ge_term = mk_comb (holfoot_ap_binexpression_term, ``($>=):num->num->bool``);

val holfoot_ap_equal_term = ``(var_res_prop_equal DISJOINT_FMAP_UNION):holfoot_a_expression->holfoot_a_expression->holfoot_a_proposition``
val holfoot_ap_unequal_term = ``(var_res_prop_unequal DISJOINT_FMAP_UNION):holfoot_a_expression->holfoot_a_expression->holfoot_a_proposition``
val holfoot_ap_false_term = ``asl_false:holfoot_a_proposition``
val holfoot_ap_eq_cond_term = ``(var_res_prop_binexpression_cond DISJOINT_FMAP_UNION $=):holfoot_a_expression -> holfoot_a_expression -> holfoot_a_proposition -> holfoot_a_proposition -> holfoot_a_proposition``
val holfoot_ap_star_term = ``asl_star holfoot_separation_combinator``
val holfoot_ap_bigstar_list_term = ``asl_bigstar_list holfoot_separation_combinator``

val holfoot_prop_input_ap_distinct_term = 
``(var_res_prop_input_ap_distinct DISJOINT_FMAP_UNION):
  (holfoot_var set # holfoot_var set) -> holfoot_var list ->
  holfoot_a_proposition -> holfoot_a_proposition``

val holfoot_prop_input_ap_term = 
``(var_res_prop_input_ap DISJOINT_FMAP_UNION):
  (holfoot_var set # holfoot_var set) -> 
  holfoot_a_proposition -> holfoot_a_proposition``


val HOLFOOT_SPECIFICATION_term =
``(FASL_SPECIFICATION holfoot_separation_combinator) :
     (string # holfoot_a_proposition) list -> 
     (bool # string # (holfoot_var list # num list -> holfoot_program)
           # (holfoot_var list # num list -> holfoot_program)) list -> 
     bool``;

val holfoot_lock_invariant_term = 
   ``(var_res_lock_invariant DISJOINT_FMAP_UNION):(holfoot_var set) -> holfoot_a_proposition -> holfoot_a_proposition``

val HOLFOOT_LOCK_ENV_MAP_term =
  ``(VAR_RES_LOCK_ENV_MAP DISJOINT_FMAP_UNION):(string # holfoot_var list # holfoot_a_proposition) list ->
     (string # holfoot_a_proposition) list``


val holfoot_ap_data_list_seg_term = holfoot_mk_const "holfoot_ap_data_list_seg";
val dest_holfoot_ap_data_list_seg = strip_comb_4 holfoot_ap_data_list_seg_term;
val is_holfoot_ap_data_list_seg = (can dest_holfoot_ap_data_list_seg);

val holfoot_ap_data_list_term = holfoot_mk_const "holfoot_ap_data_list";
val dest_holfoot_ap_data_list = strip_comb_3 holfoot_ap_data_list_term;
val is_holfoot_ap_data_list = (can dest_holfoot_ap_data_list);

val holfoot_ap_data_queue_term = holfoot_mk_const "holfoot_ap_data_queue";
val dest_holfoot_ap_data_queue = strip_comb_4 holfoot_ap_data_queue_term;
val is_holfoot_ap_data_queue = (can dest_holfoot_ap_data_queue);

val holfoot_exp_null_term = ``(var_res_exp_const 0):holfoot_a_expression``
fun is_holfoot_exp_null t = aconv t holfoot_exp_null_term

val holfoot_ap_bintree_term = holfoot_mk_const "holfoot_ap_bintree";
val dest_holfoot_ap_bintree = strip_comb_2 holfoot_ap_bintree_term;
val is_holfoot_ap_bintree = (can dest_holfoot_ap_bintree);

val holfoot_ap_tree_term = holfoot_mk_const "holfoot_ap_tree";
val dest_holfoot_ap_tree = strip_comb_2 holfoot_ap_tree_term;
val is_holfoot_ap_tree = (can dest_holfoot_ap_tree);

val holfoot_ap_data_tree_term = holfoot_mk_const "holfoot_ap_data_tree";
val dest_holfoot_ap_data_tree = strip_comb_3 holfoot_ap_data_tree_term;
val is_holfoot_ap_data_tree = (can dest_holfoot_ap_data_tree);

val holfoot_ap_points_to_term = holfoot_mk_const "holfoot_ap_points_to";
val dest_holfoot_ap_points_to = strip_comb_2 holfoot_ap_points_to_term;
val is_holfoot_ap_points_to = (can dest_holfoot_ap_points_to);

val holfoot_empty_xenv_penv =
 (``((VAR_RES_COMBINATOR DISJOINT_FMAP_UNION) :holfoot_state bin_option_function,
       (K asl_false):string -> holfoot_a_proposition)``,
 ``(FEMPTY :string |-> (holfoot_var list # num list -> holfoot_program))``)


val holfoot_implies_in_heap_term = holfoot_mk_const "holfoot_implies_in_heap"
val dest_holfoot_implies_in_heap = strip_comb_3 holfoot_implies_in_heap_term;
val is_holfoot_implies_in_heap = (can dest_holfoot_implies_in_heap);

val holfoot_implies_in_heap_or_null_term = holfoot_mk_const "holfoot_implies_in_heap_or_null"
val dest_holfoot_implies_in_heap_or_null = strip_comb_3 holfoot_implies_in_heap_or_null_term;
val is_holfoot_implies_in_heap_or_null = (can dest_holfoot_implies_in_heap_or_null);

val holfoot_empty_prop_bag_term = Term `EMPTY_BAG : holfoot_a_proposition -> num`
end;
