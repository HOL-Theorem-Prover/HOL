structure vars_as_resourceSyntax :> vars_as_resourceSyntax =
struct

(*
quietdec := true;
loadPath := (Globals.HOLDIR ^ "/examples/separationLogic/src") :: 
            !loadPath;

map load ["finite_mapTheory", "vars_as_resourceTheory"];
show_assums := true;
*)

open HolKernel Parse boolLib finite_mapTheory 
open vars_as_resourceTheory;
open separationLogicSyntax separationLogicLib separationLogicTheory

(*
quietdec := false;
*)

fun var_res_mk_const n = 
   prim_mk_const {Name = n, Thy = "vars_as_resource"}

val var_res_prop_stack_true_term =  var_res_mk_const "var_res_prop_stack_true";
val dest_var_res_prop_stack_true = strip_comb_1 var_res_prop_stack_true_term
val is_var_res_prop_stack_true = can dest_var_res_prop_stack_true;


val var_res_bool_proposition_term = 
   var_res_mk_const "var_res_bool_proposition";
val dest_var_res_bool_proposition = strip_comb_2 var_res_bool_proposition_term
val is_var_res_bool_proposition = can dest_var_res_bool_proposition;

val var_res_prop_equal_term  = 
   var_res_mk_const "var_res_prop_equal";
val dest_var_res_prop_equal = strip_comb_3 var_res_prop_equal_term
val is_var_res_prop_equal = can dest_var_res_prop_equal;
fun is_var_res_prop_equal_sym e1 e2 tt = 
let
   val (_, e1', e2') = dest_var_res_prop_equal tt;
in
   ((aconv e1 e1') andalso (aconv e2 e2')) orelse
   ((aconv e1 e2') andalso (aconv e2 e1'))
end handle HOL_ERR _ => false


val var_res_prop_unequal_term  = 
   var_res_mk_const "var_res_prop_unequal";
val dest_var_res_prop_unequal = strip_comb_3 var_res_prop_unequal_term
val is_var_res_prop_unequal = can dest_var_res_prop_unequal;
fun is_var_res_prop_unequal_sym e1 e2 tt = 
let
   val (_, e1', e2') = dest_var_res_prop_unequal tt;
in
   ((aconv e1 e1') andalso (aconv e2 e2')) orelse
   ((aconv e1 e2') andalso (aconv e2 e1'))
end handle HOL_ERR _ => false

val var_res_prop_expression_term = var_res_mk_const "var_res_prop_expression";
val var_res_prop_binexpression_term = var_res_mk_const "var_res_prop_binexpression";
val dest_var_res_prop_binexpression = strip_comb_5 var_res_prop_binexpression_term;
val is_var_res_prop_binexpression = can dest_var_res_prop_binexpression

val var_res_prop_binexpression_cond_term = var_res_mk_const "var_res_prop_binexpression_cond";
val dest_var_res_prop_binexpression_cond = strip_comb_6 var_res_prop_binexpression_cond_term;
val is_var_res_prop_binexpression_cond = can dest_var_res_prop_binexpression_cond

val var_res_prog_procedure_call_term          = var_res_mk_const "var_res_prog_procedure_call" 
val var_res_prog_parallel_procedure_call_term = var_res_mk_const "var_res_prog_parallel_procedure_call" 
val var_res_prog_local_var_term               = var_res_mk_const "var_res_prog_local_var"
val var_res_prog_call_by_value_arg_term       = var_res_mk_const "var_res_prog_call_by_value_arg"


fun var_res_mk_local_var (var,term) =
   mk_icomb (var_res_prog_local_var_term, mk_abs (var, term));

fun dest_var_res_prog_local_var t = dest_abs (strip_comb_1 var_res_prog_local_var_term t);
val is_var_res_prog_local_var = can dest_var_res_prog_local_var


fun var_res_mk_call_by_value_arg ((arg,expr),term) =
   list_mk_icomb (var_res_prog_call_by_value_arg_term, [mk_abs (arg, term), expr]);

fun dest_var_res_prog_call_by_value_arg t = 
let
   val (tt, c) = strip_comb_2 var_res_prog_call_by_value_arg_term t;
   val (v, body) = dest_abs tt;
in
   (c,v,body)
end;
val is_var_res_prog_call_by_value_arg = can dest_var_res_prog_call_by_value_arg


(*
val t =
   ``var_res_prog_call_by_value_arg
    (\(a :holfoot_var).
       var_res_prog_call_by_value_arg
         (\(z :holfoot_var).
            var_res_prog_local_var
              (\(y :holfoot_var).
                 var_res_prog_local_var
                   (\(x :holfoot_var).
                      holfoot_prog_dispose (var_res_exp_var x)))) (5 :
         num)) (3 :num)``
*)

fun var_res_strip_local_vars t = 
    let
       val (op_term, args) = strip_comb t;
    in
       if (same_const op_term var_res_prog_call_by_value_arg_term) then (
         let
	     val (arg1, arg2) = (el 1 args, el 2 args);
	     val (v, t') = dest_abs arg1;
             val (l, t'') = var_res_strip_local_vars t';
         in
	     ((v,SOME arg2)::l, t'')
         end
       ) else if (same_const op_term var_res_prog_local_var_term) then (
         let
	     val arg1 = el 1 args;
	     val (v, t') = dest_abs arg1;
             val (l, t'') = var_res_strip_local_vars t';
         in
	     ((v,NONE)::l, t'')
         end
       ) else ([],t)
    end handle HOL_ERR _ => ([], t);


fun var_res_mk_local_vars [] t = t
  | var_res_mk_local_vars ((v, NONE)::L) t =
       var_res_mk_local_var (v, var_res_mk_local_vars L t)
  | var_res_mk_local_vars ((v, SOME e)::L) t =
       var_res_mk_call_by_value_arg ((v,e), var_res_mk_local_vars L t);


val VAR_RES_HOARE_TRIPLE_term = var_res_mk_const "VAR_RES_HOARE_TRIPLE";
val dest_VAR_RES_HOARE_TRIPLE = strip_comb_5 VAR_RES_HOARE_TRIPLE_term;
val is_VAR_RES_HOARE_TRIPLE = (can dest_VAR_RES_HOARE_TRIPLE);

val VAR_RES_COND_HOARE_TRIPLE_term = var_res_mk_const "VAR_RES_COND_HOARE_TRIPLE";
val dest_VAR_RES_COND_HOARE_TRIPLE = strip_comb_4 VAR_RES_COND_HOARE_TRIPLE_term;
val is_VAR_RES_COND_HOARE_TRIPLE = (can dest_VAR_RES_COND_HOARE_TRIPLE);


fun VAR_RES_COND_HOARE_TRIPLE___location_inc_CONV tt =
let
   val (f,pre,prog,post) = dest_VAR_RES_COND_HOARE_TRIPLE tt;
   val (p1, pL) = listSyntax.dest_cons (dest_asl_prog_block prog)   
   val (c, p1') = dest_asl_comment_location p1;
   val p1_thm = ISPECL [c, p1'] separationLogicTheory.asl_comment_location_def

   val c' = separationLogicLib.asl_comment_modify_INC c;
   val pL_thm = ((if listSyntax.is_cons pL then
                   (RATOR_CONV o RAND_CONV) else I)
                (asl_comment_location_INTRO_CONV c')) pL

   val thm = ((RATOR_CONV o RAND_CONV o RAND_CONV) 
              ((RAND_CONV (K pL_thm)) THENC
               ((RATOR_CONV o RAND_CONV) (K p1_thm)))) tt
in
   thm
end;

fun dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND tt =
let
   val (f,pre,prog,post) = dest_VAR_RES_COND_HOARE_TRIPLE tt;
   val (p1, pL) = listSyntax.dest_cons (dest_asl_prog_block prog)   
in
   (p1, pL, f, pre, post)
end;

fun dest_VAR_RES_COND_HOARE_TRIPLE___FIRST_COMMAND_location tt =
let
   val (f,pre,prog,post) = dest_VAR_RES_COND_HOARE_TRIPLE tt;
   val (p1, pL) = listSyntax.dest_cons (dest_asl_prog_block prog)   
   
   val (p1', c_opt, thm_fun) = if not (is_asl_comment_location p1) then
       (p1, NONE, fn () => REFL tt) else
       let
          val (c, p1') = dest_asl_comment_location p1;
       in
          (p1', SOME c, fn () => VAR_RES_COND_HOARE_TRIPLE___location_inc_CONV tt)
       end
in
   (p1', c_opt, f, pre, post, thm_fun)
end;

fun mk_VAR_RES_COND_HOARE_TRIPLE (f, P, prog, Q) = 
list_mk_icomb (VAR_RES_COND_HOARE_TRIPLE_term, [f, P, prog, Q])



val var_res_prog_assign_term = var_res_mk_const "var_res_prog_assign";
val dest_var_res_prog_assign = strip_comb_2 var_res_prog_assign_term;
val is_var_res_prog_assign = (can dest_var_res_prog_assign);



val var_res_prog_aquire_lock_internal_term  = var_res_mk_const "var_res_prog_aquire_lock_internal";
val var_res_prog_release_lock_internal_term = var_res_mk_const "var_res_prog_release_lock_internal";
val var_res_prog_aquire_lock_term           = var_res_mk_const "var_res_prog_aquire_lock";
val var_res_prog_release_lock_term          = var_res_mk_const "var_res_prog_release_lock";
val var_res_prog_aquire_lock_input_term     = var_res_mk_const "var_res_prog_aquire_lock_input";
val var_res_prog_release_lock_input_term    = var_res_mk_const "var_res_prog_release_lock_input";

val dest_var_res_prog_release_lock_input = strip_comb_3 var_res_prog_release_lock_input_term;
val is_var_res_prog_release_lock_input = (can dest_var_res_prog_release_lock_input)

val dest_var_res_prog_release_lock_internal = strip_comb_3 var_res_prog_release_lock_internal_term;
val is_var_res_prog_release_lock_internal = (can dest_var_res_prog_release_lock_internal)

val dest_var_res_prog_release_lock = strip_comb_3 var_res_prog_release_lock_term;
val is_var_res_prog_release_lock = (can dest_var_res_prog_release_lock)

val dest_var_res_prog_aquire_lock_input = strip_comb_4 var_res_prog_aquire_lock_input_term;
val is_var_res_prog_aquire_lock_input = (can dest_var_res_prog_aquire_lock_input)

val dest_var_res_prog_aquire_lock_internal = strip_comb_4 var_res_prog_aquire_lock_internal_term;
val is_var_res_prog_aquire_lock_internal = (can dest_var_res_prog_aquire_lock_internal)

val dest_var_res_prog_aquire_lock = strip_comb_4 var_res_prog_aquire_lock_term;
val is_var_res_prog_aquire_lock = (can dest_var_res_prog_aquire_lock)



val var_res_prog_eval_expressions_term = var_res_mk_const "var_res_prog_eval_expressions";
val dest_var_res_prog_eval_expressions = strip_comb_2 var_res_prog_eval_expressions_term;
val is_var_res_prog_eval_expressions = can dest_var_res_prog_eval_expressions;




val var_res_cond_best_local_action_term =  var_res_mk_const "var_res_cond_best_local_action";
val dest_var_res_cond_best_local_action = strip_comb_3 var_res_cond_best_local_action_term;
val is_var_res_cond_best_local_action = (can dest_var_res_cond_best_local_action);

val var_res_best_local_action_term =  var_res_mk_const "var_res_best_local_action";
val dest_var_res_best_local_action = strip_comb_3 var_res_best_local_action_term;
val is_var_res_best_local_action = (can dest_var_res_best_local_action);


val var_res_prog_best_local_action_term = var_res_mk_const "var_res_prog_best_local_action";
val dest_var_res_prog_best_local_action = strip_comb_2 var_res_prog_best_local_action_term;
val is_var_res_prog_best_local_action = (can dest_var_res_prog_best_local_action);

val var_res_prog_quant_best_local_action_term = var_res_mk_const "var_res_prog_quant_best_local_action";
val dest_var_res_prog_quant_best_local_action = strip_comb_2 var_res_prog_quant_best_local_action_term;
val is_var_res_prog_quant_best_local_action = (can dest_var_res_prog_quant_best_local_action);


val var_res_prog_cond_best_local_action_term = var_res_mk_const "var_res_prog_cond_best_local_action";
val dest_var_res_prog_cond_best_local_action = strip_comb_2 var_res_prog_cond_best_local_action_term;
val is_var_res_prog_cond_best_local_action = (can dest_var_res_prog_cond_best_local_action);

val var_res_prog_cond_quant_best_local_action_term = var_res_mk_const "var_res_prog_cond_quant_best_local_action";
val dest_var_res_prog_cond_quant_best_local_action = strip_comb_2 var_res_prog_cond_quant_best_local_action_term;
val is_var_res_prog_cond_quant_best_local_action = (can dest_var_res_prog_cond_quant_best_local_action);


val dest_var_res_prog_procedure_call = strip_comb_2 var_res_prog_procedure_call_term;
val is_var_res_prog_procedure_call = (can dest_var_res_prog_procedure_call);

val dest_var_res_prog_parallel_procedure_call = strip_comb_4 var_res_prog_parallel_procedure_call_term;
val is_var_res_prog_parallel_procedure_call = (can dest_var_res_prog_parallel_procedure_call);


val var_res_map_term = var_res_mk_const "var_res_map";

val var_res_prop_internal_term = var_res_mk_const "var_res_prop_internal";
fun dest_var_res_prop_internal tt =
  let
     val (f,wpbrpb,wprp,d,sfb,P) = strip_comb_6 var_res_prop_internal_term tt;
     val (wpb, rpb) = safe_dest_pair wpbrpb;
     val (wp, rp) = safe_dest_pair wprp;
  in
    (f,wpb,rpb,wp,rp,d,sfb,P)
  end;
val is_var_res_prop_internal = (can dest_var_res_prop_internal);


val var_res_prop_term = var_res_mk_const "var_res_prop";
fun dest_var_res_prop tt =
  let
     val (f, wprp, sfb) = strip_comb_3 var_res_prop_term tt;
     val (wp, rp) = safe_dest_pair wprp;
  in
    (f, wp,rp, sfb)
  end
val is_var_res_prop = (can dest_var_res_prop);

fun dest_var_res_prop___propL tt =
let   
   val (f, wp, rp, sfb) = dest_var_res_prop tt;
   val sfs = fst (bagSyntax.dest_bag sfb);
in 
   (f, wp, rp, sfb, sfs)
end;


val var_res_implies_unequal_term = var_res_mk_const "var_res_implies_unequal"
val dest_var_res_implies_unequal = strip_comb_4 var_res_implies_unequal_term
val is_var_res_implies_unequal = can dest_var_res_implies_unequal

fun is_var_res_implies_unequal_sym e1 e2 tt = 
let
   val (_, _, e1', e2') = dest_var_res_implies_unequal tt;
in
   ((aconv e1 e1') andalso (aconv e2 e2')) orelse
   ((aconv e1 e2') andalso (aconv e2 e1'))
end handle HOL_ERR _ => false


val var_res_prop_implies_term = var_res_mk_const "var_res_prop_implies"
fun dest_var_res_prop_implies tt =
  let
     val (f, wprp, sfb, sfb') = strip_comb_4 var_res_prop_implies_term tt;
     val (wp, rp) = safe_dest_pair wprp;
  in
    (f, wp,rp, sfb,sfb')
  end
val is_var_res_prop_implies = (can dest_var_res_prop_implies);

val var_res_prop_implies_eq_term = var_res_mk_const "var_res_prop_implies_eq"
fun dest_var_res_prop_implies_eq tt =
  let
     val (f, wprp, sfb, sfb1, sfb1') = strip_comb_5 var_res_prop_implies_eq_term tt;
     val (wp, rp) = safe_dest_pair wprp;
  in
    (f, wp,rp, sfb,sfb1,sfb1')
  end
val is_var_res_prop_implies_eq = (can dest_var_res_prop_implies_eq);


val var_res_prop_input_ap_distinct_term = var_res_mk_const "var_res_prop_input_ap_distinct";
val dest_var_res_prop_input_ap_distinct = strip_comb_4 var_res_prop_input_ap_distinct_term;
val is_var_res_prop_input_ap_distinct = (can dest_var_res_prop_input_ap_distinct);
val var_res_prop_input_ap_term = var_res_mk_const "var_res_prop_input_ap";


val var_res_prop_input_distinct_term = var_res_mk_const "var_res_prop_input_distinct";
val dest_var_res_prop_input_distinct = strip_comb_4 var_res_prop_input_distinct_term;
val is_var_res_prop_input_distinct = (can dest_var_res_prop_input_distinct);



val VAR_RES_FRAME_SPLIT_term = var_res_mk_const "VAR_RES_FRAME_SPLIT";
val dest_VAR_RES_FRAME_SPLIT = strip_comb_8 VAR_RES_FRAME_SPLIT_term;
val is_VAR_RES_FRAME_SPLIT = (can dest_VAR_RES_FRAME_SPLIT);


val VAR_RES_PROP_IS_EQUIV_FALSE_term = var_res_mk_const "VAR_RES_PROP_IS_EQUIV_FALSE";
val dest_VAR_RES_PROP_IS_EQUIV_FALSE = strip_comb_4 VAR_RES_PROP_IS_EQUIV_FALSE_term;
val is_VAR_RES_PROP_IS_EQUIV_FALSE = (can dest_VAR_RES_PROP_IS_EQUIV_FALSE);


val VAR_RES_IS_STACK_IMPRECISE___USED_VARS_term = var_res_mk_const "VAR_RES_IS_STACK_IMPRECISE___USED_VARS";
val dest_VAR_RES_IS_STACK_IMPRECISE___USED_VARS = strip_comb_2 VAR_RES_IS_STACK_IMPRECISE___USED_VARS_term;
val is_VAR_RES_IS_STACK_IMPRECISE___USED_VARS = can dest_VAR_RES_IS_STACK_IMPRECISE___USED_VARS;
fun mk_VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs p =
   list_mk_icomb (VAR_RES_IS_STACK_IMPRECISE___USED_VARS_term, [vs,p])


val VAR_RES_IS_STACK_IMPRECISE_term = var_res_mk_const "VAR_RES_IS_STACK_IMPRECISE";
val dest_VAR_RES_IS_STACK_IMPRECISE = strip_comb_1 VAR_RES_IS_STACK_IMPRECISE_term;
val is_VAR_RES_IS_STACK_IMPRECISE = can dest_VAR_RES_IS_STACK_IMPRECISE;


fun inst_type_to_type ty t =
   inst (match_type (type_of t) ty) t

val var_res_exp_var_term  = var_res_mk_const "var_res_exp_var";
val dest_var_res_exp_var = strip_comb_1 var_res_exp_var_term;
val is_var_res_exp_var = can dest_var_res_exp_var;

fun mk_var_res_exp_var v ty = 
   inst_type_to_type ty (mk_icomb(var_res_exp_var_term, v));

val var_res_exp_const_term = var_res_mk_const "var_res_exp_const";
val dest_var_res_exp_const = strip_comb_1 var_res_exp_const_term;
val is_var_res_exp_const = can dest_var_res_exp_const;
fun mk_var_res_exp_const c ty = inst_type_to_type ty 
   (mk_icomb(var_res_exp_const_term, c));


val var_res_exp_op_term = var_res_mk_const "var_res_exp_op";

val var_res_exp_binop_term = var_res_mk_const "var_res_exp_binop";
val dest_var_res_exp_binop = strip_comb_2 var_res_exp_binop_term;
val is_var_res_exp_binop = can dest_var_res_exp_binop;


val VAR_RES_IS_PURE_PROPOSITION_term = var_res_mk_const "VAR_RES_IS_PURE_PROPOSITION";
val dest_VAR_RES_IS_PURE_PROPOSITION = strip_comb_2 VAR_RES_IS_PURE_PROPOSITION_term;
val is_VAR_RES_IS_PURE_PROPOSITION = can dest_VAR_RES_IS_PURE_PROPOSITION;
fun mk_VAR_RES_IS_PURE_PROPOSITION f p = 
   list_mk_icomb (VAR_RES_IS_PURE_PROPOSITION_term, [f, p])


val var_res_pred_term = var_res_mk_const "var_res_pred";
val var_res_pred_bin_term = var_res_mk_const "var_res_pred_bin";

fun string2num_var s = mk_var(s, numLib.num);


val var_res_prop___var_eq_const_BAG_term =
   var_res_mk_const "var_res_prop___var_eq_const_BAG"

val var_res_prop_varlist_update_term =
   var_res_mk_const "var_res_prop_varlist_update"
val dest_var_res_prop_varlist_update = strip_comb_2 var_res_prop_varlist_update_term
val is_var_res_prop_varlist_update = can dest_var_res_prop_varlist_update

val var_res_exp_varlist_update_term =
   var_res_mk_const "var_res_exp_varlist_update"
val dest_var_res_exp_varlist_update = strip_comb_2 var_res_exp_varlist_update_term
val is_var_res_exp_varlist_update = can dest_var_res_exp_varlist_update


fun dest_var_res_state_type ty =
   let
      val (var_ty, x) = finite_mapSyntax.dest_fmap_ty ty
      val (data_ty, _) = pairSyntax.dest_prod x
   in
      (var_ty, data_ty)
   end;

fun dest_var_res_expr_type ty =
   dest_var_res_state_type (hd (fst (strip_fun ty)))

local
   val org_ty = Type `:('a, 'b, 'a) var_res_expression`;
in
fun mk_var_res_expr_type state_ty =
let
   val (var_ty, data_ty) = dest_var_res_state_type state_ty
in
   type_subst [beta |-> var_ty, alpha |-> data_ty] org_ty
end;
end
 
fun dest_var_res_ext_state_type ty =
   pairSyntax.dest_prod ty

fun dest_var_res_proposition ty =
   (hd (fst (strip_fun ty)))

fun dest_var_res_cond_proposition ty =
   dest_var_res_proposition (snd (pairSyntax.dest_prod ty))







end
