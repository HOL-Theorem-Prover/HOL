structure smallfootSyntax :> smallfootSyntax =
struct

(*
quietdec := true;
loadPath := 
            (concat Globals.HOLDIR "/examples/separationLogic/src") :: 
            (concat Globals.HOLDIR "/examples/separationLogic/src/smallfoot") :: 
            !loadPath;

map load ["finite_mapTheory", "smallfootTheory"];
show_assums := true;
*)

open HolKernel Parse boolLib finite_mapTheory smallfootTheory;


(*
quietdec := false;
*)


val smallfoot_var_term = ``smallfoot_var``;
val smallfoot_tag_term = ``smallfoot_tag``;
val smallfoot_p_var_term = ``smallfoot_p_var``;
val smallfoot_p_const_term = ``smallfoot_p_const``;
val smallfoot_p_add_term = ``smallfoot_p_add``;
val smallfoot_p_sub_term = ``smallfoot_p_sub``;

val smallfoot_p_equal_term = ``smallfoot_p_equal``;
val smallfoot_p_unequal_term = ``smallfoot_p_unequal``;
val smallfoot_p_less_term = ``smallfoot_p_less``;
val smallfoot_p_lesseq_term = ``smallfoot_p_lesseq``;
val smallfoot_p_greater_term = ``smallfoot_p_greater``;
val smallfoot_p_greatereq_term = ``smallfoot_p_greatereq``;
val smallfoot_p_neg_term = ``smallfoot_p_neg``;
val smallfoot_p_and_term = ``smallfoot_p_and``;
val smallfoot_p_or_term = ``smallfoot_p_or``;


fun string2smallfoot_const s =
	mk_var(s, numLib.num);

fun string2smallfoot_var s =
	mk_comb (smallfoot_var_term, stringLib.fromMLstring s);

fun string2smallfoot_tag s =
	mk_comb (smallfoot_tag_term, stringLib.fromMLstring s);

val smallfoot_ae_var_term = ``smallfoot_ae_var``;
val smallfoot_ae_const_term = ``smallfoot_ae_const``;
val smallfoot_ae_null_term = ``smallfoot_ae_null``;


val smallfoot_ap_list_term = ``smallfoot_ap_list``;
val smallfoot_ap_list_seg_term = ``smallfoot_ap_list_seg``;
val smallfoot_ap_data_list_term = ``smallfoot_ap_data_list``;
val smallfoot_ap_data_list_seg_term = ``smallfoot_ap_data_list_seg``;
val smallfoot_ap_bintree_term = ``smallfoot_ap_bintree``;
val smallfoot_ap_list_seg_term = ``smallfoot_ap_list_seg``
val smallfoot_ap_emp_term = ``smallfoot_ap_emp``;
val smallfoot_ap_unknown_term = ``smallfoot_ap_unknown``;
val smallfoot_ap_points_to_term = ``smallfoot_ap_points_to``;
val smallfoot_ap_stack_true_term = ``smallfoot_ap_stack_true``;

val smallfoot_ap_equal_term = ``smallfoot_ap_equal``;
val smallfoot_ap_unequal_term = ``smallfoot_ap_unequal``;
val smallfoot_ap_less_term = ``smallfoot_ap_less``;
val smallfoot_ap_lesseq_term = ``smallfoot_ap_lesseq``;
val smallfoot_ap_greater_term = ``smallfoot_ap_greater``;
val smallfoot_ap_greatereq_term = ``smallfoot_ap_greatereq``;
val smallfoot_ap_false_term = ``smallfoot_ap_false``;
val smallfoot_ap_cond_term = ``smallfoot_ap_cond``;
val smallfoot_ap_unequal_cond_term = ``smallfoot_ap_unequal_cond``;
val smallfoot_ap_equal_cond_term = ``smallfoot_ap_equal_cond``;
val smallfoot_ap_star_term = ``smallfoot_ap_star``;
val smallfoot_ap_bigstar_term = ``smallfoot_ap_bigstar``;
val smallfoot_ap_bigstar_list_term = ``smallfoot_ap_bigstar_list``;


val smallfoot_prog_assign_term = ``smallfoot_prog_assign``;
val smallfoot_prog_field_lookup_term = ``smallfoot_prog_field_lookup``;
val smallfoot_prog_field_assign_term = ``smallfoot_prog_field_assign``;
val smallfoot_prog_new_term = ``smallfoot_prog_new``;
val smallfoot_prog_dispose_term = ``smallfoot_prog_dispose``;
val smallfoot_prog_block_term = ``smallfoot_prog_block``;
val smallfoot_prog_cond_term = ``smallfoot_prog_cond``;
val smallfoot_prog_while_term = ``smallfoot_prog_while`` 
val smallfoot_prog_while_with_invariant_term = ``smallfoot_prog_while_with_invariant`` 
val smallfoot_prog_procedure_call_term = ``smallfoot_prog_procedure_call`` 
val smallfoot_prog_parallel_procedure_call_term = ``smallfoot_prog_parallel_procedure_call`` 
val smallfoot_prog_parallel_term = ``smallfoot_prog_parallel``;
val smallfoot_prog_local_var_term = ``$smallfoot_prog_local_var``
val smallfoot_prog_val_arg_term = ``$smallfoot_prog_val_arg``
val smallfoot_prog_with_resource_term = ``smallfoot_prog_with_resource``;
val smallfoot_prog_aquire_resource_internal_term = ``smallfoot_prog_aquire_resource_internal``;
val smallfoot_prog_release_resource_internal_term = ``smallfoot_prog_release_resource_internal``;
val smallfoot_prog_aquire_resource_term = ``smallfoot_prog_aquire_resource``;
val smallfoot_prog_release_resource_term = ``smallfoot_prog_release_resource``;

val smallfoot_prop_input_ap_term = ``smallfoot_prop_input_ap``;
val smallfoot_prop_input_ap_distinct_term = ``smallfoot_prop_input_ap_distinct``;
val smallfoot_input_preserve_names_wrapper_term = ``smallfoot_input_preserve_names_wrapper``

fun smallfoot_mk_var_abs (var, term) =
	let
		val sm_var_term = string2smallfoot_var var;
		val var_term = variant (free_vars term) (mk_var (var, Type `:smallfoot_var`));
		val term1 = subst [sm_var_term |-> var_term] term;
		val term2 = mk_abs (var_term, term1)
	in
		term2
	end;

fun smallfoot_mk_local_var (var,term) =
	let
		val term' = smallfoot_mk_var_abs (var, term);
	in
		mk_comb (smallfoot_prog_local_var_term, term')
	end;


fun smallfoot_mk_val_arg ((arg,expr),term) =
	let
		val term' = smallfoot_mk_var_abs (arg, term);
	in
 		list_mk_comb (smallfoot_prog_val_arg_term, [term', expr])
	end;

val smallfoot_p_expression_eval_term = ``SMALLFOOT_P_EXPRESSION_EVAL``

fun dest_smallfoot_tag t =
    let
	val (op_term, arg) = dest_comb t;
        val _ = if (op_term = smallfoot_tag_term) then () else
                (raise (ERR "dest_smallfoot_tag" "no tag term!"));
    in 
        arg
    end;

fun dest_smallfoot_var t =
    let
	val (op_term, arg) = dest_comb t;
        val _ = if (op_term = smallfoot_var_term) then () else
                (raise (ERR "dest_smallfoot_var" "no var term!"));
    in 
        arg
    end;
val is_smallfoot_var = can dest_smallfoot_var


fun dest_local_vars t = 
    let
       val (op_term, args) = strip_comb t;
    in
       if (op_term = smallfoot_prog_val_arg_term) then (
         let
	     val (arg1, arg2) = (el 1 args, el 2 args);
	     val (v, t') = dest_abs arg1;
             val (l, t'') = dest_local_vars t';
         in
	     ((v,SOME arg2)::l, t'')
         end
       ) else if (op_term = smallfoot_prog_local_var_term) then (
         let
	     val arg1 = el 1 args;
	     val (v, t') = dest_abs arg1;
             val (l, t'') = dest_local_vars t';
         in
	     ((v,NONE)::l, t'')
         end
       ) else ([],t)
    end handle HOL_ERR _ => ([], t);



val FEMPTY_tm = ``FEMPTY``;
val FUPDATE_tm = ``$FUPDATE``;


fun dest_finite_map t = 
    let
	val (op_term, args) = strip_comb t;
    in
       if (same_const op_term FUPDATE_tm) then
	   let
	       val (slist, rest) = (dest_finite_map (el 1 args));
	   in
               ((pairLib.dest_pair (el 2 args))::slist, rest)
	   end
       else if (same_const op_term FEMPTY_tm) then ([], NONE)
       else ([], SOME t) 
    end handle _ => ([], SOME t);



val smallfoot_p_proposition_type = Type `:smallfoot_p_proposition`;
val smallfoot_prog_type = Type `:smallfoot_prog`;
val smallfoot_var_type = Type `:smallfoot_var`;
val smallfoot_p_expression_type = Type `:smallfoot_p_expression`;
val smallfoot_tag_type = Type `:smallfoot_tag`;
val smallfoot_a_expression_type = Type `:smallfoot_a_expression`;
val smallfoot_a_proposition_type = Type `:smallfoot_a_proposition`;

fun save_dest_pair t =
  pairLib.dest_pair t handle HOL_ERR _ =>
  (pairLib.mk_fst t, pairLib.mk_snd t);




val FASL_PROGRAM_HOARE_TRIPLE_term = ``FASL_PROGRAM_HOARE_TRIPLE``;
fun dest_FASL_PROGRAM_HOARE_TRIPLE tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f FASL_PROGRAM_HOARE_TRIPLE_term) andalso
	        (length args = 5) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_FASL_PROGRAM_HOARE_TRIPLE" "Wrong Term")
  in
    (el 1 args, el 2 args, el 3 args, el 4 args, el 5 args)
  end;
val is_FASL_PROGRAM_HOARE_TRIPLE = (can dest_FASL_PROGRAM_HOARE_TRIPLE);



val SMALLFOOT_COND_HOARE_TRIPLE_term = ``SMALLFOOT_COND_HOARE_TRIPLE``;
fun dest_SMALLFOOT_COND_HOARE_TRIPLE tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f SMALLFOOT_COND_HOARE_TRIPLE_term) andalso
	        (length args = 3) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_SMALLFOOT_COND_HOARE_TRIPLE" "Wrong Term")
  in
    (el 1 args, el 2 args, el 3 args)
  end;
val is_SMALLFOOT_COND_HOARE_TRIPLE = (can dest_SMALLFOOT_COND_HOARE_TRIPLE);



val SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE_term = 
   ``SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE``;
fun dest_SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE_term) andalso
	        (length args = 1) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE" "Wrong Term");

     val (vL, b) = strip_abs (el 1 args);
     val _ = if (length vL = 2) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE" "Wrong Term");

  in
    (el 1 vL, el 2 vL, b)
  end;
val is_SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE = (can dest_SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE);



val SMALLFOOT_HOARE_TRIPLE_term = ``SMALLFOOT_HOARE_TRIPLE``;
fun dest_SMALLFOOT_HOARE_TRIPLE tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f SMALLFOOT_HOARE_TRIPLE_term) andalso
	        (length args = 5) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_SMALLFOOT_HOARE_TRIPLE" "Wrong Term")
  in
    (el 1 args, el 2 args, el 3 args, el 4 args, el 5 args)
  end;
val is_SMALLFOOT_HOARE_TRIPLE = (can dest_SMALLFOOT_HOARE_TRIPLE);



val fasl_prog_seq_term = ``fasl_prog_seq``;

fun dest_FASL_PROG_SEQ tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f fasl_prog_seq_term) andalso
	        (length args = 2) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_FASL_PROG_SEQ" "No Prog-Sequence")
  in
    (el 1 args, el 2 args)
  end;

val is_FASL_PROG_SEQ = (can dest_FASL_PROG_SEQ);


fun dest_smallfoot_prog_val_arg tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f smallfoot_prog_val_arg_term) andalso
	        (length args = 2) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_smallfoot_prog_val_arg" "No VAL-ARG")
     val (v, pp) = dest_abs (el 1 args);
  in
    (v, pp, el 2 args)
  end;

val is_smallfoot_prog_val_arg = (can dest_smallfoot_prog_val_arg);



fun dest_smallfoot_prog_local_var tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f smallfoot_prog_local_var_term) andalso
	        (length args = 1) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_smallfoot_prog_local_var" "No local variable")
     val (v, pp) = dest_abs (el 1 args);
  in
    (v, pp)
  end;

val is_smallfoot_prog_local_var = (can dest_smallfoot_prog_local_var);


val fasl_prog_block_term = ``fasl_prog_block``;
fun dest_fasl_prog_block tt =
  let
     val (f, arg) = dest_comb tt;
     val _ = if (same_const f fasl_prog_block_term) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_fasl_prog_block" "No block")
  in
    arg
  end;

val is_fasl_prog_block = (can dest_fasl_prog_block);
fun mk_fasl_prog_block t = mk_icomb (fasl_prog_block_term, t);



fun dest_smallfoot_prog_block tt =
  let
     val (f, arg) = dest_comb tt;
     val _ = if (same_const f smallfoot_prog_block_term) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_smallfoot_prog_block" "No block")
  in
    arg
  end;

val is_smallfoot_prog_block = (can dest_smallfoot_prog_block);


fun dest_smallfoot_prog_assign tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f smallfoot_prog_assign_term) andalso
	        (length args = 2) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_smallfoot_prog_assign" "Wrong term")
  in
    (el 1 args, el 2 args)
  end;
val is_smallfoot_prog_assign = (can dest_smallfoot_prog_assign);



fun dest_smallfoot_prog_new tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f smallfoot_prog_new_term) andalso
	        (length args = 1) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_smallfoot_prog_new" "Wrong term")
  in
    (el 1 args)
  end;
val is_smallfoot_prog_new = (can dest_smallfoot_prog_new);




fun dest_smallfoot_prog_field_lookup tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f smallfoot_prog_field_lookup_term) andalso
	        (length args = 3) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_smallfoot_prog_field_lookup" "Wrong term")
  in
    (el 1 args, el 2 args, el 3 args)
  end;
val is_smallfoot_prog_field_lookup = (can dest_smallfoot_prog_field_lookup);


fun dest_smallfoot_prog_field_assign tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f smallfoot_prog_field_assign_term) andalso
	        (length args = 3) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_smallfoot_prog_field_assign" "Wrong term")
  in
    (el 1 args, el 2 args, el 3 args)
  end;
val is_smallfoot_prog_field_assign = (can dest_smallfoot_prog_field_assign);


fun dest_smallfoot_prog_dispose tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f smallfoot_prog_dispose_term) andalso
	        (length args = 1) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_smallfoot_prog_field_dispose" "Wrong term")
  in
    (el 1 args)
  end;
val is_smallfoot_prog_dispose = (can dest_smallfoot_prog_dispose);



val FASL_PROGRAM_IS_ABSTRACTION_term = ``FASL_PROGRAM_IS_ABSTRACTION``;
fun dest_FASL_PROGRAM_IS_ABSTRACTION tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f FASL_PROGRAM_IS_ABSTRACTION_term) andalso
	        (length args = 4) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_FASL_PROGRAM_IS_ABSTRACTION" "Wrong term")
  in
    (el 1 args, el 2 args, el 3 args, el 4 args)
  end
val is_FASL_PROGRAM_IS_ABSTRACTION = (can dest_FASL_PROGRAM_IS_ABSTRACTION);
fun mk_FASL_PROGRAM_IS_ABSTRACTION (xenv,penv,x,y) = 
   list_mk_icomb(FASL_PROGRAM_IS_ABSTRACTION_term, [xenv,penv,x,y]);



val fasl_prog_cond_term = ``fasl_prog_cond``;
fun dest_fasl_prog_cond tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f fasl_prog_cond_term) andalso
	        (length args = 3) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_fasl_prog_cond" "Wrong term")
  in
    (el 1 args, el 2 args, el 3 args)
  end
val is_fasl_prog_cond = (can dest_fasl_prog_cond);
fun mk_fasl_prog_cond (c,p1,p2) = 
   list_mk_icomb(fasl_prog_cond_term, [c,p1,p2]);


fun dest_smallfoot_prog_cond tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f smallfoot_prog_cond_term) andalso
	        (length args = 3) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_smallfoot_prog_cond" "Wrong term")
  in
    (el 1 args, el 2 args, el 3 args)
  end
val is_smallfoot_prog_cond = (can dest_smallfoot_prog_cond);


val fasl_prog_while_with_invariant_term = ``fasl_prog_while_with_invariant``;
fun dest_fasl_prog_while_with_invariant tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f fasl_prog_while_with_invariant_term) andalso
	        (length args = 3) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_fasl_prog_while_with_invariant" "Wrong term");
  in
    (el 1 args, el 2 args, el 3 args)
  end
val is_fasl_prog_while_with_invariant = (can dest_fasl_prog_while_with_invariant);
fun mk_fasl_prog_while_with_invariant (i,c,p) = 
   list_mk_icomb(fasl_prog_while_with_invariant_term, [i,c,p]);


fun dest_smallfoot_prog_with_resource tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f smallfoot_prog_with_resource_term) andalso
	        (length args = 3) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_smallfoot_prog_with_resource" "Wrong term")
  in
    (el 1 args, el 2 args, el 3 args)
  end
val is_smallfoot_prog_with_resource = (can dest_smallfoot_prog_with_resource)



fun dest_smallfoot_prog_release_resource tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f smallfoot_prog_release_resource_term) andalso
	        (length args = 2) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_smallfoot_prog_release_resource" "Wrong term")
  in
    (el 1 args, el 2 args)
  end
val is_smallfoot_prog_release_resource = (can dest_smallfoot_prog_release_resource)




val smallfoot_choose_const_best_local_action_term = 
   ``smallfoot_choose_const_best_local_action``;

fun dest_smallfoot_choose_const_best_local_action tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f smallfoot_choose_const_best_local_action_term) andalso
	        (length args = 5) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_smallfoot_choose_const_best_local_action" "Wrong term")
  in
    (el 1 args, el 2 args, el 3 args, el 4 args,  el 5 args)
  end
val is_smallfoot_choose_const_best_local_action = (can dest_smallfoot_choose_const_best_local_action);




val smallfoot_cond_best_local_action_term = 
   ``smallfoot_cond_best_local_action``;

fun dest_smallfoot_cond_best_local_action tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f smallfoot_cond_best_local_action_term) andalso
	        (length args = 2) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_smallfoot_cond_best_local_action" "Wrong term")
  in
    (el 1 args, el 2 args)
  end
val is_smallfoot_cond_best_local_action = (can dest_smallfoot_cond_best_local_action);





val fasl_prog_best_local_action_term = 
   ``fasl_prog_best_local_action``;

fun dest_fasl_prog_best_local_action tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f fasl_prog_best_local_action_term) andalso
	        (length args = 2) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_fasl_prog_best_local_action" "Wrong term")
  in
    (el 1 args, el 2 args)
  end
val is_fasl_prog_best_local_action = (can dest_fasl_prog_best_local_action);



val smallfoot_prog_best_local_action_term = 
   ``smallfoot_prog_best_local_action``;

fun dest_smallfoot_prog_best_local_action tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f smallfoot_prog_best_local_action_term) andalso
	        (length args = 2) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_smallfoot_prog_best_local_action" "Wrong term")
  in
    (el 1 args, el 2 args)
  end
val is_smallfoot_prog_best_local_action = (can dest_smallfoot_prog_best_local_action);


val smallfoot_parallel_proc_call_abstraction_term = 
   ``smallfoot_parallel_proc_call_abstraction``;

fun dest_smallfoot_parallel_proc_call_abstraction tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f smallfoot_parallel_proc_call_abstraction_term) andalso
	        (length args = 8) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_smallfoot_parallel_proc_call_abstraction" "Wrong term")
     val (ref1,val1) = save_dest_pair (el 3 args);
     val (ref2,val2) = save_dest_pair (el 7 args);
  in
    (el 1 args, el 2 args, el 4 args, ref1, val1,
     el 5 args, el 7 args, el 8 args, ref2, val2)
  end
val is_smallfoot_parallel_proc_call_abstraction = (can dest_smallfoot_parallel_proc_call_abstraction);



val smallfoot_proc_call_abstraction_term =  ``smallfoot_proc_call_abstraction``;

fun dest_smallfoot_proc_call_abstraction tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f smallfoot_proc_call_abstraction_term) andalso
	        (length args = 4) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_smallfoot_proc_call_abstraction" "Wrong term")
     val (ref_arg,val_arg) = save_dest_pair (el 3 args);
  in
    (el 1 args, el 2 args, el 4 args, ref_arg, val_arg)
  end;
val is_smallfoot_proc_call_abstraction = (can dest_smallfoot_proc_call_abstraction);





fun dest_smallfoot_prog_while_with_invariant tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f smallfoot_prog_while_with_invariant_term) andalso
	        (length args = 3) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_smallfoot_prog_while_with_invariant" "Wrong term")
     val (x1,x2) = pairLib.dest_pair (el 1 args);
  in
    (x1,x2, el 2 args, el 3 args)
  end
val is_smallfoot_prog_while_with_invariant = (can dest_smallfoot_prog_while_with_invariant);
fun mk_smallfoot_prog_while_with_invariant (fvL,qi,c,p) = 
   list_mk_icomb(smallfoot_prog_while_with_invariant_term, [pairLib.mk_pair(fvL,qi),c,p]);



val SMALLFOOT_SPECIFICATION_term = ``SMALLFOOT_SPECIFICATION``;
fun dest_SMALLFOOT_SPECIFICATION tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f SMALLFOOT_SPECIFICATION_term) andalso
	        (length args = 2) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_SMALLFOOT_SPECIFICATION" "Wrong term")
  in
    (el 1 args, el 2 args)
  end
val is_SMALLFOOT_SPECIFICATION = (can dest_SMALLFOOT_SPECIFICATION);



fun dest_smallfoot_prog_procedure_call tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f smallfoot_prog_procedure_call_term) andalso
	        (length args = 2) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_smallfoot_prog_procedure_call" "Wrong term")
     val (ra, va) = save_dest_pair (el 2 args);
  in
    (el 1 args, ra, va)
  end
val is_smallfoot_prog_procedure_call = (can dest_smallfoot_prog_procedure_call);



fun dest_smallfoot_prog_parallel_procedure_call tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f smallfoot_prog_parallel_procedure_call_term) andalso
	        (length args = 4) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_smallfoot_prog_parallel_procedure_call" "Wrong term")
     val (ra1, va1) = save_dest_pair (el 2 args);
     val (ra2, va2) = save_dest_pair (el 4 args);
  in
    (el 1 args, ra1, va1, el 3 args, ra2, va2)
  end
val is_smallfoot_prog_parallel_procedure_call = (can dest_smallfoot_prog_parallel_procedure_call);


val SMALLFOOT_SING_PROCEDURE_SPEC_term = ``SMALLFOOT_SING_PROCEDURE_SPEC``;
fun dest_SMALLFOOT_SING_PROCEDURE_SPEC tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f SMALLFOOT_SING_PROCEDURE_SPEC_term) andalso
	        (length args = 8) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_SMALLFOOT_SING_PROCEDURE_SPEC" "Wrong term")
  in
    (el 1 args, el 2 args, el 3 args, el 4 args, el 5 args, el 6 args, el 7 args, el 8 args)
  end
val is_SMALLFOOT_SING_PROCEDURE_SPEC = (can dest_SMALLFOOT_SING_PROCEDURE_SPEC);


fun dest_smallfoot_prog_parallel tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f smallfoot_prog_parallel_term) andalso
	        (length args = 2) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_smallfoot_prog_parallel" "Wrong term")
  in
    (el 1 args, el 2 args)
  end
val is_smallfoot_prog_parallel = (can dest_smallfoot_prog_parallel);



val smallfoot_cond_choose_const_best_local_action_term = ``smallfoot_cond_choose_const_best_local_action``;
fun dest_smallfoot_cond_choose_const_best_local_action tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f smallfoot_cond_choose_const_best_local_action_term) andalso
	        (length args = 5) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_smallfoot_cond_choose_const_best_local_action" "Wrong term")
  in
    (el 1 args, el 2 args,el 3 args, el 4 args,el 5 args)
  end
val is_smallfoot_cond_choose_const_best_local_action = (can dest_smallfoot_cond_choose_const_best_local_action);



val smallfoot_prop_input_term = ``smallfoot_prop_input``;
fun dest_smallfoot_prop_input tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f smallfoot_prop_input_term) andalso
	        (length args = 3) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_smallfoot_prop_input" "Wrong term")
     val (wp, rp) = save_dest_pair (el 1 args);
     val (d_list,_) = listLib.dest_list (el 2 args);
  in
    (wp,rp,d_list, el 3 args)
  end
val is_smallfoot_prop_input = (can dest_smallfoot_prop_input);



val smallfoot_prop_internal_ap_term = ``smallfoot_prop_internal_ap``;
fun dest_smallfoot_prop_internal_ap tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f smallfoot_prop_internal_ap_term) andalso
	        (length args = 4) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_smallfoot_prop_internal_ap" "Wrong term")
     val (wp, rp) = save_dest_pair (el 1 args);
  in
    (wp,rp,el 2 args, el 3 args, el 4 args)
  end
val is_smallfoot_prop_internal_ap = (can dest_smallfoot_prop_internal_ap);


val smallfoot_prop_internal_term = ``smallfoot_prop_internal``;
fun dest_smallfoot_prop_internal tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f smallfoot_prop_internal_term) andalso
	        (length args = 6) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_smallfoot_prop_internal" "Wrong term")
     val (wpb, rpb) = save_dest_pair (el 1 args);
     val (wp, rp) = save_dest_pair (el 2 args);
  in
    (wpb,rpb,wp,rp,el 3 args, el 4 args, el 5 args, el 6 args)
  end
val is_smallfoot_prop_internal = (can dest_smallfoot_prop_internal);


val smallfoot_prop_term = ``smallfoot_prop``;
fun dest_smallfoot_prop tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f smallfoot_prop_term) andalso
	        (length args = 2) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_smallfoot_prop" "Wrong term")
     val (wp, rp) = save_dest_pair (el 1 args);
  in
    (wp,rp, el 2 args)
  end
val is_smallfoot_prop = (can dest_smallfoot_prop);



val SMALLFOOT_PROP_IMPLIES_term = ``SMALLFOOT_PROP_IMPLIES``;
fun dest_SMALLFOOT_PROP_IMPLIES tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f SMALLFOOT_PROP_IMPLIES_term) andalso
	        (length args = 7) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_SMALLFOOT_PROP_IMPLIES" "Wrong term")
     val (wp, rp) = save_dest_pair (el 2 args);
  in
    (el 1 args, wp,rp, el 3 args, el 4 args, el 5 args, el 6 args, el 7 args)
  end
val is_SMALLFOOT_PROP_IMPLIES = (can dest_SMALLFOOT_PROP_IMPLIES);





val SMALLFOOT_COND_PROP___IMP_term = ``SMALLFOOT_COND_PROP___IMP``;
fun dest_SMALLFOOT_COND_PROP___IMP tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f SMALLFOOT_COND_PROP___IMP_term) andalso
	        (length args = 2) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_SMALLFOOT_COND_PROP___IMP" "Wrong Term")
  in
    (el 1 args, el 2 args)
  end;
val is_SMALLFOOT_COND_PROP___IMP = (can dest_SMALLFOOT_COND_PROP___IMP);




val SMALLFOOT_COND_PROP___EQUIV_term = ``SMALLFOOT_COND_PROP___EQUIV``;
fun dest_SMALLFOOT_COND_PROP___EQUIV tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f SMALLFOOT_COND_PROP___EQUIV_term) andalso
	        (length args = 2) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_SMALLFOOT_COND_PROP___EQUIV" "Wrong Term")
  in
    (el 1 args, el 2 args)
  end;
val is_SMALLFOOT_COND_PROP___EQUIV = (can dest_SMALLFOOT_COND_PROP___EQUIV);


val COND_PROP___STRONG_EXISTS_term = ``COND_PROP___STRONG_EXISTS``;
fun dest_COND_PROP___STRONG_EXISTS tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f COND_PROP___STRONG_EXISTS_term) andalso
	        (length args = 1) then () else
             raise (mk_HOL_ERR "smallfootSyntax" "dest_COND_PROP___STRONG_EXISTS" "Wrong term")
     val (v, body) = dest_abs (el 1 args)
  in
    (v, body)
  end
val is_COND_PROP___STRONG_EXISTS = can dest_COND_PROP___STRONG_EXISTS;



val COND_PROP___EXISTS_term = ``$COND_PROP___EXISTS``;
fun dest_COND_PROP___EXISTS tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f COND_PROP___EXISTS_term) andalso
	        (length args = 1) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_COND_PROP___EXISTS" "Wrong Term")
     val (v,b) = dest_abs (el 1 args)
  in
    (v,b)
  end;
val is_COND_PROP___EXISTS = (can dest_COND_PROP___EXISTS);



val COND_PROP___ADD_COND_term = ``COND_PROP___ADD_COND``;
fun dest_COND_PROP___ADD_COND tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f COND_PROP___ADD_COND_term) andalso
	        (length args = 2) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_COND_PROP___ADD_COND" "Wrong Term!")
  in
    (el 1 args,el 2 args)
  end;
val is_COND_PROP___ADD_COND = (can dest_COND_PROP___ADD_COND);




val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_term = ``SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS``;
fun dest_SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_term) andalso
	        (length args = 2) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS" "Wrong term")
  in
    (el 1 args, el 2 args)
  end
val is_SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS = (can dest_SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS);

fun mk_SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs p =
list_mk_icomb (SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_term, [vs,p])



val SMALLFOOT_AP_PERMISSION_UNIMPORTANT_term = ``SMALLFOOT_AP_PERMISSION_UNIMPORTANT``;
fun dest_SMALLFOOT_AP_PERMISSION_UNIMPORTANT tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f SMALLFOOT_AP_PERMISSION_UNIMPORTANT_term) andalso
	        (length args = 1) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_SMALLFOOT_AP_PERMISSION_UNIMPORTANT" "Wrong term")
  in
    (el 1 args)
  end
val is_SMALLFOOT_AP_PERMISSION_UNIMPORTANT = (can dest_SMALLFOOT_AP_PERMISSION_UNIMPORTANT);





val smallfoot_ap_implies_ae_equal_term = ``smallfoot_ap_implies_ae_equal``;
fun dest_smallfoot_ap_implies_ae_equal tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f smallfoot_ap_implies_ae_equal_term) andalso
	        (length args = 3) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_smallfoot_ap_implies_ae_equal" "Wrong term")
  in
    (el 1 args, el 2 args, el 3 args)
  end
val is_smallfoot_ap_implies_ae_equal = (can dest_smallfoot_ap_implies_ae_equal);




fun smallfoot_dest_is_binop cL m =
  let 
     fun dest_fun tt =
     let
        val (f, args) = strip_comb tt;
        val _ = if (exists (same_const f) cL) andalso
	        (length args = 2) then () else
                raise (mk_HOL_ERR "smallfootLib" m "Wrong term")
     in
       (el 1 args, el 2 args)
     end
  in
     (dest_fun, can dest_fun)
  end;


val (dest_smallfoot_ap_equal, is_smallfoot_ap_equal) = 
    smallfoot_dest_is_binop [smallfoot_ap_equal_term] "dest_smallfoot_ap_equal";

val (dest_smallfoot_ap_unequal, is_smallfoot_ap_unequal) = 
    smallfoot_dest_is_binop [smallfoot_ap_unequal_term] "dest_smallfoot_ap_unequal";




val (dest_smallfoot_ap_compare, is_smallfoot_ap_compare) = 
    smallfoot_dest_is_binop [smallfoot_ap_equal_term,
			     smallfoot_ap_unequal_term,
			     smallfoot_ap_lesseq_term,
			     smallfoot_ap_less_term,
			     smallfoot_ap_greatereq_term,
			     smallfoot_ap_greater_term] 
			    "dest_smallfoot_ap_compare";


fun dest_smallfoot_ae_const tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f smallfoot_ae_const_term) andalso
	        (length args = 1) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_smallfoot_ae_const" "Wrong term")
  in
    (el 1 args)
  end
val is_smallfoot_ae_const = (can dest_smallfoot_ae_const);



fun is_smallfoot_ae_null tt = (same_const tt smallfoot_ae_null_term);

fun dest_smallfoot_ae_const_null tt =
  if is_smallfoot_ae_null tt then
     numSyntax.zero_tm
  else dest_smallfoot_ae_const tt;

val is_smallfoot_ae_const_null = (can dest_smallfoot_ae_const_null);

fun is_smallfoot_ae_null_or_const_zero tt =
  (numSyntax.int_of_term (dest_smallfoot_ae_const_null tt) = 0) handle HOL_ERR _ => false;




val smallfoot_ae_var_term = ``smallfoot_ae_var``;
fun dest_smallfoot_ae_var tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f smallfoot_ae_var_term) andalso
	        (length args = 1) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_smallfoot_ae_var" "Wrong term")
  in
    (el 1 args)
  end
val is_smallfoot_ae_var = (can dest_smallfoot_ae_var);




val smallfoot_ap_var_update_term = ``smallfoot_ap_var_update``;
fun dest_smallfoot_ap_var_update t =
  let
     val (f, args) = strip_comb t;
     val _ = if (same_const f smallfoot_ap_var_update_term) andalso
	        (length args = 3) then () else
             raise (mk_HOL_ERR "smallfoot_ap_var_update_term" "dest_FEVERY" "Wrong term")
  in
    (el 1 args, el 2 args, el 3 args)
  end
val is_smallfoot_ap_var_update = (can dest_smallfoot_ap_var_update);


val smallfoot_ae_var_update_term = ``smallfoot_ae_var_update``;
fun dest_smallfoot_ae_var_update t =
  let
     val (f, args) = strip_comb t;
     val _ = if (same_const f smallfoot_ae_var_update_term) andalso
	        (length args = 3) then () else
             raise (mk_HOL_ERR "smallfoot_ae_var_update_term" "dest_FEVERY" "Wrong term")
  in
    (el 1 args, el 2 args, el 3 args)
  end
val is_smallfoot_ae_var_update = (can dest_smallfoot_ae_var_update);




fun dest_smallfoot_ap_points_to t =
  let
     val (f, args) = strip_comb t;
     val _ = if (same_const f smallfoot_ap_points_to_term) andalso
	        (length args = 2) then () else
             raise (mk_HOL_ERR "smallfoot_ap_points_to_term" "dest_FEVERY" "Wrong term")
  in
    (el 1 args, el 2 args)
  end
val is_smallfoot_ap_points_to = (can dest_smallfoot_ap_points_to);



fun dest_smallfoot_ap_data_list t =
  let
     val (f, args) = strip_comb t;
     val _ = if (same_const f smallfoot_ap_data_list_term) andalso
	        (length args = 3) then () else
             raise (mk_HOL_ERR "smallfoot_ap_data_list" "smallfootSyntax" "Wrong term")
  in
    (el 1 args, el 2 args, el 3 args)
  end
val is_smallfoot_ap_data_list = (can dest_smallfoot_ap_data_list);


fun dest_smallfoot_ap_unknown t =
  let
     val (f, args) = strip_comb t;
     val _ = if (same_const f smallfoot_ap_unknown_term) andalso
	        (length args = 1) then () else
             raise (mk_HOL_ERR "smallfoot_ap_unknown_term" "smallfootSyntax" "Wrong term")
  in
    (stringLib.fromHOLstring (el 1 args))
  end
val is_smallfoot_ap_unknown = (can dest_smallfoot_ap_unknown);
fun mk_smallfoot_ap_unknown s = 
   mk_icomb (smallfoot_ap_unknown_term, stringLib.fromMLstring s);




fun dest_smallfoot_ap_data_list_seg t =
  let
     val (f, args) = strip_comb t;
     val _ = if (same_const f smallfoot_ap_data_list_seg_term) andalso
	        (length args = 4) then () else
             raise (mk_HOL_ERR "smallfoot_ap_data_list_seg" "dest_FEVERY" "Wrong term")
  in
    (el 1 args, el 2 args, el 3 args, el 4 args)
  end
val is_smallfoot_ap_data_list_seg = (can dest_smallfoot_ap_data_list_seg);


fun dest_smallfoot_ap_data_list_seg_or_list t =
dest_smallfoot_ap_data_list_seg t handle HOL_ERR _ =>
let val (t,e1,data) = dest_smallfoot_ap_data_list t in
(t,e1,data,smallfoot_ae_null_term) end

val is_smallfoot_ap_data_list_seg_or_list = (can dest_smallfoot_ap_data_list_seg_or_list);


fun dest_smallfoot_ap_bintree t =
  let
     val (f, args) = strip_comb t;
     val _ = if (same_const f smallfoot_ap_bintree_term) andalso
	        (length args = 2) then () else
             raise (mk_HOL_ERR "smallfoot_ap_bintree" "dest_FEVERY" "Wrong term")
     val (lt,rt) = save_dest_pair (el 1 args);
  in
    (lt,rt, el 2 args)
  end
val is_smallfoot_ap_bintree = (can dest_smallfoot_ap_bintree);



fun dest_smallfoot_ap_data_list_seg_or_list_or_bintree t =
  let val (_,e1,_,e2) = dest_smallfoot_ap_data_list_seg_or_list t in (e1,e2) end handle HOL_ERR _ =>
  let val (_,_,e1) = (dest_smallfoot_ap_bintree t) in (e1,smallfoot_ae_null_term) end;

val is_smallfoot_ap_data_list_seg_or_list_or_bintree = (can dest_smallfoot_ap_data_list_seg_or_list_or_bintree);


fun dest_smallfoot_ap_spatial t =
  (fst (dest_smallfoot_ap_points_to t)) handle HOL_ERR _ =>
  (#2 (dest_smallfoot_ap_data_list_seg_or_list t)) handle HOL_ERR _ =>
  (#3 (dest_smallfoot_ap_bintree t));

val is_smallfoot_ap_spatial = (can dest_smallfoot_ap_spatial);



fun dest_smallfoot_ap_spatial___no_data_list_seg t =
  (fst (dest_smallfoot_ap_points_to t)) handle HOL_ERR _ =>
  (#2 (dest_smallfoot_ap_data_list t)) handle HOL_ERR _ =>
  (#3 (dest_smallfoot_ap_bintree t));

val is_smallfoot_ap_spatial___no_data_list_seg = (can dest_smallfoot_ap_spatial___no_data_list_seg);






val smallfoot_ap_empty_heap_cond_term = ``smallfoot_ap_empty_heap_cond``
fun dest_smallfoot_ap_empty_heap_cond t =
  let
     val (f, args) = strip_comb t;
     val _ = if (same_const f smallfoot_ap_empty_heap_cond_term) andalso
	        (length args = 1) then () else
             raise (mk_HOL_ERR "smallfootSyntax" "smallfoot_ap_empty_heap_cond" "Wrong term")
  in
    (el 1 args)
  end
val is_smallfoot_ap_empty_heap_cond = can dest_smallfoot_ap_empty_heap_cond;

val smallfoot_ap_exp_is_defined_term = ``smallfoot_ap_exp_is_defined``
fun dest_smallfoot_ap_exp_is_defined t =
  let
     val (f, args) = strip_comb t;
     val _ = if (same_const f smallfoot_ap_exp_is_defined_term) andalso
	        (length args = 1) then () else
             raise (mk_HOL_ERR "smallfootSyntax" "smallfoot_ap_exp_is_defined" "Wrong term")
  in
    (el 1 args)
  end
val is_smallfoot_ap_exp_is_defined = can dest_smallfoot_ap_exp_is_defined;



fun dest_smallfoot_ap_cond t =
  let
     val (f, args) = strip_comb t;
     val _ = if (same_const f smallfoot_ap_cond_term) andalso
	        (length args = 4) then () else
             raise (mk_HOL_ERR "smallfootSyntax" "smallfoot_ap_cond" "Wrong term")
  in
    (el 1 args,el 2 args,el 3 args,el 4 args)
  end
val is_smallfoot_ap_cond = can dest_smallfoot_ap_cond;


fun dest_smallfoot_ap_unequal_cond t =
  let
     val (f, args) = strip_comb t;
     val _ = if (same_const f smallfoot_ap_unequal_cond_term) andalso
	        (length args = 3) then () else
             raise (mk_HOL_ERR "smallfootSyntax" "smallfoot_ap_unequal_cond" "Wrong term")
  in
    (el 1 args,el 2 args,el 3 args)
  end
val is_smallfoot_ap_unequal_cond = can dest_smallfoot_ap_unequal_cond;
fun mk_smallfoot_ap_unequal_cond (l,r,P) = list_mk_icomb (smallfoot_ap_unequal_cond_term, [l,r,P])


fun dest_smallfoot_ap_equal_cond t =
  let
     val (f, args) = strip_comb t;
     val _ = if (same_const f smallfoot_ap_equal_cond_term) andalso
	        (length args = 3) then () else
             raise (mk_HOL_ERR "smallfootSyntax" "smallfoot_ap_equal_cond" "Wrong term")
  in
    (el 1 args,el 2 args,el 3 args)
  end
val is_smallfoot_ap_equal_cond = can dest_smallfoot_ap_equal_cond;
fun mk_smallfoot_ap_equal_cond (l,r,P) = list_mk_icomb (smallfoot_ap_equal_cond_term, [l,r,P])


val SMALLFOOT_IS_STRONG_STACK_PROPOSITION_term = ``SMALLFOOT_IS_STRONG_STACK_PROPOSITION``;
fun dest_SMALLFOOT_IS_STRONG_STACK_PROPOSITION t =
  let
     val (f, args) = strip_comb t;
     val _ = if (same_const f SMALLFOOT_IS_STRONG_STACK_PROPOSITION_term) andalso
	        (length args = 1) then () else
             raise (mk_HOL_ERR "smallfootSyntax" "dest_SMALLFOOT_IS_STRONG_STACK_PROPOSITION" "Wrong term")
  in
    (el 1 args)
  end
val is_SMALLFOOT_IS_STRONG_STACK_PROPOSITION = can dest_SMALLFOOT_IS_STRONG_STACK_PROPOSITION;


val SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE_term =
 ``SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE``;







val smallfoot_slp_new_var___PROP_COND_term = ``smallfoot_slp_new_var___PROP_COND``;
fun dest_smallfoot_slp_new_var___PROP_COND tt =
  let
     val (f, args) = strip_comb tt;
     val _ = if (same_const f smallfoot_slp_new_var___PROP_COND_term) andalso
	        (length args = 4) then () else
             raise (mk_HOL_ERR "smallfootSyntax" "dest_smallfoot_slp_new_var___PROP_COND" "Wrong term")
  in
    (el 1 args,el 2 args,el 3 args,el 4 args)
  end
val is_smallfoot_slp_new_var___PROP_COND = can dest_smallfoot_slp_new_var___PROP_COND;







val smallfoot_xenv_term = ``smallfoot_xenv``;
val smallfoot_env_term = ``smallfoot_env``;


val FEVERY_term = ``FEVERY``;
fun dest_FEVERY t =
  let
     val (f, args) = strip_comb t;
     val _ = if (same_const f FEVERY_term) andalso
	        (length args = 2) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_FEVERY" "Wrong term")
  in
    (el 1 args, el 2 args)
  end
val is_FEVERY = (can dest_FEVERY);


fun dest_FUPDATE t =
  let
     val (f, args) = strip_comb t;
     val _ = if (same_const f FUPDATE_tm) andalso
	        (length args = 2) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_FUPDATE" "Wrong term")
  in
    (el 1 args, el 2 args)
  end
val is_FUPDATE = (can dest_FUPDATE);


val BAG_IMAGE_tm = ``BAG_IMAGE``;
fun dest_BAG_IMAGE t =
  let
     val (f, args) = strip_comb t;
     val _ = if (same_const f BAG_IMAGE_tm) andalso
	        (length args = 2) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_BAG_IMAGE" "Wrong term")
  in
    (el 1 args, el 2 args)
  end
val is_BAG_IMAGE = (can dest_BAG_IMAGE);
fun mk_BAG_IMAGE f b = list_mk_icomb (BAG_IMAGE_tm, [f,b]);



val BAG_EVERY_tm = ``BAG_EVERY``;
fun dest_BAG_EVERY t =
  let
     val (f, args) = strip_comb t;
     val _ = if (same_const f BAG_EVERY_tm) andalso
	        (length args = 2) then () else
             raise (mk_HOL_ERR "smallfootLib" "dest_BAG_EVERY" "Wrong term")
  in
    (el 1 args, el 2 args)
  end
val is_BAG_EVERY = (can dest_BAG_EVERY);



fun is_EMPTY_BAG t = same_const bagSyntax.EMPTY_BAG_tm t


end
