structure separationLogicSyntax :> separationLogicSyntax =
struct

(*
quietdec := true;
loadPath := (Globals.HOLDIR ^ "/examples/separationLogic/src") :: 
            (Globals.HOLDIR ^ "/examples/separationLogic/src/holfoot") :: 
            !loadPath;

map load ["finite_mapTheory", "separationLogicTheory"];
show_assums := true;
*)

open HolKernel Parse boolLib separationLogicTheory


(*
quietdec := false;
*)



fun safe_dest_pair t =
  pairLib.dest_pair t handle HOL_ERR _ =>
  (pairLib.mk_fst t, pairLib.mk_snd t);


(*****************************************************************
 Finite Maps
 ****************************************************************)

(*val t = ``FEMPTY |+ (v1,1) |+ (v2,2)``*)

val FEMPTY_tm = ``FEMPTY:'a |-> 'b``;
val FUPDATE_tm = ``$FUPDATE:('a |-> 'b) -> 'a # 'b -> ('a |-> 'b)``;

fun strip_finite_map t = 
    let
	val (op_term, args) = strip_comb t;
    in
       if (same_const op_term FUPDATE_tm) then
	   let
	       val (slist, rest) = (strip_finite_map (el 1 args));
	   in
               ((pairLib.dest_pair (el 2 args))::slist, rest)
	   end
       else if (same_const op_term FEMPTY_tm) then ([], NONE)
       else ([], SOME t) 
    end handle HOL_ERR _ => ([], SOME t);



(*****************************************************************
 Destructors Constructors
 ****************************************************************)

(*val l = [1,2,3,4,5,6,7,8,9]*)

fun list2tuple1 l = (el 1 l);
fun list2tuple2 l = (el 1 l, el 2 l);
fun list2tuple3 l = (el 1 l, el 2 l, el 3 l);
fun list2tuple4 l = (el 1 l, el 2 l, el 3 l, el 4 l);
fun list2tuple5 l = (el 1 l, el 2 l, el 3 l, el 4 l, el 5 l);
fun list2tuple6 l = (el 1 l, el 2 l, el 3 l, el 4 l, el 5 l, el 6 l);
fun list2tuple7 l = (el 1 l, el 2 l, el 3 l, el 4 l, el 5 l, el 6 l, el 7 l);
fun list2tuple8 l = (el 1 l, el 2 l, el 3 l, el 4 l, el 5 l, el 6 l, el 7 l, el 8 l);
fun list2tuple9 l = (el 1 l, el 2 l, el 3 l, el 4 l, el 5 l, el 6 l, el 7 l, el 8 l, el 9 l);


fun strip_comb_num n ff t = 
  let
     val (f, args) = strip_comb t;
     val _ = if (same_const f ff) andalso (length args = n) then () else Feedback.fail ()
  in 
     args
  end;

fun strip_comb_1 ff = list2tuple1 o (strip_comb_num 1 ff);
fun strip_comb_2 ff = list2tuple2 o (strip_comb_num 2 ff);
fun strip_comb_3 ff = list2tuple3 o (strip_comb_num 3 ff);
fun strip_comb_4 ff = list2tuple4 o (strip_comb_num 4 ff);
fun strip_comb_5 ff = list2tuple5 o (strip_comb_num 5 ff);
fun strip_comb_6 ff = list2tuple6 o (strip_comb_num 6 ff);
fun strip_comb_7 ff = list2tuple7 o (strip_comb_num 7 ff);
fun strip_comb_8 ff = list2tuple8 o (strip_comb_num 8 ff);
fun strip_comb_9 ff = list2tuple9 o (strip_comb_num 9 ff);







fun asl_mk_const n = 
   prim_mk_const {Name = n, Thy = "separationLogic"}

val asl_prog_parallel_term = asl_mk_const "asl_prog_parallel";
val dest_asl_prog_parallel = strip_comb_2 asl_prog_parallel_term;
val is_asl_prog_parallel = (can dest_asl_prog_parallel);


val asl_prog_seq_term = asl_mk_const "asl_prog_seq";
val dest_asl_prog_seq = strip_comb_2 asl_prog_seq_term;
val is_asl_prog_seq = (can dest_asl_prog_seq);


val asl_prog_block_term = asl_mk_const "asl_prog_block";
val dest_asl_prog_block = strip_comb_1 asl_prog_block_term;
val is_asl_prog_block = (can dest_asl_prog_block);
fun mk_asl_prog_block t = mk_icomb (asl_prog_block_term, t);

val asl_prog_cond_term = asl_mk_const "asl_prog_cond";
val dest_asl_prog_cond = strip_comb_3 asl_prog_cond_term;
val is_asl_prog_cond = (can dest_asl_prog_cond);
fun mk_asl_prog_cond (c,p1,p2) = 
   list_mk_icomb(asl_prog_cond_term, [c,p1,p2]);


val asl_prog_while_term = asl_mk_const "asl_prog_while";
val dest_asl_prog_while = strip_comb_2 asl_prog_while_term;
val is_asl_prog_while = (can dest_asl_prog_while);
fun mk_asl_prog_while (c,p) = 
   list_mk_icomb(asl_prog_while_term, [c,p]);

val asl_prog_assume_term = asl_mk_const "asl_prog_assume";
val dest_asl_prog_assume = strip_comb_1 asl_prog_assume_term;
val is_asl_prog_assume = (can dest_asl_prog_assume);


val asl_prog_cond_critical_section_term = asl_mk_const "asl_prog_cond_critical_section";
val dest_asl_prog_cond_critical_section = strip_comb_3 asl_prog_cond_critical_section_term;
val is_asl_prog_cond_critical_section = (can dest_asl_prog_cond_critical_section);


val asl_prog_best_local_action_term = asl_mk_const "asl_prog_best_local_action";
val dest_asl_prog_best_local_action = strip_comb_2 asl_prog_best_local_action_term;
val is_asl_prog_best_local_action = (can dest_asl_prog_best_local_action);


val ASL_PROGRAM_HOARE_TRIPLE_term = asl_mk_const "ASL_PROGRAM_HOARE_TRIPLE";
val dest_ASL_PROGRAM_HOARE_TRIPLE = strip_comb_5 ASL_PROGRAM_HOARE_TRIPLE_term;
val is_ASL_PROGRAM_HOARE_TRIPLE = (can dest_ASL_PROGRAM_HOARE_TRIPLE);



val ASL_PROGRAM_IS_ABSTRACTION_term = asl_mk_const "ASL_PROGRAM_IS_ABSTRACTION";
val dest_ASL_PROGRAM_IS_ABSTRACTION = strip_comb_4 ASL_PROGRAM_IS_ABSTRACTION_term;
val is_ASL_PROGRAM_IS_ABSTRACTION = (can dest_ASL_PROGRAM_IS_ABSTRACTION);
fun mk_ASL_PROGRAM_IS_ABSTRACTION (xenv,penv,x,y) = 
   list_mk_icomb(ASL_PROGRAM_IS_ABSTRACTION_term, [xenv,penv,x,y]);


val ASL_SPECIFICATION_term = asl_mk_const "ASL_SPECIFICATION"
val dest_ASL_SPECIFICATION = strip_comb_3 ASL_SPECIFICATION_term;
val is_ASL_SPECIFICATION = can dest_ASL_SPECIFICATION;


val COND_PROP___IMP_term = asl_mk_const "COND_PROP___IMP";
val dest_COND_PROP___IMP = strip_comb_2 COND_PROP___IMP_term;
val is_COND_PROP___IMP = (can dest_COND_PROP___IMP);

val COND_PROP___EQUIV_term = asl_mk_const "COND_PROP___EQUIV";
val dest_COND_PROP___EQUIV = strip_comb_2 COND_PROP___EQUIV_term;
val is_COND_PROP___EQUIV = (can dest_COND_PROP___EQUIV);


val COND_PROP___STRONG_EXISTS_term = asl_mk_const "COND_PROP___STRONG_EXISTS";
fun dest_COND_PROP___STRONG_EXISTS tt =
  let
     val arg = strip_comb_1 COND_PROP___STRONG_EXISTS_term tt;
     val (v, body) = pairSyntax.dest_pabs arg
  in
    (v, body)
  end;
val is_COND_PROP___STRONG_EXISTS = can dest_COND_PROP___STRONG_EXISTS;



val COND_PROP___EXISTS_term = asl_mk_const "COND_PROP___EXISTS";
fun dest_COND_PROP___EXISTS tt =
  let
     val arg = strip_comb_1 COND_PROP___EXISTS_term tt;
     val (v,b) = dest_abs arg
  in
    (v,b)
  end;
val is_COND_PROP___EXISTS = (can dest_COND_PROP___EXISTS);



val COND_PROP___ADD_COND_term = asl_mk_const "COND_PROP___ADD_COND";
val dest_COND_PROP___ADD_COND = strip_comb_2 COND_PROP___ADD_COND_term;
val is_COND_PROP___ADD_COND = (can dest_COND_PROP___ADD_COND);


val asl_cond_star_term = asl_mk_const "asl_cond_star";
val dest_asl_cond_star = strip_comb_3 asl_cond_star_term
val is_asl_cond_star = (can dest_asl_cond_star);


val asl_pred_false_term = asl_mk_const "asl_pred_false";
val asl_pred_true_term = asl_mk_const "asl_pred_true";
val asl_pred_neg_term = asl_mk_const "asl_pred_neg";
val asl_pred_and_term = asl_mk_const "asl_pred_and";
val asl_pred_or_term = asl_mk_const "asl_pred_or";
val asl_pred_prim_term = asl_mk_const "asl_pred_prim";

val asl_exists_term = asl_mk_const "asl_exists"
val asl_exists_list_term = asl_mk_const "asl_exists_list"
val fasl_star_term = asl_mk_const "fasl_star";
val asl_star_term = asl_mk_const "asl_star";
val asl_bigstar_list_term = asl_mk_const "asl_bigstar_list";
val asl_trivial_cond_term = asl_mk_const "asl_trivial_cond";
val asl_emp_term = asl_mk_const "asl_emp";
val asl_false_term = asl_mk_const "asl_false";
val is_asl_false = same_const asl_false_term


val dest_asl_trival_cond = strip_comb_2 asl_trivial_cond_term;
val is_asl_trivial_cond = (can dest_asl_trival_cond);

val dest_asl_star = strip_comb_3 asl_star_term;
val is_asl_star = (can dest_asl_star);
fun strip_asl_star t =
let
   val (_, p1, p2) = dest_asl_star t;
   val p1L = strip_asl_star p1;
   val p2L = strip_asl_star p2;
in
   (p1L @ p2L)
end handle HOL_ERR _ => [t];


fun dest_asl_exists tt =
  let
     val arg = strip_comb_1 asl_exists_term tt;
     val (v,b) = dest_abs arg
  in
    (v,b)
  end;
val is_asl_exists = (can dest_asl_exists);

fun dest_asl_exists_list tt =
  let
     val (arg1, arg2) = strip_comb_2 asl_exists_list_term tt;
  in
    (arg1,arg2)
  end;
val is_asl_exists_list = (can dest_asl_exists_list);



val asl_comment_loop_invariant_term = asl_mk_const "asl_comment_loop_invariant"
val dest_asl_comment_loop_invariant = strip_comb_2 asl_comment_loop_invariant_term;
val is_asl_comment_loop_invariant = (can dest_asl_comment_loop_invariant);

val asl_comment_block_spec_term = asl_mk_const "asl_comment_block_spec"
val dest_asl_comment_block_spec = strip_comb_2 asl_comment_block_spec_term;
val is_asl_comment_block_spec = (can dest_asl_comment_block_spec);

val asl_comment_loop_spec_term = asl_mk_const "asl_comment_loop_spec"
val dest_asl_comment_loop_spec = strip_comb_2 asl_comment_loop_spec_term;
val is_asl_comment_loop_spec = (can dest_asl_comment_loop_spec);

val asl_comment_loop_unroll_term = asl_mk_const "asl_comment_loop_unroll"
val dest_asl_comment_loop_unroll = strip_comb_2 asl_comment_loop_unroll_term;
val is_asl_comment_loop_unroll = (can dest_asl_comment_loop_unroll);

val asl_comment_location_string_term = asl_mk_const "asl_comment_location_string"
val dest_asl_comment_location_string = strip_comb_2 asl_comment_location_string_term;
val is_asl_comment_location_string = (can dest_asl_comment_location_string);

val asl_comment_location_term = asl_mk_const "asl_comment_location"
val dest_asl_comment_location = strip_comb_2 asl_comment_location_term;
val is_asl_comment_location = (can dest_asl_comment_location);
fun mk_asl_comment_location (c, tt) = list_mk_icomb (asl_comment_location_term, [c, tt])

val empty_label_list = listSyntax.mk_list ([], markerSyntax.label_ty)
fun save_dest_asl_comment_location tt =
let
   val (c, p) = dest_asl_comment_location tt;
in
   (c, p, fn () => ISPECL [c, p] asl_comment_location_def)
end handle HOL_ERR _ => (empty_label_list, tt, fn () => REFL tt)


fun dest_list_asl_comment_location tt =
dest_asl_comment_location tt handle HOL_ERR _ =>
dest_asl_comment_location (rand (rator tt))


fun save_dest_list_asl_comment_location tt =
   if (is_asl_comment_location tt) then
      save_dest_asl_comment_location tt 
   else
   let
      val (c, p, f) = save_dest_asl_comment_location (rand (rator tt))
   in
      (c, p, fn () => (RATOR_CONV (RAND_CONV (K (f ()))) tt))
   end;

val asl_comment_location2_term = asl_mk_const "asl_comment_location2"
val dest_asl_comment_location2 = strip_comb_2 asl_comment_location2_term;
val is_asl_comment_location2 = (can dest_asl_comment_location2);
fun mk_asl_comment_location2 (c, tt) = list_mk_icomb (asl_comment_location2_term, [c, tt])

fun save_dest_asl_comment_location2 tt =
let
   val (c, p) = dest_asl_comment_location2 tt;
in
   (c, p, fn () => ISPECL [c, p] asl_comment_location2_def)
end handle HOL_ERR _ => (empty_label_list, tt, fn () => REFL tt)


val asl_comment_abstraction_term = asl_mk_const "asl_comment_abstraction"
val dest_asl_comment_abstraction = strip_comb_2 asl_comment_abstraction_term;
val is_asl_comment_abstraction = (can dest_asl_comment_abstraction);

fun dest_asl_comment t =
  let
     val (op_term, args) = strip_comb t;
     val _ = if (length args = 2) then () else (Feedback.fail ());
     val (arg1, arg2) = (el 1 args, el 2 args);

     val def_thm = 
         if (same_const op_term asl_comment_location_term) then 
            asl_comment_location_def
         else if (same_const op_term asl_comment_location_string_term) then 
            asl_comment_location_string_def
         else if (same_const op_term asl_comment_location2_term) then 
            asl_comment_location2_def
         else if (same_const op_term asl_comment_loop_invariant_term) then 
            asl_comment_loop_invariant_def
         else if (same_const op_term asl_comment_abstraction_term) then 
            asl_comment_abstraction_def
         else if (same_const op_term asl_comment_loop_spec_term) then 
            asl_comment_loop_spec_def
         else if (same_const op_term asl_comment_loop_unroll_term) then 
            asl_comment_loop_unroll_def
         else if (same_const op_term asl_comment_block_spec_term) then 
            asl_comment_block_spec_def
         else Feedback.fail();
   in
     (op_term, arg1, arg2, def_thm)   
   end;

val asl_comment_assert_term = asl_mk_const "asl_comment_assert"
val dest_asl_comment_assert = strip_comb_1 asl_comment_assert_term;
val is_asl_comment_assert = (can dest_asl_comment_assert);


val asl_procedure_call_preserve_names_wrapper_term = asl_mk_const "asl_procedure_call_preserve_names_wrapper"
val dest_asl_procedure_call_preserve_names_wrapper = strip_comb_4 asl_procedure_call_preserve_names_wrapper_term
val is_asl_procedure_call_preserve_names_wrapper = can dest_asl_procedure_call_preserve_names_wrapper





end;
