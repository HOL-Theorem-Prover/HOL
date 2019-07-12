structure holfoot_pp_print :> holfoot_pp_print =
struct

(*
quietdec := true;
loadPath :=
            (concat [Globals.HOLDIR, "/examples/separationLogic/src"]) ::
            (concat [Globals.HOLDIR, "/examples/separationLogic/src/holfoot"]) ::
            !loadPath;
show_assums := true;
*)

open HolKernel boolLib bossLib PPBackEnd Parse
open separationLogicSyntax
open vars_as_resourceSyntax
open holfootSyntax
open Unicode

(*
quietdec := false;
*)
val holfoot_pretty_printer_block_indent = ref 3;

fun unicode_choice snu su =
  if (current_trace "Unicode" = 1) then su else snu

val _ = register_UserStyle NONE "holfoot_comment" [FG LightGrey]
val _ = register_UserStyle NONE "holfoot_spec"    [FG OrangeRed]
val _ = register_UserStyle NONE "holfoot_alert_0" [Bold, Underline]
val _ = register_UserStyle NONE "holfoot_alert_1" [Bold]
val _ = register_UserStyle NONE "holfoot_alert_2" [Underline]
val _ = register_UserStyle NONE "holfoot_frame_split___context" [FG LightGrey]
val _ = register_UserStyle NONE "holfoot_frame_split___imp"     [FG OrangeRed]
val _ = register_UserStyle NONE "holfoot_frame_split___split"   [FG Green]

fun holfoot_var_printer GS backend (sys : term_pp_types.sysprinter) (ppfns:term_pp_types.ppstream_funs) gravs d t = let
    open Portable term_pp_types
    val v_term = dest_holfoot_var t;
  in
    (#add_string ppfns) (stringLib.fromHOLstring v_term)
  end



fun holfoot_tag_printer GS backend (sys : term_pp_types.sysprinter) (ppfns:term_pp_types.ppstream_funs) gravs d t = let
    open Portable term_pp_types
    val t_term = dest_holfoot_tag t;
  in
    (#add_string ppfns) (stringLib.fromHOLstring t_term)
  end


fun pretty_print_list not_last oper list =
    smpp.pr_list oper not_last list;


fun pretty_print_list_sep sep (sys,strn,brk) d =
   let
      open Portable term_pp_types smpp;
      infix >>;
   in
      pretty_print_list (strn sep >> brk (1,0))
        (fn arg => sys (Top, Top, Top) (d - 1) arg)
   end;


fun holfoot_proccall_args_printer backend (sys_raw : term_pp_types.sysprinter) (ppfns:term_pp_types.ppstream_funs) gravs d args_term =
   let
      open Portable term_pp_types smpp;
      val {add_string,add_break,add_newline,...} = ppfns
      val (refArgs_term, valArgs_term) = pairLib.dest_pair args_term;
      val (refArgsL, _) = listSyntax.dest_list refArgs_term;
      val (valArgsL, _) = listSyntax.dest_list valArgs_term;
      fun sys gravs d' = sys_raw {gravs = gravs, depth = d', binderp = false}
      val pretty_print_arg_list = pretty_print_list_sep "," (sys, add_string, add_break) d;
   in
      if (null valArgsL) andalso (null refArgsL) then (add_string "()") else
      (add_string "(" >>
       pretty_print_arg_list refArgsL >>
       (if (null valArgsL) then nothing else (
           add_string ";" >> add_break (1,0) >>
           pretty_print_arg_list valArgsL
       )) >>
       add_string ")")
  end;

fun prefix_var_name prefix v =
let
   val (v_name, v_type) = dest_var v;
   val v' = mk_var (prefix^v_name, v_type);
in
   v'
end;


fun add_loc_add_string (i:int) add_string add_break loc_add_strings =
let
   open smpp;
   fun add_pps [] = nothing
     | add_pps [s1] = (add_string s1)
     | add_pps (s1::l) = (
         add_string s1 >>
         add_string " " >>
         add_string "-" >>
         add_break (1, i) >>
         add_pps l)
in
   add_pps loc_add_strings
end;

fun label_list2ML t = rev (map (fst o dest_var) (fst (listSyntax.dest_list t)));

fun holfoot_prog_printer GS backend (sys_raw : term_pp_types.sysprinter) (ppfns:term_pp_types.ppstream_funs) gravs d t = let
    open Portable term_pp_types smpp
    infix >>
    val {add_string,add_break,ublock,add_newline,ustyle,...} = ppfns
    val (op_term,args) = strip_comb t;
    fun sys gravs d' = sys_raw {gravs = gravs, depth = d', binderp = false}
  in
    if (same_const op_term holfoot_prog_field_lookup_term)  then (
       let
          val v_term = el 1 args;
          val exp_term = el 2 args;
          val tag_term = el 3 args;
       in
          ublock INCONSISTENT (!holfoot_pretty_printer_block_indent) (
             sys (Top, Top, Top) (d - 1) v_term >>
             add_string " =" >>
             add_break (1,1) >>
             sys (Top, Top, Top) (d - 1) exp_term >>
             add_string (unicode_choice "->" UChar.rightarrow) >>
             sys (Top, Top, Top) (d - 1) tag_term
          )
       end
    ) else if (same_const op_term holfoot_prog_field_assign_term)  then (
       let
          val exp_term = el 1 args;
          val tag_term = el 2 args;
          val exp2_term = el 3 args;
       in
          ublock INCONSISTENT (!holfoot_pretty_printer_block_indent) (
             sys (Top, Top, Top) (d - 1) exp_term >>
             add_string (unicode_choice "->" UChar.rightarrow) >>
             sys (Top, Top, Top) (d - 1) tag_term >>
             add_string " =" >>
             add_break (1,1) >>
             sys (Top, Top, Top) (d - 1) exp2_term
          )
       end
    ) else if (same_const op_term holfoot_prog_procedure_call_term)  then (
       let
          val name_term = el 1 args;
          val args_term = el 2 args;
       in
          ublock INCONSISTENT (!holfoot_pretty_printer_block_indent) (
             add_string (stringLib.fromHOLstring name_term) >>
             holfoot_proccall_args_printer backend sys_raw ppfns gravs (d - 1) args_term
          )
       end
    ) else if (same_const op_term holfoot_prog_parallel_procedure_call_term)  then (
       let
          val name1_term = el 1 args;
          val args1_term = el 2 args;
          val name2_term = el 3 args;
          val args2_term = el 4 args;
       in
          ublock INCONSISTENT (!holfoot_pretty_printer_block_indent) (
             add_string (stringLib.fromHOLstring name1_term) >>
             holfoot_proccall_args_printer backend sys_raw ppfns gravs (d - 1) args1_term >>
             add_string " ||" >>
             add_string " " >>
             add_string (stringLib.fromHOLstring name2_term) >>
             holfoot_proccall_args_printer backend sys_raw ppfns gravs (d - 1) args2_term
          )
       end
    ) else if (same_const op_term holfoot_prog_assign_term)  then (
       let
          val v_term = el 1 args;
          val exp_term = el 2 args;
       in
          ublock INCONSISTENT (!holfoot_pretty_printer_block_indent) (
             sys (Top, Top, Top) (d - 1) v_term >>
             add_string " =" >>
             add_break (1,1) >>
             sys (Top, Top, Top) (d - 1) exp_term
          )
       end
    ) else if (same_const op_term holfoot_prog_dispose_term)  then (
       let
          val n_term = el 1 args;
          val e_term = el 2 args;
          val simple = is_holfoot_exp_one n_term;
       in
          ublock INCONSISTENT (!holfoot_pretty_printer_block_indent) (
          if (simple) then (
             add_string "dispose" >>
             add_string " " >>
             sys (Top, Top, Top) (d - 1) e_term
          ) else (
             add_string "dispose-block" >>
             add_string "(" >>
             sys (Top, Top, Top) (d - 1) e_term >>
             add_string "," >>
             sys (Top, Top, Top) (d - 1) n_term >>
             add_string ")"
          ))
       end
    ) else if (same_const op_term holfoot_prog_new_term)  then (
       let
          val n_term = el 1 args;
          val v_term = el 2 args;
          val (l, _) = listSyntax.dest_list (el 3 args);
          val simple = is_holfoot_exp_one n_term;
       in
          ublock INCONSISTENT (!holfoot_pretty_printer_block_indent) (
             sys (Top, Top, Top) (d - 1) v_term >>
             add_string " =" >>
             add_break (1,!holfoot_pretty_printer_block_indent) >>
             (if simple then (
                add_string "new()"
             ) else (
                add_string "new-block" >>
                add_string "(" >>
                sys (Top, Top, Top) (d - 1) n_term >>
                add_string ")"
             )) >>
             (if (null l) then nothing else (
                add_string " " >>
                add_string "[" >>
                ustyle [UserStyle "holfoot_spec"] (
                   pretty_print_list_sep "," (sys, add_string, add_break) d l
                ) >>
                add_string "]"
             ))
          )
       end
    ) else if (same_const op_term asl_prog_assume_term)  then (
       let
          val prop_term = el 1 args;
       in
          ublock CONSISTENT 0 (
             add_string "assume" >>
             sys (Top, Top, Top) (d - 1) prop_term
          )
       end
    ) else if (same_const op_term asl_prog_diverge_term)  then (
          ublock CONSISTENT 0 (
             add_string "diverge"
          )
    ) else if (same_const op_term asl_prog_fail_term)  then (
          ublock CONSISTENT 0 (
             add_string "fail"
          )
    ) else if (same_const op_term asl_prog_cond_term)  then (
       let
          val prop_term = el 1 args;
          val prog1_term = el 2 args;
          val prog2_term = el 3 args;
       in
          ublock CONSISTENT 0 (
             add_string "if" >>
             add_string " " >>
             sys (Top, Top, Top) (d - 1) prop_term >>
             add_string " {" >>
             add_break (1,(!holfoot_pretty_printer_block_indent)) >>
             ublock INCONSISTENT 0 (
                sys (Top, Top, Top) (d - 1) prog1_term
             ) >>
             add_break (1,0) >>
             add_string "} else {" >>
             add_break (1,(!holfoot_pretty_printer_block_indent)) >>
             ublock INCONSISTENT 0 (
                sys (Top, Top, Top) (d - 1) prog2_term
             ) >>
             add_break (1,0) >>
             add_string "}"
          )
       end
    ) else if (same_const op_term asl_prog_choice_term)  then (
       let
          val prog1_term = el 1 args;
          val prog2_term = el 2 args;
       in
          ublock CONSISTENT 0 (
             add_string "if (*) {" >>
             add_break (1,(!holfoot_pretty_printer_block_indent)) >>
             ublock INCONSISTENT 0 (
                sys (Top, Top, Top) (d - 1) prog1_term
             ) >>
             add_break (1,0) >>
             add_string "} else {" >>
             add_break (1,(!holfoot_pretty_printer_block_indent)) >>
             ublock INCONSISTENT 0 (
                sys (Top, Top, Top) (d - 1) prog2_term
             ) >>
             add_break (1,0) >>
             add_string "}"
          )
       end
     ) else if (same_const op_term asl_prog_while_term)  then (
       let
          val prop_term = el 1 args;
          val prog_term = el 2 args;
       in
          ublock CONSISTENT 0 (
             add_string "while" >>
             add_string " " >>
             sys (Top, Top, Top) (d - 1) prop_term >>
             add_string " " >>
             add_string "{" >>
             add_break (1,(!holfoot_pretty_printer_block_indent)) >>
             ublock INCONSISTENT 0 (
                sys (Top, Top, Top) (d - 1) prog_term
             ) >>
             add_break (1,0) >>
             add_string "}"
          )
       end
    ) else if (same_const op_term asl_comment_block_spec_term) orelse
              (same_const op_term asl_comment_loop_spec_term) then (
       let
          val (pre_term, post_term) = pairSyntax.dest_pair (el 1 args);
          val prog_term = el 2 args;
          val loop = same_const op_term asl_comment_loop_spec_term;

          val (v,pre_body) = pairSyntax.dest_pabs pre_term;
          val (_,post_body) = pairSyntax.dest_pabs post_term;
          val vL = free_vars v;
          val vL' = map (prefix_var_name "!") vL;
          val su = map (op |->) (zip vL vL');
          val pre_body' = subst su pre_body;
          val post_body' = subst su post_body;
       in
          ublock CONSISTENT 0 (
             ustyle [UserStyle "holfoot_comment"] (
                add_string (if loop then "loop-specification" else "block-specification") >>
                add_string " " >>
                add_string "[" >>
                sys (Top, Top, Top) (d - 1) pre_body' >>
                add_string "]"
             ) >>
             add_string " " >>
             add_string "{" >>
             add_break (1,(!holfoot_pretty_printer_block_indent)) >>
             ublock INCONSISTENT 0 (
                sys (Top, Top, Top) (d - 1) prog_term
             ) >>
             add_break (1,0) >>
             add_string "}" >>
             add_string " " >>
             ustyle [UserStyle "holfoot_comment"] (
               add_string "[" >>
               sys (Top, Top, Top) (d - 1) post_body' >>
               add_string "]"
             )
          )
       end
    ) else if (same_const op_term asl_comment_loop_unroll_term)  then (
       let
          val unroll_term = el 1 args;
          val prog_term   = el 2 args;
       in
          ublock CONSISTENT 0 (
             ustyle [UserStyle "holfoot_comment"] (
                add_string ("loop-unroll") >>
                add_string " " >>
                sys (Top, Top, Top) (d - 1) unroll_term
             ) >>
             add_string " " >>
             add_string "{" >>
             add_break (1,(!holfoot_pretty_printer_block_indent)) >>
             ublock INCONSISTENT 0 (
                sys (Top, Top, Top) (d - 1) prog_term
             ) >>
             add_break (1,0) >>
             add_string "}"
          )
       end
    ) else if (same_const op_term asl_comment_assert_term)  then (
       let
          val p_term   = el 1 args;
          val (v,p_body) = pairSyntax.dest_pabs p_term;
          val vL = free_vars v;
          val vL' = map (prefix_var_name "!") vL;
          val su = map (op |->) (zip vL vL');
          val p_body' = subst su p_body;
       in
          ustyle [UserStyle "holfoot_comment"] (
             add_string ("assert") >>
             add_string " " >>
             add_string "[" >>
             ublock CONSISTENT 0 (
                sys (Top, Top, Top) (d - 1) p_body'
             ) >>
             add_string "]"
          )
       end
    ) else if (same_const op_term asl_prog_cond_critical_section_term)  then (
       let
          val res_term = el 1 args;
          val cond_term = el 2 args;
          val prog_term = el 3 args;
       in
          ublock CONSISTENT 0 (
             add_string "with" >>
             add_string " " >>
             add_string (stringLib.fromHOLstring res_term) >>
             add_string " " >>
             add_string "when" >>
             add_string " " >>
             sys (Top, Top, Top) (d - 1) cond_term >>
             add_string " {" >>
             add_break (1,(!holfoot_pretty_printer_block_indent)) >>
             ublock INCONSISTENT 0 (
                sys (Top, Top, Top) (d - 1) prog_term
             ) >>
             add_break (1,0) >>
             add_string "}"
          )
       end
    ) else if (same_const op_term var_res_prog_local_var_term) orelse
              (same_const op_term var_res_prog_call_by_value_arg_term) then (
       let
          val (l, t') = var_res_strip_local_vars t
          val _ = if null l then raise term_pp_types.UserPP_Failed else ()
       in
          ublock INCONSISTENT 0 (
             add_string "local" >>
             add_break (1,!holfoot_pretty_printer_block_indent) >>
             pretty_print_list
                (add_string "," >> add_break (1, !holfoot_pretty_printer_block_indent))
                (fn (v,vt) => (
                ublock CONSISTENT (!holfoot_pretty_printer_block_indent) (
                if (isSome vt) then (
                   add_string "(" >>
                   sys (Top, Top, Top) (d - 1) v >>
                   add_string " " >>
                   add_string "=" >>
                   add_string " " >>
                   sys (Top, Top, Top) (d - 1) (valOf vt) >>
                   add_string ")"
                ) else (
                   sys (Top, Top, Top) (d - 1) v
                )))) l>>
             add_string ";" >>
             add_break (1,0) >>
             sys (Top, Top, Top) (d - 1) t'
          )
      end
    ) else if (same_const op_term asl_prog_block_term)  then (
       let
          val (argL_term, rest_term) = listSyntax.strip_cons (el 1 args);
          val (argL_term, rest_term) = let
                    val (c, rest_term') = dest_asl_comment_location rest_term
                    val nc = mk_asl_comment_location (c, mk_comb (op_term, rest_term'))
                  in
                    (argL_term@[nc], rest_term')
                  end handle HOL_ERR _ => (argL_term, rest_term);
          val _ = if listSyntax.is_nil rest_term then () else Feedback.fail()
       in
          if null argL_term then nothing else
          if length argL_term = 1 then sys (Top, Top, Top) (d - 1) (hd argL_term) else
          (
             ublock CONSISTENT 0 (
             pretty_print_list (add_break (1,0))
                (fn stm =>
                (ublock CONSISTENT (!holfoot_pretty_printer_block_indent) (
                sys (Top, Top, Top) (d - 1) stm >>
                add_string ";"
                ))) argL_term
             )
          )
       end
    ) else if (same_const op_term asl_comment_location_term) then (
      let
         val loc_add_strings = label_list2ML (el 1 args);
      in
         ublock CONSISTENT 0 (
            ublock INCONSISTENT 0 (
               ustyle [UserStyle "holfoot_comment"] (
                  add_string "/*" >>
                  add_break (1,3) >>
                  add_loc_add_string 3 add_string add_break loc_add_strings >>
                  add_break (1,0) >>
                  add_string "*/"
               )
            ) >>
            add_break (1,0) >>
            sys (Top, Top, Top) (d - 1) (el 2 args)
         )
      end
    ) else if (same_const op_term asl_comment_location2_term) then (
      let
         val loc_add_strings = label_list2ML (el 1 args);
      in
         ublock CONSISTENT 0 (
            ublock INCONSISTENT 0 (
               ustyle [UserStyle "holfoot_comment"] (
               add_string "/**" >>
               add_break (1,3) >>
               add_loc_add_string 3 add_string add_break loc_add_strings >>
               add_break (1,0) >>
               add_string "**/"
               )
            ) >>
            add_break (1,0) >>
            sys (Top, Top, Top) (d - 1) (el 2 args)
         )
      end
    ) else if (same_const op_term asl_comment_loop_invariant_term) then (
      let
         val (v,body) = pairSyntax.dest_pabs (el 1 args);
         val vL = free_vars v;
         val vL' = map (prefix_var_name "!") vL;
         val su = map (op |->) (zip vL vL');
         val body' = subst su body;
      in
         ublock CONSISTENT 0 (
            ublock INCONSISTENT 0 (
               ustyle [UserStyle "holfoot_comment"] (
                 add_string "/*" >>
                 add_string " " >>
                 ustyle [UserStyle "holfoot_alert_2"] (
                   add_string "Loop Invariant:"
                 ) >>
                 add_break (1,3) >>
                 add_string "[" >>
                 sys (Top, Top, Top) (d - 1) body' >>
                 add_string "] */"
               )
            ) >>
            add_break (1,0) >>
            sys (Top, Top, Top) (d - 1) (el 2 args)
         )
      end
    ) else if (same_const op_term asl_comment_abstraction_term) then (
      ublock INCONSISTENT (!holfoot_pretty_printer_block_indent) (
         add_string "abstracted" >>
         add_string " " >>
         add_string (fst (dest_var (el 1 args)))
      )
    ) else if (same_const op_term asl_comment_location_string_term) then (
      let
         val loc_add_strings = [stringLib.fromHOLstring (el 1 args)];
      in
         ublock CONSISTENT 0 (
            ublock INCONSISTENT 0 (
               ustyle [UserStyle "holfoot_comment"] (
               add_string "/***" >>
               add_break (1,3) >>
               add_loc_add_string 3 add_string add_break loc_add_strings >>
               add_break (1,0) >>
               add_string "***/"
               )
            ) >>
            add_break (1,0) >>
            sys (Top, Top, Top) (d - 1) (el 2 args)
         )
      end
    ) else(
      raise term_pp_types.UserPP_Failed
    )
  end




fun coded_expression_to_term e1 e2 p =
   let
      val arg1 = Parse.term_to_string e1;
      val arg2 = Parse.term_to_string e2;
      val v1 = mk_var (arg1, numSyntax.num);
      val v2 = mk_var (arg2, numSyntax.num);
      val tt0 = list_mk_comb(p, [v1,v2])
      val tt1 = rhs (concl (LIST_BETA_CONV tt0)) handle HOL_ERR _ => tt0;
   in
      tt1
   end;

fun gencoded_expression_to_term p eL_t =
   let
      val (eL,_) = listSyntax.dest_list eL_t;
      val esL = map Parse.term_to_string eL;
      val evL = map (fn n => mk_var (n, numSyntax.num)) esL;
      val evL_t = listSyntax.mk_list (evL, numSyntax.num);
      val tt0 = mk_comb(p, evL_t)
      val tt1 = rhs (concl ((BETA_CONV THENC SIMP_CONV list_ss []) tt0)) handle HOL_ERR _ => tt0;
   in
      tt1
   end;

fun holfoot_expression_printer GS backend (sys_raw : term_pp_types.sysprinter) (ppfns:term_pp_types.ppstream_funs) gravs d t =
  let
    open Portable term_pp_types smpp
    infix >>
    val {add_string,add_break,ublock,add_newline,ustyle,...} = ppfns
    fun sys gravs d' = sys_raw {gravs = gravs, depth = d', binderp = false}
    val (op_term,args) = strip_comb t;
  in
    if (same_const op_term var_res_exp_var_term)  then (
      sys (Top, Top, Top) (d - 1) (hd args)
    ) else if (same_const op_term var_res_exp_const_term)  then (
      (if (is_var (hd args)) then add_string "#" else nothing) >>
      sys (Top, Top, Top) (d - 1) (hd args)
    ) else if (same_const op_term var_res_exp_binop_term)  then (
      add_string "(" >>
      sys (Top, Top, Top) (d - 1) (coded_expression_to_term (el 2 args) (el 3 args) (el 1 args)) >>
      add_string ")"
    ) else if (same_const op_term var_res_exp_op_term)  then (
      add_string "(" >>
      sys (Top, Top, Top) (d - 1) (gencoded_expression_to_term
         (el 1 args) (el 2 args)) >>
      add_string ")"
    ) else (
      raise term_pp_types.UserPP_Failed
    )
  end

fun holfoot_pred_printer GS backend sys_raw (ppfns:term_pp_types.ppstream_funs) gravs d t =
  let
    open Portable term_pp_types smpp
    infix >>
    val {add_string,add_break,ublock,add_newline,ustyle,...} = ppfns
    fun sys gravs d' = sys_raw {gravs = gravs, depth = d', binderp = false}
    val (op_term,args) = strip_comb t;
  in
    if (same_const op_term asl_pred_false_term)  then (
      add_string "false"
    ) else if (same_const op_term asl_pred_true_term)  then (
      add_string "true"
    ) else if (same_const op_term asl_pred_neg_term)  then (
      add_string "(not" >>
      add_string " " >>
      sys (Top, Top, Top) (d - 1) (el 1 args) >>
      add_string ")"
    ) else if (same_const op_term asl_pred_and_term)  then (
      add_string "(" >>
      sys (Top, Top, Top) (d - 1) (el 1 args) >>
      add_string " " >>
      add_string "and" >>
      add_string " " >>
      sys (Top, Top, Top) (d - 1) (el 2 args) >>
      add_string (")")
    ) else if (same_const op_term asl_pred_or_term)  then (
      add_string ("(") >>
      sys (Top, Top, Top) (d - 1) (el 1 args) >>
      add_string (" or") >>
      add_string " " >>
      sys (Top, Top, Top) (d - 1) (el 2 args) >>
      add_string (")")
    ) else if (same_const op_term var_res_pred_bin_term)  then (
      add_string ("(") >>
      sys (Top, Top, Top) (d - 1) (coded_expression_to_term (el 2 args) (el 3 args) (el 1 args)) >>
      add_string (")")
    ) else if (same_const op_term var_res_pred_term)  then (
      add_string "(" >>
      sys (Top, Top, Top) (d - 1) (gencoded_expression_to_term
         (el 1 args) (el 2 args)) >>
      add_string ")"
    ) else (
      raise term_pp_types.UserPP_Failed
    )
  end



fun finite_map_printer (sys, strn, brk) gravs d t =
      let
          open Portable term_pp_types smpp
          infix >>
          val (plist,rest) = strip_finite_map t;
      in
          (if ((length plist) = 1) then nothing else strn "[") >>
          (pretty_print_list (strn ", ")
                (fn (tag,exp) =>
                (sys (Top, Top, Top) (d - 1) tag >>
                strn ":" >>
                sys (Top, Top, Top) (d - 1) exp
                )) plist) >>
          (if (isSome rest) then (
              (if (length plist = 0) then nothing else strn (", ")) >>
              strn ("..."))
          else nothing) >>
          (if (length plist = 1) then nothing else strn "]")
      end

fun tag_list_printer (sys, strn, brk) gravs d t =
      let
          open Portable term_pp_types smpp
          infix >>
          val (plist,_) = listSyntax.dest_list t;
          val plist = map pairSyntax.dest_pair plist;
      in
          (if ((length plist) = 1) then nothing else strn "[") >>
          (pretty_print_list (strn ", ")
                (fn (tag,exp) =>
                (sys (Top, Top, Top) (d - 1) tag >>
                strn ":" >>
                sys (Top, Top, Top) (d - 1) exp
                )) plist) >>
          (if (length plist = 1) then nothing else strn "]")
      end


fun COND_PROP___STRONG_EXISTS_term_rewrite tt =
let
   val (v, body) = dest_COND_PROP___STRONG_EXISTS tt;
   val vL = pairSyntax.strip_pair v;
   val vL' = map (prefix_var_name "_") vL;
   val body' = subst (map op|-> (zip vL vL')) body;
in
   COND_PROP___STRONG_EXISTS_term_rewrite body'
end handle HOL_ERR _ => tt;


fun holfoot_a_prop_printer Gs backend (sys_raw:term_pp_types.sysprinter) (ppfns:term_pp_types.ppstream_funs) gravs d t = let
    open Portable term_pp_types smpp
    infix >>
    val {add_string,add_break,ublock,add_newline,ustyle,...} = ppfns
    val (op_term,args) = strip_comb t;
    fun sys gravs d' = sys_raw {gravs = gravs, depth = d', binderp = false}
  in
    if (same_const op_term asl_star_term) orelse
       (same_const op_term fasl_star_term) then (
      sys (Top, Top, Top) (d - 1) (el 2 args) >>
      add_string " " >>
      add_string (unicode_choice "-*-" UChar.blackstar) >>
      add_break (1,0) >>
      sys (Top, Top, Top) (d - 1) (el 3 args)
    ) else if (same_const op_term asl_bigstar_list_term) then (
      add_string (unicode_choice "-**-" UChar.circlestar) >>
      add_break (1,0) >>
      sys (Top, Top, Top) (d - 1) (el 2 args)
    ) else if (same_const op_term var_res_prop_equal_term)  then (
      ublock INCONSISTENT 0 (
         add_string "(" >>
         sys (Top, Top, Top) (d - 1) (el 2 args) >>
         add_string (" "^(unicode_choice "==" "=")) >>
         add_break (1,!holfoot_pretty_printer_block_indent) >>
         sys (Top, Top, Top) (d - 1) (el 3 args) >>
         add_string ")"
      )
    ) else if (same_const op_term var_res_prop_unequal_term)  then (
      ublock INCONSISTENT 0 (
         add_string "(" >>
         sys (Top, Top, Top) (d - 1) (el 2 args) >>
         add_string (" "^(unicode_choice "!=" UChar.neq)) >>
         add_break (1,!holfoot_pretty_printer_block_indent) >>
         sys (Top, Top, Top) (d - 1) (el 3 args) >>
         add_string ")"
      )
    ) else if (same_const op_term var_res_prop_binexpression_term)  then (
      ublock INCONSISTENT 0 (
         add_string "(" >>
         sys (Top, Top, Top) (d - 1) (coded_expression_to_term (el 4 args) (el 5 args) (el 3 args)) >>
         add_string ")"
      )
    ) else if (same_const op_term asl_emp_term)  then (
      add_string "emp"
    ) else if (same_const op_term holfoot_ap_data_list_term)  then (
      ublock INCONSISTENT 0 (
         add_string (if (same_const (el 3 args) listSyntax.nil_tm) then
                 "list" else "data_list") >>
         add_string "(" >>
         add_break (0,!holfoot_pretty_printer_block_indent) >>
         sys (Top, Top, Top) (d - 1) (el 1 args) >>
         add_string ";" >>
         add_break (1,!holfoot_pretty_printer_block_indent) >>
         sys (Top, Top, Top) (d - 1) (el 2 args) >>
         (if not (same_const (el 3 args) listSyntax.nil_tm) then
           (add_string "," >> add_break (1,!holfoot_pretty_printer_block_indent) >>
            tag_list_printer (sys, add_string, add_break) (Top,Top,Top) (d-1) (el 3 args)
           ) else nothing) >>
         add_string ")"
      )
    ) else if (same_const op_term holfoot_ap_data_list_seg_term)  then (
      let
         val end_is_null = is_holfoot_exp_null (el 4 args);
         val has_data = not (same_const (el 3 args) listSyntax.nil_tm);
         val desc = if has_data then
                 (if end_is_null then "data_list" else "data_lseg") else
                 (if end_is_null then "list" else "lseg")
      in
         ublock INCONSISTENT 0 (
            add_string desc >>
            add_string "(" >>
            add_break (0,!holfoot_pretty_printer_block_indent) >>
            sys (Top, Top, Top) (d - 1) (el 1 args) >>
            add_string ";" >>
            add_break (1,!holfoot_pretty_printer_block_indent) >>
            sys (Top, Top, Top) (d - 1) (el 2 args) >>
            (if has_data then
              (add_string "," >> add_break (1,!holfoot_pretty_printer_block_indent) >>
               tag_list_printer (sys, add_string, add_break) (Top,Top,Top) (d-1) (el 3 args)
              ) else nothing) >>
            (if (end_is_null) then nothing else (
               add_string "," >>
               add_break (1,!holfoot_pretty_printer_block_indent) >>
               sys (Top, Top, Top) (d - 1) (el 4 args)
            )) >>
            add_string ")"
         )
      end
    ) else if (same_const op_term holfoot_ap_data_queue_term)  then (
      let
         val has_data = not (same_const (el 3 args) listSyntax.nil_tm);
         val desc = if has_data then "data_queue" else "queue";
      in
         ublock INCONSISTENT 0 (
            add_string desc >>
            add_string "(" >>
            add_break (0,!holfoot_pretty_printer_block_indent) >>
            sys (Top, Top, Top) (d - 1) (el 1 args) >>
            add_string ";" >>
            add_break (1,!holfoot_pretty_printer_block_indent) >>
            sys (Top, Top, Top) (d - 1) (el 2 args) >>
            (if has_data then
              (add_string "," >> add_break (1,!holfoot_pretty_printer_block_indent) >>
               tag_list_printer (sys, add_string, add_break) (Top,Top,Top) (d-1) (el 3 args)
              ) else nothing) >>
            add_string "," >>
            add_break (1,!holfoot_pretty_printer_block_indent) >>
            sys (Top, Top, Top) (d - 1) (el 4 args) >>
            add_string ")"
         )
      end
    ) else if ((same_const op_term holfoot_ap_data_array_term) orelse
               (same_const op_term holfoot_ap_data_interval_term)) then (
      let
         val has_data = not (same_const (el 3 args) listSyntax.nil_tm);
         val is_interval = same_const op_term holfoot_ap_data_interval_term;
         val desc = if is_interval then
                       (if has_data then "data_interval" else "interval")
                    else
                       (if has_data then "data_array" else "array");
      in
         ublock INCONSISTENT 0 (
            add_string desc >>
            add_string "(" >>
            add_break (0,!holfoot_pretty_printer_block_indent) >>
            sys (Top, Top, Top) (d - 1) (el 1 args) >>
            add_string "," >>
            add_break (1,!holfoot_pretty_printer_block_indent) >>
            sys (Top, Top, Top) (d - 1) (el 2 args) >>
            (if has_data then
              (add_string "," >> add_break (1,!holfoot_pretty_printer_block_indent) >>
               tag_list_printer (sys, add_string, add_break) (Top,Top,Top) (d-1) (el 3 args)
              ) else nothing) >>
            add_string ")"
         )
      end
    ) else if (same_const op_term holfoot_ap_bintree_term)  then (
      ublock INCONSISTENT 0 (
         add_string "bin_tree" >>
         add_string "(" >>
         sys (Top, Top, Top) (d - 1) (fst (pairSyntax.dest_pair (el 1 args))) >>
         add_string "," >>
         add_string " " >>
         sys (Top, Top, Top) (d - 1) (snd (pairSyntax.dest_pair (el 1 args))) >>
         add_string ";" >>
         add_break(1, !holfoot_pretty_printer_block_indent) >>
         sys (Top, Top, Top) (d - 1) (el 2 args) >>
         add_string ")"
      )
    ) else if (same_const op_term holfoot_ap_tree_term)  then (
      ublock INCONSISTENT 0 (
         add_string "tree" >>
         add_string "(" >>
         sys (Top, Top, Top) (d - 1) (el 1 args) >>
         add_string ";" >>
         add_break(1, !holfoot_pretty_printer_block_indent) >>
         sys (Top, Top, Top) (d - 1) (el 2 args) >>
         add_string ")"
      )
    ) else if (same_const op_term holfoot_ap_data_tree_term)  then (
      let
         val (dtag_t, data_t) = pairSyntax.dest_pair (el 3 args);
      in
         ublock INCONSISTENT 0 (
            add_string "data_tree" >>
            add_string "(" >>
            sys (Top, Top, Top) (d - 1) (el 1 args) >>
            add_string ";" >>
            add_break(1, !holfoot_pretty_printer_block_indent) >>
            sys (Top, Top, Top) (d - 1) (el 2 args) >>
            add_string "," >>
            add_break(1, !holfoot_pretty_printer_block_indent) >>
            sys (Top, Top, Top) (d - 1) dtag_t >>
            add_string ":" >>
            sys (Top, Top, Top) (d - 1) data_t >>
            add_string ")"
         )
      end
    ) else if (same_const op_term holfoot_ap_points_to_term) then (
      ublock INCONSISTENT 0 (
         sys (Top, Top, Top) (d - 1) (el 1 args) >>
         add_string " " >>
         add_string (unicode_choice "|->" UChar.longmapsto) >>
         add_break(1, !holfoot_pretty_printer_block_indent) >>
         finite_map_printer (sys,add_string,add_break) (Top,Top,Top) (d-1) (el 2 args)
      )
    ) else if (same_const op_term var_res_map_term) then (
      let
         val (vc, b) = pairSyntax.dest_pabs (el 2 args);
         val vl = pairSyntax.strip_pair vc;
      in
         ublock INCONSISTENT 0 (
            add_string "map" >>
            add_string " " >>
            add_string "(\\" >>
            pretty_print_list_sep "" (sys, add_string, add_break) d vl >>
            add_string "." >>
            add_break (1,!holfoot_pretty_printer_block_indent) >>
            sys (Top, Top, Top) (d - 1) b >>
            add_string ")" >>
            add_break (1,!holfoot_pretty_printer_block_indent) >>
            add_string "(" >>
            sys (Top, Top, Top) (d - 1) (el 3 args) >>
            add_string ")"
         )
      end
    ) else if (same_const op_term var_res_prop_binexpression_cond_term)  then (
      ublock CONSISTENT 0 (
         add_string "if" >>
         add_string " " >>
         add_string "(" >>
         ublock INCONSISTENT (!holfoot_pretty_printer_block_indent) (
            sys (Top, Top, Top) (d - 1) (coded_expression_to_term (el 3 args) (el 4 args) (el 2 args)) >>
            add_string ")"
         ) >>
         add_string(" ") >>
         add_string("then (") >>
         add_break (1,(!holfoot_pretty_printer_block_indent)) >>
         ublock INCONSISTENT 0 (
           sys (Top, Top, Top) (d - 1) (el 5 args)
         ) >>
         add_break (1, 0) >>
         add_string ") else (" >>
         add_break (1,(!holfoot_pretty_printer_block_indent)) >>
         ublock INCONSISTENT 0 (
            sys (Top, Top, Top) (d - 1) (el 6 args)
         ) >>
         add_break (1, 0) >>
         add_string ") end"
      )
    ) else if (same_const op_term var_res_bool_proposition_term)  then (
      ublock INCONSISTENT (!holfoot_pretty_printer_block_indent) (
         add_string "pure" >>
         add_string "(" >>
         sys (Top, Top, Top) (d - 1) (el 2 args) >>
         add_string ")"
      )
    ) else if (same_const op_term var_res_prop_expression_term)  then (
      ublock INCONSISTENT (!holfoot_pretty_printer_block_indent) (
         add_string "pure" >>
         add_string "(" >>
         sys (Top, Top, Top) (d - 1) (gencoded_expression_to_term
            (el 3 args) (el 4 args)) >>
         add_string ")"
      )
    ) else if (same_const op_term var_res_prop_stack_true_term)  then (
      add_string "pure(T)"
    ) else if (same_const op_term asl_false_term)  then (
      add_string "false"
    ) else if (same_const op_term var_res_prop_input_ap_distinct_term)  then (
      let
         val (w,r) = pairSyntax.dest_pair (el 2 args);
         val wL = pred_setSyntax.strip_set w;
         val rL = pred_setSyntax.strip_set r;
      in
         ublock INCONSISTENT (!holfoot_pretty_printer_block_indent) (
            add_string "w/r:" >>
            add_break (1,0) >>
            pretty_print_list_sep "," (sys, add_string, add_break) d wL >>
            add_string ";" >>
            add_break (1,0) >>
            pretty_print_list_sep "," (sys, add_string, add_break) d rL >>
            add_string " " >>
            add_string "|" >>
            add_break (1,0) >>
            sys (Top, Top, Top) (d - 1) (el 4 args)
         )
      end
    ) else if (same_const op_term var_res_prop_input_ap_term)  then (
      let
         val (w,r) = pairSyntax.dest_pair (el 2 args);
         val wL = pred_setSyntax.strip_set w;
         val rL = pred_setSyntax.strip_set r;
      in
         ublock INCONSISTENT (!holfoot_pretty_printer_block_indent) (
            add_string "w/r:" >>
            add_break (1,0) >>
            pretty_print_list_sep "," (sys, add_string, add_break) d wL >>
            add_string ";" >>
            add_break (1,0) >>
            pretty_print_list_sep "," (sys, add_string, add_break) d rL >>
            add_string " " >>
            add_string "|" >>
            add_break (1,0) >>
            sys (Top, Top, Top) (d - 1) (el 3 args) >>
            add_string ""
         )
      end
    ) else if (same_const op_term COND_PROP___STRONG_EXISTS_term) then (
      let
         val body' = COND_PROP___STRONG_EXISTS_term_rewrite t
      in
         sys (Top, Top, Top) (d - 1) body'
      end
    ) else if (same_const op_term asl_exists_term) then (
      let
         val (v,body) = dest_abs (el 1 args);
         val v' = prefix_var_name "_" v;
         val body' = subst [v |-> v'] body;
      in
         sys (Top, Top, Top) (d - 1) body'
      end
    ) else (
      raise term_pp_types.UserPP_Failed
    )
  end




fun holfoot_specification_printer GS backend (sys_raw:term_pp_types.sysprinter) (ppfns:term_pp_types.ppstream_funs) gravs d t = let
    open Portable term_pp_types smpp
    infix >>
    val {add_string,add_break,ublock,add_newline,ustyle,...} = ppfns
    fun sys gravs d' = sys_raw {gravs = gravs, depth = d', binderp = false}
    val (_, resL,funL) = dest_ASL_SPECIFICATION t;
    val resL = rand resL;

    fun rest_preprocess rest =
      let
         val argL = pairLib.strip_pair rest;
      in
         (el 1 argL, el 2 argL, el 3 argL)
      end;

    val restL = map rest_preprocess (fst (listSyntax.dest_list resL));

    fun funt_preprocess funt =
      let
         val argL = pairLib.strip_pair funt;
         val (assume_opt_term, fun_name,abs_body,abs_spec) =
             (el 1 argL, el 2 argL, el 3 argL, el 4 argL);


         val (pv, spec) = pairSyntax.dest_pabs abs_spec;
         val x_pre_wrapper = rand (rator spec);
         val pre_wrapper = (snd (pairSyntax.dest_pabs x_pre_wrapper)) handle HOL_ERR _ => x_pre_wrapper

         val x_post = rand spec;
         val post = (snd (pairSyntax.dest_pabs x_post)) handle HOL_ERR _ => x_post
         val abs_post = pairSyntax.mk_pabs (pv, post)

         val wrapper_argL = snd (strip_comb pre_wrapper);
         val (argL1_term,_) = listSyntax.dest_list (el 1 wrapper_argL);
         val (argL2_term,_) = listSyntax.dest_list (el 2 wrapper_argL);
         val argL1_string = map (fst o dest_var) argL1_term;
         val argL2_string = map (fst o dest_var) argL2_term;

         val argL1_const = map (fn n => mk_comb (holfoot_var_term, stringLib.fromMLstring n)) argL1_string;
         val argL2_const = map (fn n => mk_var (n, numSyntax.num)) argL2_string

         val argL_term =  pairLib.mk_pair
                               (listSyntax.mk_list (argL1_const, ``:holfoot_var``),
                                listSyntax.mk_list (argL2_const, numSyntax.num));

         val body_term = mk_comb (abs_body, argL_term);

         val pre_term = mk_comb (el 3 wrapper_argL, argL_term);
         val post_term = mk_comb (abs_post, argL_term);


         fun term_simp t = (rhs o concl) (SIMP_CONV list_ss [bagTheory.BAG_UNION_INSERT, bagTheory.BAG_UNION_EMPTY] t)
         val body_term' = term_simp body_term;
         val pre_term' = term_simp pre_term;
         val post_term' = term_simp post_term;

         val assume_opt = if same_const assume_opt_term T then true else false;
      in
         (assume_opt, fun_name, argL_term, pre_term', body_term', post_term')
      end

    val funtL_term = (fst (listSyntax.dest_list funL));
    val funtL = map funt_preprocess funtL_term;

    fun umap f [] = nothing
      | umap f (x::xs) = (f x) >> (umap f xs);
  in
     ublock CONSISTENT 0 (
     ustyle [UserStyle "holfoot_alert_0"] (
        add_string ("HOLFOOT_SPECIFICATION")
     ) >>
     add_string " " >>
     add_string "(" >>
     add_newline >>
     ublock CONSISTENT (!holfoot_pretty_printer_block_indent) (
     add_newline >>
     (umap (fn (s,vars,prop) => (
                ublock INCONSISTENT 0 (
                add_string "resource" >>
                add_string " " >>
                ustyle [UserStyle "holfoot_alert_1"] (
                   add_string (stringLib.fromHOLstring s)
                ) >>
                add_break (1, (!holfoot_pretty_printer_block_indent)) >>
                sys (Top, Top, Top) (d - 1) vars >>
                add_break (1, (!holfoot_pretty_printer_block_indent)) >>
                add_string "{" >>
                sys (Top, Top, Top) (d - 1) prop >>
                add_string "}" >>
                add_newline >>
                add_newline
                ))) restL) >>
     (umap (fn (assume_opt, fun_name, argL_term, pre_term, body_term, post_term) => (
                ublock INCONSISTENT 0 (
                (if (not assume_opt) then (add_string "assume") else nothing) >>
                ustyle [UserStyle "holfoot_alert_1"] (
                   add_string (stringLib.fromHOLstring fun_name)
                ) >>
                holfoot_proccall_args_printer backend sys_raw (ppfns:term_pp_types.ppstream_funs) gravs (d - 1) argL_term >>
                (if (not assume_opt) then (add_newline >> add_string "  ")
                    else (add_break (1,2))) >>
                add_string "[" >>

                ustyle [UserStyle "holfoot_spec"] (
                ublock INCONSISTENT (!holfoot_pretty_printer_block_indent) (
                   sys (Top, Top, Top) (d - 1) pre_term
                )) >>

                add_string "]" >>
                (if assume_opt then (
                   add_string " " >>
                   add_string "{" >>
                   add_newline >>
                   add_string "   " >>

                   ublock INCONSISTENT 0 (
                      sys (Top, Top, Top) (d - 1) body_term
                   ) >>

                   add_newline >>
                   add_string "}")
                 else nothing) >>
                (if (not assume_opt) then (add_newline >> add_string "  ")
                    else (add_string " ")) >>
                add_string "[" >>
                ublock INCONSISTENT (!holfoot_pretty_printer_block_indent) (
                   ustyle [UserStyle "holfoot_spec"] (
                      sys (Top, Top, Top) (d - 1) post_term
                   ) >>
                   add_string "]"
                ) >>
                add_newline >>
                add_newline
                ))) funtL )
     ) >>
     add_newline >>
     add_string ")"
     )
  end;



(*
val t = find_term is_VAR_RES_FRAME_SPLIT (snd (top_goal ()))
*)
fun holfoot_prop_is_equiv_false_printer GS backend (sys_raw : term_pp_types.sysprinter) (ppfns:term_pp_types.ppstream_funs) gravs d t = let
    open Portable term_pp_types smpp
    infix >>
    val {add_string,add_break,ublock,add_newline,ustyle,...} = ppfns
in
    if (is_VAR_RES_PROP_IS_EQUIV_FALSE t) orelse
       ((is_neg t) andalso (is_VAR_RES_PROP_IS_EQUIV_FALSE (dest_neg t))) then
       add_string "..."
    else
       raise term_pp_types.UserPP_Failed
end


(*
val t = find_term is_VAR_RES_FRAME_SPLIT (snd (top_goal ()))
*)
fun holfoot_frame_split_printer GS backend (sys_raw : term_pp_types.sysprinter) (ppfns:term_pp_types.ppstream_funs) gravs d t = let
    open Portable term_pp_types smpp
    infix >>
    val {add_string,add_break,ublock,add_newline,ustyle,...} = ppfns
    fun sys gravs d' = sys_raw {gravs = gravs, depth = d', binderp = false}
    val (f, rfc, wr, w', context, split, imp, restP) = dest_VAR_RES_FRAME_SPLIT t;
    val (mode, comment_opt) = pairSyntax.dest_pair rfc;
    val _ = if (aconv f holfoot_disjoint_fmap_union_term) then () else Feedback.fail();


    fun fst_dest_bag t = (fst o bagSyntax.dest_bag) t handle HOL_ERR _ => [t];
    val (wL, rL) =  ((fn f => f ## f) fst_dest_bag)
           (pairSyntax.dest_pair wr)
    val wL' = fst_dest_bag w';

    fun wL_sys a b v =
       if not (tmem v wL') then sys a b v else
       (add_string "!" >> (sys a b v));
in
    ublock CONSISTENT 0 (
    (if (optionSyntax.is_some comment_opt) then
         (ublock INCONSISTENT 0 (
            ustyle [UserStyle "holfoot_comment"] (
            add_string "/*" >>
            add_break (1,3) >>
            add_loc_add_string 3 add_string add_break
                (label_list2ML (optionSyntax.dest_some comment_opt)) >>
            add_break (1,0) >>
            add_string "*/"
            )
         ) >>
         add_break (1,0)) else nothing) >>
    ublock INCONSISTENT (!holfoot_pretty_printer_block_indent) (
       add_string "[[w/r:" >>
       add_string " " >>
       pretty_print_list_sep "," (wL_sys, add_string, add_break) d wL >>
       add_string ";" >>
       add_break (1,0) >>
       ublock INCONSISTENT (!holfoot_pretty_printer_block_indent) (
          pretty_print_list_sep "," (sys, add_string, add_break) d rL >>
          add_string " " >>
          add_string "|"
       ) >>
       add_break (1,0) >>
       ublock INCONSISTENT (!holfoot_pretty_printer_block_indent) (
          ustyle [UserStyle "holfoot_frame_split___context"] (
             pretty_print_list_sep " *" (sys, add_string, add_break) d (fst_dest_bag context)
          ) >>
          add_string " " >>
          add_string "|"
       ) >>
       add_break (1,0) >>
       ublock INCONSISTENT (!holfoot_pretty_printer_block_indent) (
           ustyle [UserStyle "holfoot_frame_split___split"] (
              pretty_print_list_sep " *" (sys, add_string, add_break) d (fst_dest_bag split)
           ) >>
           add_string " " >>
           add_string "-->"
       ) >>
       add_break (1,0) >>
       ublock INCONSISTENT (!holfoot_pretty_printer_block_indent) (
          ustyle [UserStyle "holfoot_frame_split___imp"] (
             pretty_print_list_sep " *" (sys, add_string, add_break) d (fst_dest_bag imp)
          ) >>
          (if (aconv mode T) then
             (add_string " " >>
              add_string "|" >>
              add_break (1,2) >>
              add_string "...") else nothing) >>
          add_string "]]"
       )
    ))
end

fun holfoot_cond_triple_printer GS backend sys_raw (ppfns:term_pp_types.ppstream_funs) gravs d t = let
    open Portable term_pp_types smpp
    infix >>
    val {add_string,add_break,ublock,add_newline,ustyle,...} = ppfns
    fun sys gravs d' = sys_raw {gravs = gravs, depth = d', binderp = false}

    val (f, pre, prog, post) = dest_VAR_RES_COND_HOARE_TRIPLE t;
    val _ = if (aconv f holfoot_disjoint_fmap_union_term) then () else Feedback.fail();

    fun my_dest_var_res_prop p = let
       val (f', wr, re, b) = dest_var_res_prop (COND_PROP___STRONG_EXISTS_term_rewrite p);
       val _ = if (aconv f' holfoot_disjoint_fmap_union_term) then () else Feedback.fail();
       val (wL, _) = bagSyntax.dest_bag wr
       val (rL, _) = bagSyntax.dest_bag re
       val (bL, _) = bagSyntax.dest_bag b
    in
       (rL, wL, bL)
    end;

    val (pre_readL,  pre_writeL,  pre_condL ) = my_dest_var_res_prop pre;
    val (post_readL, post_writeL, post_condL) = my_dest_var_res_prop post;

    fun print_condition (wL, rL, cL) = (
       ublock INCONSISTENT (!holfoot_pretty_printer_block_indent) (
         ustyle [UserStyle "holfoot_spec"] (
            add_string "[[w/r:" >>
            add_string " " >>
            pretty_print_list_sep "," (sys, add_string, add_break) d wL >>
            add_string ";" >>
            (if (null rL) then nothing else (
               add_break (1,0) >>
               pretty_print_list_sep "," (sys, add_string, add_break) d rL
            )) >>
            add_string " " >>
            add_string "|" >>
            add_break (1,0) >>
            pretty_print_list_sep " *" (sys, add_string, add_break) d cL >>
            add_string "]]"
         )
       ));
in
    ublock CONSISTENT (0) (
       print_condition (pre_writeL, pre_readL, pre_condL) >>
       add_break (1,!holfoot_pretty_printer_block_indent) >>
       ublock CONSISTENT (!holfoot_pretty_printer_block_indent) (
          sys (Top, Top, Top) (d - 1) prog
       ) >>
       add_newline >>
       print_condition (post_writeL, post_readL, post_condL)
    )
end


val pretty_printer_list =
 [("holfoot_prop_is_equiv_false", ``VAR_RES_PROP_IS_EQUIV_FALSE c f wrb (sfb:holfoot_a_proposition -> num)``,    holfoot_prop_is_equiv_false_printer),
  ("holfoot_prop_is_equiv_false", ``~(VAR_RES_PROP_IS_EQUIV_FALSE c f wrb (sfb:holfoot_a_proposition -> num))``, holfoot_prop_is_equiv_false_printer),
  ("holfoot_specification", ``ASL_SPECIFICATION holfoot_separation_combinator locks
     (procs : (bool # 'b # ('c -> ('c, 'a, 'b, holfoot_state) asl_program) #
                           ('c -> ('c, 'a, 'b, holfoot_state) asl_program)) list)``, holfoot_specification_printer),
  ("holfoot_prog", ``prog:holfoot_program``, holfoot_prog_printer),
  ("holfoot_var", ``holfoot_var v``, holfoot_var_printer),
  ("holfoot_tag", ``holfoot_tag t``, holfoot_tag_printer),
  ("holfoot_expression", ``e:('a,'b,'c) var_res_expression``, holfoot_expression_printer),
  ("holfoot_pred", ``p:'a asl_predicate``, holfoot_pred_printer),
  ("holfoot_a_prop", ``x:'a set``, holfoot_a_prop_printer),
  ("holfoot_triple", ``VAR_RES_COND_HOARE_TRIPLE DISJOINT_FMAP_UNION pre (prog:holfoot_program) post``, holfoot_cond_triple_printer),
  ("holfoot_entails", ``VAR_RES_FRAME_SPLIT DISJOINT_FMAP_UNION mode wr w'
     frame split (imp:holfoot_a_proposition -> num) pred``, holfoot_frame_split_printer)
 ]:(string * Parse.term * term_grammar.userprinter) list;

val use_holfoot_pp = ref true
val _ = Feedback.register_btrace ("use holfoot_pp", use_holfoot_pp);

fun trace_user_printer (up:term_grammar.userprinter) =
   (fn GS => fn sys => fn ppfns => fn gravs => fn d => fn pps => fn t =>
   if (!use_holfoot_pp) then
       (up GS sys ppfns gravs d pps t)
          handle Interrupt => raise Interrupt
               | _         => raise term_pp_types.UserPP_Failed
   else
      raise term_pp_types.UserPP_Failed):term_grammar.userprinter


val pretty_printer_list_trace = map (fn (s, t, p) =>
   (s, t, trace_user_printer p)) pretty_printer_list
val _ = app (fn (s,_,c) => term_grammar.userSyntaxFns.register_userPP
                            {name = s, code = c})
            pretty_printer_list_trace

fun aup (s,pat,code) =
   (add_ML_dependency "holfoot_pp_print"; add_user_printer(s,pat))

fun temp_add_holfoot_pp () =
   (map temp_add_user_printer pretty_printer_list_trace;
    print "HOLFOOT pretty printing activated!\n");

fun temp_remove_holfoot_pp () =
   (map (temp_remove_user_printer o #1) pretty_printer_list_trace;
    print "HOLFOOT pretty printing deactivated!\n");

fun add_holfoot_pp_quiet () =
   (map aup pretty_printer_list_trace;());

fun add_holfoot_pp () =
    (add_holfoot_pp_quiet();
     print "HOLFOOT pretty printing activated!\n");

fun remove_holfoot_pp_quiet () =
   (map (remove_user_printer o #1) pretty_printer_list_trace;());

fun remove_holfoot_pp () =
   (remove_holfoot_pp_quiet ();
    print "HOLFOOT pretty printing deactivated!\n");


(*
open holfootParser
open holfoot_pp_print
val file = concat [examplesDir, "/automatic/list.sf"];
val t = parse_holfoot_file file

temp_remove_holfoot_pp ();temp_add_holfoot_pp ();t
temp_remove_holfoot_pp ();t
*)

val _ = Feedback.set_trace "PPBackEnd use annotations" 0
val _ = add_holfoot_pp_quiet();

end
