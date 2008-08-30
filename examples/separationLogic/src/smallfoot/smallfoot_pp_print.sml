structure smallfoot_pp_print :> smallfoot_pp_print =
struct

(*
quietdec := true;
loadPath := 
            (concat [Globals.HOLDIR, "/examples/separationLogic/src"]) :: 
            (concat [Globals.HOLDIR, "/examples/separationLogic/src/smallfoot"]) :: 
            !loadPath;

map load ["finite_mapTheory", "smallfootTheory"];
show_assums := true;
*)

open HolKernel Parse boolLib bossLib finite_mapTheory smallfootTheory smallfootSyntax;



(*
quietdec := false;
*)


val use_smallfoot_pretty_printer = ref true;
val smallfoot_pretty_printer_block_indent = ref 3;


fun smallfoot_p_expression_printer sys gravs d pps t = let
    open Portable term_pp_types
    val (op_term,args) = strip_comb t;
  in
    if (op_term = smallfoot_p_var_term)  then (
       (sys (Top, Top, Top) (d - 1) (hd (args)))
    ) else 
    if (op_term = smallfoot_p_const_term)  then (
       if ((hd args) = ``0:num``) then add_string pps "NULL" else
                sys (Top, Top, Top) (d - 1) (hd args)
    ) else (
      raise term_pp_types.UserPP_Failed
    )
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;




fun smallfoot_var_printer sys gravs d pps t = let
    open Portable term_pp_types
    val v_term = dest_smallfoot_var t;
  in
    add_string pps (stringLib.fromHOLstring v_term)
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;



fun smallfoot_tag_printer sys gravs d pps t = let
    open Portable term_pp_types
    val t_term = dest_smallfoot_tag t;
  in
    add_string pps (stringLib.fromHOLstring t_term)
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;



fun pretty_print_list not_last oper [] = () |
    pretty_print_list not_last oper [e] = (oper e) |
    pretty_print_list not_last oper (e1::e2::es) = 
    (oper e1;not_last ();(pretty_print_list not_last oper (e2::es)));




fun smallfoot_proccall_args_printer sys gravs d pps args_term =
   let
      open Portable term_pp_types
      val (refArgs_term, valArgs_term) = pairLib.dest_pair args_term;
      val (refArgsL, _) = listSyntax.dest_list refArgs_term;
      val (valArgsL, _) = listSyntax.dest_list valArgs_term;
      val pretty_print_arg_list = 
    	      pretty_print_list (fn () => (add_string pps ",";add_break pps (1,0))) 
	        (fn arg => sys (Top, Top, Top) (d - 1) arg);
   in
      add_string pps ("(");
      pretty_print_arg_list refArgsL;
      if (valArgsL = []) then () else (
          add_string pps ";";add_break pps (1,0);
	  pretty_print_arg_list valArgsL
      );
      add_string pps ")"
   end;



fun smallfoot_prog_printer sys gravs d pps t = let
    open Portable term_pp_types
    val (op_term,args) = strip_comb t;
  in
    if (op_term = smallfoot_prog_field_lookup_term)  then (
       let
          val v_term = el 1 args;
          val exp_term = el 2 args;
          val tag_term = el 3 args;
       in
          begin_block pps INCONSISTENT (!smallfoot_pretty_printer_block_indent);
          sys (Top, Top, Top) (d - 1) v_term;
          add_string pps " =";
          add_break pps (1,1);
          sys (Top, Top, Top) (d - 1) exp_term;
	  add_string pps ("->");
          sys (Top, Top, Top) (d - 1) tag_term;
	  end_block pps
       end
    ) else if (op_term = smallfoot_prog_field_assign_term)  then (
       let
          val exp_term = el 1 args;
          val tag_term = el 2 args;
          val exp2_term = el 3 args;
       in
          begin_block pps INCONSISTENT (!smallfoot_pretty_printer_block_indent);
          sys (Top, Top, Top) (d - 1) exp_term;
	  add_string pps ("->");
          sys (Top, Top, Top) (d - 1) tag_term;
          add_string pps " =";
          add_break pps (1,1);
          sys (Top, Top, Top) (d - 1) exp2_term;
	  end_block pps
       end 
    ) else if (op_term = smallfoot_prog_procedure_call_term)  then (
       let
          val name_term = el 1 args;
          val args_term = el 2 args;
       in
          begin_block pps INCONSISTENT (!smallfoot_pretty_printer_block_indent);
          add_string pps (stringLib.fromHOLstring name_term);
          smallfoot_proccall_args_printer sys gravs (d - 1) pps args_term;
          end_block pps
       end 
    ) else if (op_term = smallfoot_prog_parallel_procedure_call_term)  then (
       let
          val name1_term = el 1 args;
          val args1_term = el 2 args;
          val name2_term = el 3 args;
          val args2_term = el 4 args;
       in
          begin_block pps INCONSISTENT (!smallfoot_pretty_printer_block_indent);
          add_string pps (stringLib.fromHOLstring name1_term);
          smallfoot_proccall_args_printer sys gravs (d - 1) pps args1_term;
          add_string pps " || ";
          add_string pps (stringLib.fromHOLstring name2_term);
          smallfoot_proccall_args_printer sys gravs (d - 1) pps args2_term;
          end_block pps
       end 
    ) else if (op_term = smallfoot_prog_assign_term)  then (
       let
          val v_term = el 1 args;
          val exp_term = el 2 args;
       in
          begin_block pps INCONSISTENT (!smallfoot_pretty_printer_block_indent);
          sys (Top, Top, Top) (d - 1) v_term;
          add_string pps " =";
          add_break pps (1,1);
          sys (Top, Top, Top) (d - 1) exp_term;
          end_block pps
       end    
    ) else if (op_term = smallfoot_prog_dispose_term)  then (
       let
          val exp_term = el 1 args;
       in
          begin_block pps INCONSISTENT (!smallfoot_pretty_printer_block_indent);
          add_string pps "dispose ";
          sys (Top, Top, Top) (d - 1) exp_term;
	  end_block pps
       end
    ) else if (op_term = smallfoot_prog_new_term)  then (
       let
          val v_term = el 1 args;
       in
          begin_block pps INCONSISTENT (!smallfoot_pretty_printer_block_indent);
          sys (Top, Top, Top) (d - 1) v_term;
          add_string pps " =";
          add_break pps (1,!smallfoot_pretty_printer_block_indent);
          add_string pps "new()";
	  end_block pps
       end
    ) else if (op_term = smallfoot_prog_cond_term)  then (
       let
          val prop_term = el 1 args;
          val prog1_term = el 2 args;
          val prog2_term = el 3 args;
       in
          begin_block pps CONSISTENT 0;
          add_string pps "if ";
          sys (Top, Top, Top) (d - 1) prop_term;
          add_string pps " then {";
          add_break pps (1,(!smallfoot_pretty_printer_block_indent));
          begin_block pps INCONSISTENT 0;
          sys (Top, Top, Top) (d - 1) prog1_term;
          end_block pps;
          add_break pps (1,0);
          add_string pps "} else {";
          add_break pps (1,(!smallfoot_pretty_printer_block_indent));
          begin_block pps INCONSISTENT 0;
          sys (Top, Top, Top) (d - 1) prog2_term;
          end_block pps;
          add_break pps (1,0);
          add_string pps "}";
          end_block pps
       end
    ) else if (op_term = smallfoot_prog_while_with_invariant_term)  then (
       let
          val inv_term = el 1 args;
          val prop_term = el 2 args;
          val prog_term = el 3 args;
       in
          begin_block pps CONSISTENT 0;
          add_string pps "while ";
          sys (Top, Top, Top) (d - 1) prop_term;
          add_break pps (1,(!smallfoot_pretty_printer_block_indent));

          add_string pps "[";
          begin_block pps INCONSISTENT 0;
          sys (Top, Top, Top) (d - 1) inv_term;
	  end_block pps;
          add_string pps "] {";
          add_break pps (1,(!smallfoot_pretty_printer_block_indent));
          begin_block pps INCONSISTENT 0;
          sys (Top, Top, Top) (d - 1) prog_term;
          end_block pps;
          add_break pps (1,0);
          add_string pps "}";
          end_block pps
       end
    ) else if (op_term = smallfoot_prog_with_resource_term)  then (
       let
          val res_term = el 1 args;
          val cond_term = el 2 args;
          val prog_term = el 3 args;
       in
          begin_block pps CONSISTENT 0;
          add_string pps "with ";
          add_string pps (stringLib.fromHOLstring res_term);
          add_string pps " when (";
          sys (Top, Top, Top) (d - 1) cond_term;
          add_string pps ") {";
          add_break pps (1,(!smallfoot_pretty_printer_block_indent));
          begin_block pps INCONSISTENT 0;
          sys (Top, Top, Top) (d - 1) prog_term;
          end_block pps;
          add_break pps (1,0);
          add_string pps "}";
          end_block pps
       end
    ) else if (op_term = smallfoot_prog_aquire_resource_term)  then (
       let	   
          val cond_term = el 1 args;
          val var_term = el 2 args;
          val inv_term = el 3 args;
       in
          begin_block pps INCONSISTENT 0;
          add_string pps "abstracted enter with-resource-context";
          add_break pps (1,(!smallfoot_pretty_printer_block_indent));
          add_string pps "(";
          sys (Top, Top, Top) (d - 1) cond_term;
          add_string pps ")";
          add_break pps (1,(!smallfoot_pretty_printer_block_indent));
          sys (Top, Top, Top) (d - 1) var_term;
          add_break pps (1,(!smallfoot_pretty_printer_block_indent));
          sys (Top, Top, Top) (d - 1) inv_term;
          end_block pps
       end
    ) else if (op_term = smallfoot_prog_release_resource_term)  then (
       let
          val var_term = el 1 args;
          val inv_term = el 2 args;
       in
          begin_block pps INCONSISTENT 0;
          add_string pps "abstracted leave with-resource-context";
          add_break pps (1,(!smallfoot_pretty_printer_block_indent));
          sys (Top, Top, Top) (d - 1) var_term;
          add_break pps (1,(!smallfoot_pretty_printer_block_indent));
          sys (Top, Top, Top) (d - 1) inv_term;
          end_block pps
       end
    ) else if (op_term = smallfoot_prog_local_var_term) orelse 
	      (op_term = smallfoot_prog_val_arg_term) then (
       let
          val (l, t') = dest_local_vars t;          
	  val _ = if (l = []) then raise term_pp_types.UserPP_Failed else ();
       in
          begin_block pps INCONSISTENT 0;             
          add_string pps "local";	  
          add_break pps (1,!smallfoot_pretty_printer_block_indent);
          pretty_print_list 
                (fn () => (add_string pps ",";
                           add_break pps (1, !smallfoot_pretty_printer_block_indent)))
   	        (fn (v,vt) => (
                begin_block pps CONSISTENT (!smallfoot_pretty_printer_block_indent);
		if (isSome vt) then (
                   add_string pps "(";
                   sys (Top, Top, Top) (d - 1) v;
                   add_string pps " = ";
                   sys (Top, Top, Top) (d - 1) (valOf vt);
                   add_string pps ")"
                ) else (
                   sys (Top, Top, Top) (d - 1) v
                );
                end_block pps)) l;
          add_string pps ";";
          add_break pps (1,0);        
          sys (Top, Top, Top) (d - 1) t';
          end_block pps
      end
    ) else if (op_term = smallfoot_cond_choose_const_best_local_action_term)  then (
      let
         val (argL1_term,_) = listSyntax.dest_list (el 6 args);
         val (argL2_term,_) = listSyntax.dest_list (el 5 args);
	 val argL1_string = map term_to_string argL1_term;
	 val argL2_string = map term_to_string argL2_term;
	 val argL1_const = map (fn n => mk_var (n, numSyntax.num)) argL1_string
	 val argL2_const = map (fn n => mk_var (n, numSyntax.num)) argL2_string

	 val argL_term = pairLib.mk_pair
			    (listSyntax.mk_list (argL1_const, numSyntax.num),
			     listSyntax.mk_list (argL2_const, numSyntax.num));

         val pre_term = mk_comb (el 2 args, argL_term)
         val post_term = mk_comb (el 3 args, argL_term)

         val pre_term'= (#3 o dest_smallfoot_prop o rhs o concl) 
                           (SIMP_CONV list_ss [bagTheory.BAG_UNION_INSERT, bagTheory.BAG_UNION_EMPTY] pre_term)
         val post_term'= (#3 o dest_smallfoot_prop o rhs o concl) 
                           (SIMP_CONV list_ss [bagTheory.BAG_UNION_INSERT, bagTheory.BAG_UNION_EMPTY] post_term)
      in
         begin_block pps CONSISTENT 0;
         add_string pps "abstracted code";
         add_break pps (1,(!smallfoot_pretty_printer_block_indent));
         sys (Top, Top, Top) (d - 1) pre_term';
         add_break pps (1,(!smallfoot_pretty_printer_block_indent));
         sys (Top, Top, Top) (d - 1) post_term';
         end_block pps
      end
    ) else if (op_term = smallfoot_prog_block_term)  then (
       let
          val (argL_term, _) = listSyntax.dest_list (el 1 args);
       in
	  if argL_term = [] then () else
          if length argL_term = 1 then sys (Top, Top, Top) (d - 1) (hd argL_term) else
          (
             begin_block pps CONSISTENT 0;             
	     pretty_print_list (fn () => (add_break pps (1,0)))
   	        (fn stm =>                
                (begin_block pps CONSISTENT (!smallfoot_pretty_printer_block_indent);
                sys (Top, Top, Top) (d - 1) stm;
                add_string pps ";";
                end_block pps
                )) argL_term;
             end_block pps
          )
       end
    ) else( 

      raise term_pp_types.UserPP_Failed
    )
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;




fun pretty_print_infix_operator sys d pps args opstring =
       let
          open Portable term_pp_types
          val l_term = el 1 args;
          val r_term = el 2 args;
       in
          begin_block pps INCONSISTENT (!smallfoot_pretty_printer_block_indent);
          sys (Top, Top, Top) (d - 1) l_term;
          add_string pps (concat [" ", opstring]);
          add_break pps (1,1); 
          sys (Top, Top, Top) (d - 1) r_term;
	  end_block pps
       end;


fun smallfoot_prop_printer sys gravs d pps t = let
    open Portable term_pp_types
    val (op_term,args) = strip_comb t;
  in
    if (op_term = smallfoot_p_equal_term)  then (
      if (el 1 args = el 2 args) then 
	  add_string pps "true"
      else
          pretty_print_infix_operator sys d pps args "=="
    ) else if (op_term = smallfoot_p_unequal_term)  then (
      if (el 1 args = el 2 args) then 
	  add_string pps "false"
      else
          pretty_print_infix_operator sys d pps args "!="
    ) else if (op_term = smallfoot_p_greatereq_term)  then (
      pretty_print_infix_operator sys d pps args ">="
    ) else if (op_term = smallfoot_p_greater_term)  then (
      pretty_print_infix_operator sys d pps args ">"
    ) else if (op_term = smallfoot_p_lesseq_term)  then (
      pretty_print_infix_operator sys d pps args "<="
    ) else if (op_term = smallfoot_p_less_term)  then (
      pretty_print_infix_operator sys d pps args "<"
    ) else if (op_term = smallfoot_p_and_term)  then (
      pretty_print_infix_operator sys d pps args "/\\"
    ) else if (op_term = smallfoot_p_or_term) then (
      pretty_print_infix_operator sys d pps args "\\/"
    ) else (
      raise term_pp_types.UserPP_Failed
    )
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;



fun smallfoot_ae_printer sys gravs d pps t = let 
    open Portable term_pp_types
    val (op_term,args) = strip_comb t;
  in
    if (op_term = smallfoot_ae_var_term)  then (
      sys (Top, Top, Top) (d - 1) (hd args)
    ) else if (op_term = smallfoot_ae_const_term)  then (
      sys (Top, Top, Top) (d - 1) (hd args)
    ) else if (op_term = smallfoot_ae_null_term)  then (
      add_string pps "NULL"
    ) else (
      raise term_pp_types.UserPP_Failed
    )
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;


fun smallfoot_a_prop_printer sys gravs d pps t = let
    open Portable term_pp_types
    val (op_term,args) = strip_comb t;
  in
    if (op_term = smallfoot_ap_star_term)  then (
      sys (Top, Top, Top) (d - 1) (el 1 args);
      add_string pps " *";
      add_break pps (1,0);
      sys (Top, Top, Top) (d - 1) (el 2 args)
    ) else if (op_term = smallfoot_ap_equal_term)  then (
      sys (Top, Top, Top) (d - 1) (el 1 args);
      add_string pps " == ";
      sys (Top, Top, Top) (d - 1) (el 2 args)
    ) else if (op_term = smallfoot_ap_unequal_term)  then (
      sys (Top, Top, Top) (d - 1) (el 1 args);
      add_string pps " != ";
      sys (Top, Top, Top) (d - 1) (el 2 args)
    ) else if (op_term = smallfoot_ap_greater_term)  then (
      sys (Top, Top, Top) (d - 1) (el 1 args);
      add_string pps " > ";
      sys (Top, Top, Top) (d - 1) (el 2 args)
    ) else if (op_term = smallfoot_ap_greatereq_term)  then (
      sys (Top, Top, Top) (d - 1) (el 1 args);
      add_string pps " >= ";
      sys (Top, Top, Top) (d - 1) (el 2 args)
    ) else if (op_term = smallfoot_ap_less_term)  then (
      sys (Top, Top, Top) (d - 1) (el 1 args);
      add_string pps " < ";
      sys (Top, Top, Top) (d - 1) (el 2 args)
    ) else if (op_term = smallfoot_ap_lesseq_term)  then (
      sys (Top, Top, Top) (d - 1) (el 1 args);
      add_string pps " <= ";
      sys (Top, Top, Top) (d - 1) (el 2 args)
    ) else if (op_term = smallfoot_ap_emp_term)  then (
      add_string pps "emp"
    ) else if (op_term = smallfoot_ap_list_term)  then (
      add_string pps "list(";
      sys (Top, Top, Top) (d - 1) (el 1 args);
      add_string pps "; ";
      sys (Top, Top, Top) (d - 1) (el 2 args);
      add_string pps ")"
    ) else if (op_term = smallfoot_ap_list_seg_term)  then (
      add_string pps "lseg(";
      sys (Top, Top, Top) (d - 1) (el 1 args);
      add_string pps "; ";
      sys (Top, Top, Top) (d - 1) (el 2 args);
      add_string pps ", ";
      sys (Top, Top, Top) (d - 1) (el 3 args);
      add_string pps ")"
    ) else if (op_term = smallfoot_ap_points_to_term) then (
      sys (Top, Top, Top) (d - 1) (el 1 args);
      add_string pps " |-> ";
      let
	  val (plist,rest) = dest_finite_map (el 2 args);
      in
          if ((length plist) = 1) then () else add_string pps "[";
          pretty_print_list (fn () => (add_string pps ", "))
   	        (fn (tag,exp) =>                
                (sys (Top, Top, Top) (d - 1) tag;
                add_string pps ":";
                sys (Top, Top, Top) (d - 1) exp
                )) plist;
	  if (isSome rest) then (
	      if (length plist = 0) then () else add_string pps (", ");
	      add_string pps ("..."))
          else ();
          if (length plist = 1) then () else add_string pps "]"
      end
    ) else if (op_term = smallfoot_ap_cond_term)  then (
      add_string pps "if ";
      sys (Top, Top, Top) (d - 1) (el 1 args);
      add_string pps " == ";
      sys (Top, Top, Top) (d - 1) (el 2 args);
      add_string pps " then ";
      sys (Top, Top, Top) (d - 1) (el 3 args);
      add_string pps " else ";
      sys (Top, Top, Top) (d - 1) (el 4 args);
      add_string pps " end"
    ) else if (op_term = smallfoot_ap_unequal_cond_term)  then (
      add_string pps "(";
      if (el 1 args = el 2 args) then
         add_string pps "false"
      else
        (sys (Top, Top, Top) (d - 1) (el 1 args);
         add_string pps " != ";
         sys (Top, Top, Top) (d - 1) (el 2 args));
      add_string pps " : ";
      sys (Top, Top, Top) (d - 1) (el 3 args);
      add_string pps ")"
    ) else if (op_term = smallfoot_ap_equal_cond_term)  then (
      add_string pps "(";
      if (el 1 args = el 2 args) then
         add_string pps "true"
      else
        (sys (Top, Top, Top) (d - 1) (el 1 args);
         add_string pps " == ";
         sys (Top, Top, Top) (d - 1) (el 2 args));
      add_string pps " : ";
      sys (Top, Top, Top) (d - 1) (el 3 args);
      add_string pps ")"
    ) else (
      raise term_pp_types.UserPP_Failed
    )
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;





fun smallfoot_specification_printer sys gravs d pps t = let
    open Portable term_pp_types
    val (resL,funL) = dest_SMALLFOOT_SPECIFICATION t;


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
         val (fun_name,abs_body,abs_pre_wrapper,abs_post) = 
	     (el 1 argL, el 2 argL, el 3 argL, el 4 argL);

         val wrapper_argL = snd (strip_comb abs_pre_wrapper);
         val (argL1_term,_) = listSyntax.dest_list (el 1 wrapper_argL);
         val (argL2_term,_) = listSyntax.dest_list (el 2 wrapper_argL);
         val (argL3_term,_) = listSyntax.dest_list (el 3 wrapper_argL);
	 val argL2_string = map stringLib.fromHOLstring argL2_term;
	 val argL3_string = map stringLib.fromHOLstring argL3_term;

	 val argL1_const = map (fn n => mk_comb (smallfoot_var_term, n)) argL1_term;
	 val argL2_const = map (fn n => mk_var (n, numSyntax.num)) argL2_string
	 val argL3_const = map (fn n => mk_var (n, numSyntax.num)) argL3_string
			       
	 val argL_term =  pairLib.mk_pair
	   		       (listSyntax.mk_list (argL1_const, ``:smallfoot_var``),
			        listSyntax.mk_list (argL2_const, numSyntax.num));

	 val ext_argL_term = listSyntax.mk_list (argL3_const, numSyntax.num);


         val body_term = mk_comb (abs_body, argL_term);
         val pre_term = list_mk_comb (el 4 wrapper_argL, [argL_term, ext_argL_term]);
         val post_term = list_mk_comb (abs_post, [argL_term, ext_argL_term]);


	 fun term_simp t = (rhs o concl) (SIMP_CONV list_ss [bagTheory.BAG_UNION_INSERT, bagTheory.BAG_UNION_EMPTY] t)
         val body_term' = term_simp body_term;
         val pre_term' = term_simp pre_term;
         val post_term' = term_simp post_term;
      in
         (fun_name, argL_term, pre_term', body_term', post_term')
      end

    val funtL = map funt_preprocess (fst (listSyntax.dest_list funL));


  in
     begin_block pps CONSISTENT 0;
     add_string pps "SMALLFOOT_SPECIFICATION (";
     add_newline pps;
     begin_block pps CONSISTENT (!smallfoot_pretty_printer_block_indent);
     add_newline pps;
     map (fn (s,vars,prop) => (
                begin_block pps INCONSISTENT 0;
                add_string pps "resource ";
                add_string pps (stringLib.fromHOLstring s);
                add_break pps (1, (!smallfoot_pretty_printer_block_indent));
                sys (Top, Top, Top) (d - 1) vars;
                add_break pps (1, (!smallfoot_pretty_printer_block_indent));
                add_string pps "{";
                sys (Top, Top, Top) (d - 1) prop;
                add_string pps "}";
		add_newline pps;
                add_newline pps;
                end_block pps)) restL;
     map (fn (fun_name, argL_term, pre_term, body_term, post_term) => (
                begin_block pps INCONSISTENT 0;
                add_string pps (stringLib.fromHOLstring fun_name);
                smallfoot_proccall_args_printer sys gravs (d - 1) pps argL_term;
                add_break pps (1,(!smallfoot_pretty_printer_block_indent));
                add_string pps "[";

                begin_block pps INCONSISTENT 0;
                sys (Top, Top, Top) (d - 1) pre_term;
                end_block pps;
                
                add_string pps "] {";
		add_newline pps;
                add_string pps "   ";


                begin_block pps INCONSISTENT 0;
                sys (Top, Top, Top) (d - 1) body_term;
                end_block pps;

		add_newline pps;
                add_string pps "}";
                add_string pps " [";

                begin_block pps INCONSISTENT 0;
                sys (Top, Top, Top) (d - 1) post_term;
                end_block pps;
                add_string pps "]";


		add_newline pps;
		add_newline pps;
                end_block pps)) funtL;
     end_block pps;
     add_newline pps;
     add_string pps ")";
     end_block pps
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;



fun smallfoot_pretty_printer sys gravs d pps t =
  let
    val _ = if !use_smallfoot_pretty_printer then () else raise term_pp_types.UserPP_Failed;
    val t_type = type_of t;
  in
    if t_type = smallfoot_prog_type then 
       smallfoot_prog_printer sys gravs d pps t 
    else if t_type = smallfoot_p_expression_type then 
       smallfoot_p_expression_printer sys gravs d pps t 
    else if t_type = smallfoot_p_proposition_type then 
       smallfoot_prop_printer sys gravs d pps t 
    else if t_type = smallfoot_var_type then 
       smallfoot_var_printer sys gravs d pps t 
    else if t_type = smallfoot_tag_type then 
       smallfoot_tag_printer sys gravs d pps t 
    else if t_type = smallfoot_a_proposition_type then 
       smallfoot_a_prop_printer sys gravs d pps t 
    else if t_type = smallfoot_a_expression_type then 
       smallfoot_ae_printer sys gravs d pps t 
    else if is_SMALLFOOT_SPECIFICATION t then 
       smallfoot_specification_printer sys gravs d pps t 
    else (
      raise term_pp_types.UserPP_Failed
    )
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

   
fun temp_add_smallfoot_pp () = temp_add_user_printer ({Tyop = "", Thy = ""}, smallfoot_pretty_printer);


end
