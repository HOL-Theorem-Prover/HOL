structure smallfootParser :> smallfootParser =
struct

(*
quietdec := true;
loadPath := 
            (concat [Globals.HOLDIR, "/examples/separationLogic/src"]) :: 
            (concat [Globals.HOLDIR, "/examples/separationLogic/src/smallfoot"]) :: 
            !loadPath;

map load ["finite_mapTheory", "smallfootTheory", "Parser", "Lexer","Lexing", "Nonstdio",
	  "Parsetree"];
show_assums := true;
*)

open HolKernel Parse boolLib finite_mapTheory smallfootTheory smallfootSyntax
     Parsetree;


(*
quietdec := false;
*)

 
fun createLexerStream (is : BasicIO.instream) =
  Lexing.createLexer (fn buff => fn n => Nonstdio.buff_input is buff 0 n)


fun parseExprPlain lexbuf =
    let val expr = Parser.program Lexer.token lexbuf
    in
	Parsing.clearParser();
	expr
    end
    handle exn => (Parsing.clearParser(); raise exn);

fun parse file =
    let val is     = Nonstdio.open_in_bin file
        val lexbuf = createLexerStream is
	val expr   = parseExprPlain lexbuf
	             handle exn => (BasicIO.close_in is; raise exn)
    in 
        BasicIO.close_in is;
	expr
    end


fun print_file file =
    let val is     = Nonstdio.open_in_bin file
        val _ = while (not (BasicIO.end_of_stream is)) do (print (BasicIO.inputc is 100))
        val _ = BasicIO.close_in is;
    in 
         ()
    end

(*
val file = "/home/tuerk/Downloads/smallfoot/EXAMPLES/business2.sf";
val file = "/home/tt291/Downloads/smallfoot/EXAMPLES/business2.sf";

val prog = parse file;
*)


exception smallfoot_unsupported_feature_exn of string;

fun smallfoot_p_expression2term (Pexp_ident x) =
   if (String.sub (x, 0) = #"#") then  
      let
         val var_term = mk_var (String.substring(x, 1, (String.size x) - 1),
				numLib.num);
         val term = mk_comb(smallfoot_p_const_term, var_term) 
      in 
         (term, empty_tmset)
      end
   else
      let
         val var_term = string2smallfoot_var x;
         val term = mk_comb(smallfoot_p_var_term, var_term) 
      in 
         (term, HOLset.add (empty_tmset, var_term))
      end
| smallfoot_p_expression2term (Pexp_num n) =
     (mk_comb(smallfoot_p_const_term, numLib.term_of_int n), empty_tmset)
| smallfoot_p_expression2term (Pexp_prefix _) =
	Raise (smallfoot_unsupported_feature_exn "Pexp_prefix") 
| smallfoot_p_expression2term (Pexp_infix (opstring, e1, e2)) =
	let
		val opterm = if (opstring = "-") then smallfoot_p_sub_term else
			if (opstring = "+") then smallfoot_p_add_term else
			if (opstring = "==") then smallfoot_p_equal_term else
			if (opstring = "!=") then smallfoot_p_unequal_term else
			if (opstring = "<=") then smallfoot_p_lesseq_term else
			if (opstring = "<") then smallfoot_p_less_term else
			if (opstring = ">=") then smallfoot_p_greater_term else
			if (opstring = ">") then smallfoot_p_greatereq_term else
			Raise (smallfoot_unsupported_feature_exn ("Pexp_infix "^opstring));
		val (t1,vs1) = smallfoot_p_expression2term e1;
		val (t2,vs2) = smallfoot_p_expression2term e2;
	in
		(list_mk_comb (opterm, [t1, t2]), HOLset.union (vs1, vs2))
	end;



fun smallfoot_a_expression2term ex_vars (Aexp_ident x) =
   if (String.sub (x, 0) = #"#") then  
      let
         val var_term = mk_var (String.substring(x, 1, (String.size x) - 1),
				numLib.num);
         val term = mk_comb(smallfoot_ae_const_term, var_term) 
      in 
         (term, empty_tmset, ex_vars)
      end
   else if (String.sub (x, 0) = #"_") then  
      let
         val var_name = String.substring(x, 1, (String.size x) - 1);
         val (var_name, needs_variant) =
	     if (var_name = "") then ("c", true) else (var_name, false);
	     
         val var_term = mk_var (var_name, numLib.num);         
         val var_term = if (needs_variant) then variant ex_vars var_term else
			   var_term;

         val term = mk_comb(smallfoot_ae_const_term, var_term) 
      in 
         (term, empty_tmset, if (mem var_term ex_vars) then ex_vars else var_term::ex_vars)
      end
   else
      let
         val var_term = string2smallfoot_var x;
         val term = mk_comb(smallfoot_ae_var_term, var_term) 
      in 
         (term, HOLset.add (empty_tmset, var_term), ex_vars)
      end
| smallfoot_a_expression2term ex_vars (Aexp_num n) =
	(if n = 0 then smallfoot_ae_null_term else
  	mk_comb(smallfoot_ae_const_term, numLib.term_of_int n),
	 empty_tmset, ex_vars)
| smallfoot_a_expression2term _ _ =
	Raise (smallfoot_unsupported_feature_exn "Aexp");




(*
val aexp1 = Aexp_ident "test";
val aexp2 = Aexp_num 0;
val aexp3 = Aexp_num 5;
val tag = "tl";
val tagL = "l";
val tagR = "r";

val ap1 = Aprop_equal(aexp1, aexp2);
val ap2 = Aprop_false;
val ap3 = Aprop_infix ("<", aexp2, aexp1);


val pl = [(tagL, aexp1), (tagR, aexp2)]
*)


val tag_a_expression_fmap_emp_term = ``FEMPTY:(smallfoot_tag |-> smallfoot_a_expression)``;
val tag_a_expression_fmap_update_term = ``FUPDATE:(smallfoot_tag |-> smallfoot_a_expression)->
(smallfoot_tag # smallfoot_a_expression)->(smallfoot_tag |-> smallfoot_a_expression)``;


fun tag_a_expression_list2term ex_vars [] = (tag_a_expression_fmap_emp_term,empty_tmset, ex_vars) |
      tag_a_expression_list2term ex_vars ((tag,aexp1)::l) =
		let
			val tag_term = string2smallfoot_tag tag;
			val (exp_term,new_var_set, new_ex_var_list) = smallfoot_a_expression2term ex_vars aexp1;
			val p = pairLib.mk_pair (tag_term,exp_term);
			val (rest,rest_var_set, ex_var_list) = tag_a_expression_list2term new_ex_var_list l;
			val comb_term = list_mk_comb (tag_a_expression_fmap_update_term, [rest, p]);
			val comb_var_set = HOLset.union (new_var_set, rest_var_set);
		in
                        (comb_term, comb_var_set, ex_var_list)
		end;



fun smallfoot_a_space_pred2term contextOpt ex_vars (Aspred_list (tag,aexp1)) =
        let
	    val (exp_term, var_set, ex_var_list) = smallfoot_a_expression2term ex_vars aexp1;
            val list_term = list_mk_comb(smallfoot_ap_list_term, [string2smallfoot_tag tag, 
			     exp_term]);
        in
            (list_term, var_set, ex_var_list)
        end
|     smallfoot_a_space_pred2term contextOpt ex_vars (Aspred_listseg (tag,aexp1,aexp2)) =
        let
	    val (exp_term1, var_set1, ex_vars2) = smallfoot_a_expression2term ex_vars aexp1;
	    val (exp_term2, var_set2, ex_vars3) = smallfoot_a_expression2term ex_vars2 aexp2;
	    val comb_term = list_mk_comb(smallfoot_ap_list_seg_term, [string2smallfoot_tag tag, 
			     exp_term1, exp_term2]);
        in
            (comb_term, HOLset.union (var_set1, var_set2), ex_vars3)
        end
|     smallfoot_a_space_pred2term contextOpt ex_vars (Aspred_dlseg _) =
  	Raise (smallfoot_unsupported_feature_exn ("Aspred_dl_seg"))
	
|     smallfoot_a_space_pred2term contextOpt ex_vars (Aspred_tree (tagL,tagR,aexp1)) =
        let
	    val (exp_term, var_set, ex_vars2) = smallfoot_a_expression2term ex_vars aexp1;
            val comb_term = list_mk_comb(smallfoot_ap_bintree_term, [
     			     pairLib.mk_pair(string2smallfoot_tag tagL, string2smallfoot_tag tagR), 
			     exp_term])
        in
            (comb_term, var_set, ex_vars2)
        end
|     smallfoot_a_space_pred2term contextOpt ex_vars (Aspred_empty) =
	(smallfoot_ap_stack_true_term, empty_tmset, ex_vars)
|     smallfoot_a_space_pred2term contextOpt ex_vars (Aspred_hol s) =
        if (not (isSome contextOpt)) then
   	    (mk_smallfoot_ap_unknown s, empty_tmset, ex_vars)
        else
            ((Parse.parse_in_context [valOf contextOpt] [QUOTE s], empty_tmset, ex_vars)
            handle HOL_ERR _ =>
          	    (print ("Could not parse "^s^"!\n");(mk_smallfoot_ap_unknown s, empty_tmset,ex_vars)))

|     smallfoot_a_space_pred2term contextOpt ex_vars (Aspred_pointsto (aexp1, pl)) =
        let
	    val (term1, var_set1, ex_vars2) = smallfoot_a_expression2term ex_vars aexp1;
	    val (term2, var_set2, ex_vars3) = tag_a_expression_list2term ex_vars2 pl;
	    val comb_term = list_mk_comb(smallfoot_ap_points_to_term, [term1, term2]); 
        in
            (comb_term, HOLset.union (var_set1,var_set2), ex_vars3)
        end;





fun unzip3 [] = ([],[],[])
  | unzip3 ((a,b,c)::L) =
    let
	val (aL,bL,cL) = unzip3 L;
    in 
       (a::aL, b::bL, c::cL)
    end;


(*
fun list_mk_comb___with_vars op_term sub_fun l =
    let
	val term_var_l = map sub_fun l;
        val (termL, setL, ex_varsL) = unzip3 term_var_l;
        val set_union = foldr HOLset.union empty_tmset setL;
        val term = list_mk_comb (op_term, termL);
        val ex_vars = flatten ex_varsL;
    in
        (term, set_union, ex_vars)
    end;
*)

fun mk_comb2___with_vars op_term sub_fun ex_vars a1 a2 =
    let
	val (term1,set1,ex_vars1) = sub_fun ex_vars a1;
	val (term2,set2,ex_vars2) = sub_fun ex_vars1 a2;

        val set_union = HOLset.union (set1,set2);
        val term = list_mk_comb (op_term, [term1,term2]);
    in
        (term, set_union, ex_vars2)
    end;


(*
val t = 
Aprop_ifthenelse(Aprop_equal(Aexp_ident "y", Aexp_ident "x"),
                 Aprop_spred(Aspred_list("tl", Aexp_ident "x")),
                 Aprop_spred(Aspred_list("tl", Aexp_ident "x")))

fun dest_ifthenelse (Aprop_ifthenelse (Aprop_equal (aexp1, aexp2), ap1,ap2)) =
  (aexp1, aexp2, ap1, ap2)


val (aexp1, aexp2, ap1, ap2) = dest_ifthenelse t
*)


fun smallfoot_a_proposition2term_context contextOpt ex_vars (Aprop_infix (opString, aexp1, aexp2)) =
	let
		val op_term = if (opString = "<") then smallfoot_ap_less_term else
				       if (opString = "<=") then smallfoot_ap_lesseq_term else
				       if (opString = ">") then smallfoot_ap_greater_term else
				       if (opString = ">=") then smallfoot_ap_greatereq_term else
		  		       Raise (smallfoot_unsupported_feature_exn ("Aexp_infix "^opString))
	in
		mk_comb2___with_vars op_term smallfoot_a_expression2term ex_vars aexp1 aexp2
	end
| smallfoot_a_proposition2term_context contextOpt ex_vars (Aprop_equal (aexp1, aexp2)) =
	mk_comb2___with_vars smallfoot_ap_equal_term smallfoot_a_expression2term ex_vars aexp1 aexp2
| smallfoot_a_proposition2term_context contextOpt ex_vars (Aprop_not_equal (aexp1, aexp2)) =
	mk_comb2___with_vars smallfoot_ap_unequal_term smallfoot_a_expression2term ex_vars aexp1 aexp2
| smallfoot_a_proposition2term_context contextOpt ex_vars (Aprop_false) =
	(smallfoot_ap_false_term, empty_tmset, ex_vars)
| smallfoot_a_proposition2term_context contextOpt ex_vars (Aprop_ifthenelse (Aprop_equal (aexp1, aexp2), ap1,ap2)) =
        let
           val (exp1_term, exp1_set, ex_vars2) = smallfoot_a_expression2term ex_vars aexp1;
           val (exp2_term, exp2_set, ex_vars3) = smallfoot_a_expression2term ex_vars2 aexp2;
           val (prop1_term, prop1_set, ex_vars4) = smallfoot_a_proposition2term_context contextOpt ex_vars3 ap1;
           val (prop2_term, prop2_set, ex_vars5) = smallfoot_a_proposition2term_context contextOpt ex_vars4 ap2;
	   val t = list_mk_comb (smallfoot_ap_cond_term, [exp1_term, exp2_term, prop1_term, prop2_term])
           val set_union = foldr HOLset.union exp1_set [exp2_set, prop1_set, prop2_set];
        in
	   (t, set_union, ex_vars5) 
        end
| smallfoot_a_proposition2term_context contextOpt ex_vars (Aprop_ifthenelse (_, ap2,ap3)) =
  Raise (smallfoot_unsupported_feature_exn "Currently only equality checks are allowed as conditions in propositions")
| smallfoot_a_proposition2term_context contextOpt ex_vars (Aprop_star (ap1, ap2)) =
	mk_comb2___with_vars smallfoot_ap_star_term (smallfoot_a_proposition2term_context contextOpt) ex_vars ap1 ap2
| smallfoot_a_proposition2term_context contextOpt ex_vars (Aprop_spred sp) =
	smallfoot_a_space_pred2term contextOpt ex_vars sp;



val asl_exists_term = fst (dest_comb ``asl_exists x. K T``)

fun smallfoot_a_proposition2term x =
let
   val (t1,_, _) = smallfoot_a_proposition2term_context NONE [] x;
   val (t2,ts, ex_vars) = smallfoot_a_proposition2term_context (SOME t1) [] x;

   val t3 = foldr (fn (v,t) => 
	    let
               val t_abs = pairLib.mk_pabs (v, t);
               val t' = mk_icomb (asl_exists_term, t_abs);
            in
	       t'
	    end) t2 ex_vars
in
   (t3,ts)
end;

(*
val x = 
 Aprop_spred(Aspred_pointsto(Aexp_ident "r",
                                                                              [("tl",
                                                                                Aexp_ident "_b")])
)


val x = 
 Aprop_star(Aprop_star(Aprop_spred(Aspred_pointsto(Aexp_ident "r",
                                                                              [("tl",
                                                                                Aexp_ident "_b")])),
                                                  Aprop_spred(Aspred_pointsto(Aexp_ident "_b",
                                                                              [("tl",
                                                                                Aexp_ident "_tf")]))),
                                       Aprop_spred(Aspred_listseg("tl",
                                                                  Aexp_ident "_tf",
                                                                  Aexp_ident "r")))
*)


fun unzip4 [] = ([],[],[],[])
  | unzip4 ((a,b,c,d)::L) =
    let
	val (aL,bL,cL,dL) = unzip4 L;
    in 
       (a::aL, b::bL, c::cL, d::dL)
    end;

    


(*
  val (wp,rp,d_opt,Pterm) = (write_var_set,read_var_set,SOME arg_refL,preCond);
*)

fun mk_smallfoot_prop_input wp rp d_opt Pterm =
    let
	val (d_list,rp) = if isSome d_opt then
		        let
			    val d_list = valOf d_opt;
		            val rp = HOLset.addList(rp,d_list);
                            val rp = HOLset.difference (rp, wp);
			in
			    (d_list,rp)
			end
                     else
			let
                            val rp = HOLset.difference (rp, wp);
			    val d_list = append (HOLset.listItems wp) (HOLset.listItems rp);
			in
			    (d_list, rp)
			end;
        val d = listLib.mk_list(d_list,Type `:smallfoot_var`);
	val rp_term = pred_setSyntax.prim_mk_set (HOLset.listItems rp, Type `:smallfoot_var`);
	val wp_term = pred_setSyntax.prim_mk_set (HOLset.listItems wp, Type `:smallfoot_var`);
        val wp_rp_pair_term = pairLib.mk_pair (wp_term, rp_term);
    in
        list_mk_comb (smallfoot_prop_input_ap_distinct_term, [wp_rp_pair_term, d, Pterm])
    end;


fun prune_funcall_args_el prune_vset NONE = (NONE:term option)
  | prune_funcall_args_el prune_vset (SOME v) = 
    if (HOLset.member (prune_vset,v)) then 
       NONE
    else
       SOME v;


fun prune_funcall_args prune_vset (name:string, argL) =
    (name, map (prune_funcall_args_el prune_vset) argL);




fun funcall_subsume_args ([]:term option list) [] = true
  | funcall_subsume_args [] (arg2::argL2) = false
  | funcall_subsume_args (arg1::argL1) [] = false
  | funcall_subsume_args (arg1::argL1) (arg2::argL2) = 
    ((arg2 = NONE) orelse (arg1 = arg2)) andalso 
    (funcall_subsume_args argL1 argL2);


fun funcall_subsume (name1,argL1) (name2,argL2) =
    ((name1:string)=name2) andalso (funcall_subsume_args argL1 argL2);

fun funcalls_prune prune_vset done_funcalls funcalls =
let
   val funcalls2 = map (prune_funcall_args prune_vset) funcalls;
   val funcalls3 = filter (fn fc => (not (exists (funcall_subsume fc) done_funcalls))) funcalls2
in
   funcalls3
end;




(*
val	(funname:string, 
         (ref_args, write_var_set, read_var_set, local_var_set,
	 (funname2,funArgs2)::funcalls, done_funcalls), rest) =
(el 3 fun_decl_parse_read_writeL);

val envL = fun_decl_parse_read_writeL;
*)

fun fun_decl_parse_read_write___subst_fun ((ref_arg:term, ref_argOpt),
    (write_var_set, read_var_set, funcalls)) =
let
   val in_write_set = HOLset.member (write_var_set, ref_arg);
   val write_var_set1 = if in_write_set then
			    HOLset.delete (write_var_set, ref_arg)
			else write_var_set;
   val write_var_set2 = if isSome ref_argOpt then
			    HOLset.add (write_var_set1, valOf ref_argOpt)
			else write_var_set1;


   val in_read_set = HOLset.member (read_var_set, ref_arg);
   val read_var_set1 = if in_read_set then
			    HOLset.delete (read_var_set, ref_arg)
			else read_var_set;
   val read_var_set2 = if isSome ref_argOpt then
			    HOLset.add (read_var_set1, valOf ref_argOpt)
			else read_var_set1;

   

   fun funcalls_arg_update NONE = NONE
     | funcalls_arg_update (SOME arg) =
       if (arg = ref_arg) then ref_argOpt else SOME arg;

   val funcalls2 = map (fn (n:string, L) => (n, map funcalls_arg_update L)) funcalls;
in
   (write_var_set2, read_var_set2, funcalls2)
end;




fun fun_decl_parse_read_write___step_fun 
	(funname:string, 
         (ref_args, write_var_set, read_var_set, local_var_set,
	 (funname2,funArgs2)::funcalls, done_funcalls), rest) envL =
let
  val (_, (ref_args', write_var_set', read_var_set', _,
       funcalls', _),_) = first (fn (n, _,_) => (n = funname2)) envL
      handle HOL_ERR e =>
	     (print "fun_decl_parse_read_write___step_fun: Unknown function '";print funname2;print "' detected!\n";Raise (HOL_ERR e))

  val (write_var_set2, read_var_set2, funcalls2) =
     foldl fun_decl_parse_read_write___subst_fun (write_var_set', read_var_set', funcalls')
        (zip (map string2smallfoot_var ref_args') funArgs2)


  val write_var_set3 = let
	        val set1 =  HOLset.union (write_var_set, write_var_set2);
                val set2 = HOLset.difference (set1, local_var_set);
                in set2 end;
  val read_var_set3 = let
	        val set1 =  HOLset.union (read_var_set, read_var_set2);
                val set2 = HOLset.difference (set1, write_var_set);
                val set3 = HOLset.difference (set2, local_var_set);
                in set3 end;


  val done_funcalls3 = (funname2,funArgs2)::done_funcalls;
  val funcalls3 = funcalls_prune local_var_set done_funcalls3 (append funcalls funcalls2);
in
  (funname, 
   (ref_args, write_var_set3, read_var_set3, local_var_set,
    funcalls3, done_funcalls3), rest)
end |
 fun_decl_parse_read_write___step_fun _ _ = Raise (smallfoot_unsupported_feature_exn ("-"));

 

fun fun_decl_parse_read_write___has_unresolved_funcalls 
    (funname, 
         (ref_args, write_var_set, read_var_set, local_var_set,
	 funcalls, done_funcalls), rest) =
    not(funcalls = []);



fun fun_decl_update_read_write [] solvedL = rev solvedL
  | fun_decl_update_read_write (h::L) solvedL =
    if not (fun_decl_parse_read_write___has_unresolved_funcalls h) then
       fun_decl_update_read_write L (h::solvedL)
    else
       let
	  val h' = fun_decl_parse_read_write___step_fun h
			(append solvedL (h::L))
       in
          fun_decl_update_read_write (h'::L) solvedL
       end;




(*
	
val v = "var_name";
val n = 33;
val expr = Pexp_num 3;
val expr1 = Pexp_num 1;
val expr2 = Pexp_num 2;
val tag = "tag";
val cond = Pexp_infix("<", Pexp_num 2, Pexp_ident v)

val stm1 = Pstm_new v;
val stm2 = Pstm_dispose (Pexp_ident v);

val stmL = [Pstm_fldlookup (v, expr, tag), Pstm_assign (v, expr), Pstm_new v]

val name = "proc_name";
val rp = ["x", "y", "z"];
val vp = [expr1, expr2];

val envL = fun_decl_parse_read_writeL2;
val funname = "cas"

val write_var_set = write_var_set'
*)


fun smallfoot_fcall_get_read_write_var_sets envL funname args =
let
  val (_, (ref_args', write_var_set', read_var_set', _,
       funcalls', _),_) = first (fn (n, _,_) => ((n:string) = funname)) envL;

  val (write_var_set2, read_var_set2, _) =
     foldl fun_decl_parse_read_write___subst_fun (write_var_set', read_var_set', funcalls')
        (zip (map string2smallfoot_var ref_args') args)
in
  (read_var_set2, write_var_set2)
end handle HOL_ERR _ => (empty_tmset, empty_tmset);




fun smallfoot_fcall2term_internal funL (name, (rp,vp)) =
let
   val name_term = stringLib.fromMLstring name;

   val var_list = map string2smallfoot_var rp;
   val rp_term = listLib.mk_list (var_list, Type `:smallfoot_var`);

   val (exp_list, exp_varset_list) = unzip (map smallfoot_p_expression2term vp);
   val vp_term = listLib.mk_list (exp_list, Type `:smallfoot_p_expression`)
		
   val arg_term = pairLib.mk_pair (rp_term, vp_term);
   val arg_varset = HOLset.addList (foldr HOLset.union empty_tmset exp_varset_list,
						 var_list);

   val (read_var_set0,write_var_set) = smallfoot_fcall_get_read_write_var_sets funL name (map SOME var_list);
   val read_var_set = HOLset.union (arg_varset, read_var_set0);
   val funcalls = [(name, map SOME var_list)];
in
   (name_term, arg_term, read_var_set, write_var_set, funcalls)
end;



fun smallfoot_fcall2term funL (name, (rp, vp)) =
let
   val (name_term, arg_term, read_var_set, write_var_set, funcalls) =
       smallfoot_fcall2term_internal funL (name, (rp,vp));
in
   (list_mk_comb(smallfoot_prog_procedure_call_term, [name_term, arg_term]),
    read_var_set, write_var_set, funcalls)
end;


(*
val t =
 Pstm_parallel_fcall("proc",
                                            ([], [Pexp_ident "x", Pexp_num 4]),
                                            "proc",
                                            ([],
                                             [Pexp_ident "z", Pexp_num 5]));

fun dest_Pstm_parallel_fcall (Pstm_parallel_fcall(name1,(rp1,vp1),name2,(rp2,vp2))) =
(name1,(rp1,vp1),name2,(rp2,vp2));

val (name1,(rp1,vp1),name2,(rp2,vp2)) = dest_Pstm_parallel_fcall t;

*)

fun smallfoot_parallel_fcall2term funL (name1, (rp1, vp1), name2, (rp2,vp2)) =
let
   val (name_term1, arg_term1, read_var_set1, write_var_set1, funcalls1) =
       smallfoot_fcall2term_internal funL (name1, (rp1,vp1));
   val (name_term2, arg_term2, read_var_set2, write_var_set2, funcalls2) =
       smallfoot_fcall2term_internal funL (name2, (rp2,vp2));

   val read_var_set = HOLset.union (read_var_set1, read_var_set2)
   val write_var_set = HOLset.union (write_var_set1, write_var_set2)
   val funcalls = append funcalls1 funcalls2;
in
   (list_mk_comb(smallfoot_prog_parallel_procedure_call_term, [name_term1, arg_term1,name_term2, arg_term2]),
		 read_var_set, write_var_set, funcalls)
end;




(*returns the term, the set of read variables and a set of written variables*)
fun smallfoot_p_statement2term resL funL (Pstm_assign (v, expr)) =
    let
        val var_term = string2smallfoot_var v;
        val (exp_term, read_var_set) = smallfoot_p_expression2term expr;
        val comb_term = list_mk_comb (smallfoot_prog_assign_term, [var_term, exp_term]);
	val write_var_set = HOLset.add (empty_tmset, var_term);
    in
        (comb_term, read_var_set, write_var_set, [])
    end
| smallfoot_p_statement2term resL funL (Pstm_fldlookup (v, expr, tag)) =
    let
        val var_term = string2smallfoot_var v;
        val (exp_term, read_var_set) = smallfoot_p_expression2term expr;
        val comb_term = list_mk_comb (smallfoot_prog_field_lookup_term, [var_term, exp_term, string2smallfoot_tag tag]);
	val write_var_set = HOLset.add (empty_tmset, var_term);
    in
        (comb_term, read_var_set, write_var_set, [])
    end
| smallfoot_p_statement2term resL funL (Pstm_fldassign (expr1, tag, expr2)) =
    let
        val (exp_term1, read_var_set1) = smallfoot_p_expression2term expr1;
        val (exp_term2, read_var_set2) = smallfoot_p_expression2term expr2;
        val comb_term = list_mk_comb (smallfoot_prog_field_assign_term, [exp_term1, string2smallfoot_tag tag, exp_term2]);
	val read_var_set = HOLset.union (read_var_set1, read_var_set2);
	val write_var_set = empty_tmset;
    in
        (comb_term, read_var_set, write_var_set, [])
    end
| smallfoot_p_statement2term resL funL (Pstm_new v) =
    let
        val var_term = string2smallfoot_var v;
        val comb_term = mk_comb (smallfoot_prog_new_term, var_term);
	val write_var_set = HOLset.add (empty_tmset, var_term);
        val read_var_set = empty_tmset;
    in
        (comb_term, read_var_set, write_var_set, [])
    end  
| smallfoot_p_statement2term resL funL (Pstm_dispose expr) =
    let
        val (exp_term, read_var_set) = smallfoot_p_expression2term expr;
        val comb_term = mk_comb (smallfoot_prog_dispose_term, exp_term);
	val write_var_set = empty_tmset;
    in
        (comb_term, read_var_set, write_var_set, [])
    end  
| smallfoot_p_statement2term resL funL (Pstm_block stmL) =
	let
		val (termL, read_var_setL, write_var_setL,funcallsL) = unzip4 (map (smallfoot_p_statement2term resL funL) stmL);		
		val list_term = listLib.mk_list (termL, Type `:smallfoot_prog`);
		val comb_term = mk_comb (smallfoot_prog_block_term, list_term);
                val read_var_set = foldr HOLset.union empty_tmset read_var_setL;
                val write_var_set = foldr HOLset.union empty_tmset write_var_setL;
                val funcalls = flatten funcallsL;
	in
           (comb_term, read_var_set, write_var_set,funcalls)
        end
| smallfoot_p_statement2term resL funL (Pstm_if (cond, stm1, stm2)) =
	let
		val (c_term, c_read_var_set) = smallfoot_p_expression2term cond;
		val (stm1_term,read_var_set1,write_var_set1,funcalls1) = smallfoot_p_statement2term resL funL stm1;
		val (stm2_term,read_var_set2,write_var_set2,funcalls2) = smallfoot_p_statement2term resL funL stm2;
		val comb_term = list_mk_comb (smallfoot_prog_cond_term, [c_term, stm1_term, stm2_term]);
                val read_var_set = HOLset.union (c_read_var_set, HOLset.union (read_var_set1, read_var_set2));
		val write_var_set = HOLset.union (write_var_set1, write_var_set2);
	in
           (comb_term, read_var_set, write_var_set, append funcalls1 funcalls2)
        end

| smallfoot_p_statement2term resL funL (Pstm_while (i, cond, stm1)) =
	let
		val (i_opt,i_read_var_set) = 
		       if isSome i then
			  let
		            val (prop_term, prop_varset) = smallfoot_a_proposition2term (valOf i);
		          in
			    (SOME prop_term, prop_varset)
                          end
		       else (NONE, empty_tmset);

		val (stm1_term, stm_read_var_set, stm_write_var_set, funcalls) = smallfoot_p_statement2term resL funL stm1;
		val (c_term, c_read_var_set) = smallfoot_p_expression2term cond;
                val read_var_set = HOLset.union (c_read_var_set, HOLset.union (i_read_var_set, stm_read_var_set));
		val write_var_set = stm_write_var_set;


		val op_term = if (isSome i_opt) then
				  let
				      val prop_term = mk_smallfoot_prop_input write_var_set read_var_set NONE (valOf i_opt);
				  in
                                      mk_comb (smallfoot_prog_while_with_invariant_term, prop_term)
				  end
			      else smallfoot_prog_while_term;
                val comb_term = list_mk_comb (op_term, [c_term, stm1_term]); 
	in
           (comb_term, read_var_set, write_var_set, funcalls)
        end
| smallfoot_p_statement2term resL funL (Pstm_withres (res, cond, stm1)) =
	let
		val (c_term, c_read_var_set) = smallfoot_p_expression2term cond;
		val (stm1_term,read_var_set1,write_var_set1, funcalls1) = smallfoot_p_statement2term resL funL stm1;
                val res_term = stringLib.fromMLstring res;
                val res_decl_opt = List.find (fn (a, _) => (a = res)) resL;
                val _ = if isSome (res_decl_opt) then () else raise 
                    Raise (smallfoot_unsupported_feature_exn (
                        "Undefined resource '"^res^"'!"));
                val (_, (_,res_var_set))  = valOf res_decl_opt


		val comb_term = list_mk_comb (smallfoot_prog_with_resource_term, [res_term, c_term, stm1_term]);
                val read_var_set = HOLset.difference (HOLset.union (c_read_var_set, read_var_set1), res_var_set);
		val write_var_set = HOLset.difference (write_var_set1, res_var_set);
                val funcalls = map (prune_funcall_args res_var_set) funcalls1;
	in
           (comb_term, read_var_set, write_var_set, funcalls)
        end
| smallfoot_p_statement2term resL funL (Pstm_fcall(name,args)) =
       smallfoot_fcall2term funL (name, args)
| smallfoot_p_statement2term resL funL (Pstm_parallel_fcall(name1,args1,name2,args2)) =
       smallfoot_parallel_fcall2term funL (name1, args1, name2, args2);



(*
val dummy_fundecl =
Pfundecl("proc", ([], ["x", "y"]),
                       SOME(Aprop_spred(Aspred_pointsto(Aexp_ident "x", []))),
                       [],
                       [Pstm_fldassign(Pexp_ident "x", "tl", Pexp_ident "y")],
                       SOME(Aprop_spred(Aspred_pointsto(Aexp_ident "x",
                                                        [("tl",
                                                          Aexp_ident "y")]))))


fun destPfundecl (Pfundecl(funname, (ref_args, val_args), preCond, localV, 
	fun_body, postCond)) =
	(funname, (ref_args, val_args), preCond, localV, 
	fun_body, postCond);

val (funname, (ref_args, val_args), preCondOpt, localV, 
	fun_body, postCondOpt) = destPfundecl dummy_fundecl;

val var = "y";
val term = fun_body_term; 
*)





fun mk_el_list n v = 
List.tabulate (n, (fn n => list_mk_icomb (listLib.el_tm, [numLib.term_of_int n, v])))

fun mk_dest_pair_list 0 v = [v]
  | mk_dest_pair_list n v =
    (pairLib.mk_fst v) :: mk_dest_pair_list (n-1) (pairLib.mk_snd v);




fun list_variant l [] = [] |
      list_variant l (v::vL) =
	let
		val v' = variant l v;
	in
		v'::(list_variant (v'::l) vL)
	end;



(*
   fun dest_Presource (Presource(resname, varL, invariant)) =
        (resname, varL, invariant);


   val (resname, varL, invariant) = dest_Presource ((el 2 (program_item_decl)));

*)


fun Presource2hol (Presource(resname, varL, invariant)) =
let
   val write_varL = map string2smallfoot_var varL;
   val write_var_set = HOLset.addList (empty_tmset, write_varL);
   val (i_term, i_read_var_set) = smallfoot_a_proposition2term invariant;
   val _ = if HOLset.isSubset (i_read_var_set, write_var_set) then () else
              Raise (smallfoot_unsupported_feature_exn (
                "All variables used in an resource invariant must be bound to the resource!"));
in
   (resname, (i_term, write_var_set))
end |
 Presource2hol _ = Raise (smallfoot_unsupported_feature_exn ("-"));




(*
   fun dest_Pfundecl (Pfundecl(funname, (ref_args, val_args), preCondOpt, localV, 
	fun_body, postCondOpt)) = (funname, (ref_args, val_args), preCondOpt, localV, 
	fun_body, postCondOpt);


   val (funname, (ref_args, val_args), preCondOpt, localV, 
	fun_body, postCondOpt) = dest_Pfundecl ((el 1 (program_item_decl)));

   val resL = resource_parseL
*)


fun Pfundecl2hol funL resL (Pfundecl(funname, (ref_args, val_args), preCondOpt, localV, 
	fun_body, postCondOpt)) = 
let
	val (fun_body_term, read_var_set_body, write_var_set_body, funcalls) = smallfoot_p_statement2term resL funL (Pstm_block fun_body)
        val (preCond, read_var_set_preCond, postCond, read_var_set_postCond) = 
            if not (funname = "init") then
               let
         	  val (preCond, read_var_set_preCond) = if isSome preCondOpt then smallfoot_a_proposition2term (valOf preCondOpt) else (smallfoot_ap_stack_true_term,empty_tmset);
        	  val (postCond, read_var_set_postCond) = if isSome postCondOpt then smallfoot_a_proposition2term (valOf postCondOpt) else (smallfoot_ap_stack_true_term, empty_tmset);
               in
                  (preCond, read_var_set_preCond, postCond, read_var_set_postCond)
               end
            else
               let
                  val _ = if isSome preCondOpt orelse isSome postCondOpt orelse
			     not (ref_args = []) orelse
			     not (val_args = []) then
                             raise smallfoot_unsupported_feature_exn ("init function must not have parameters or pre- / postconditions") else ();                   
         	  val (preCond, read_var_set_preCond) = (smallfoot_ap_stack_true_term,empty_tmset);
                  val postCondL = listLib.mk_list (map (fn (a,(b,c)) => b) resL, Type `:smallfoot_a_proposition`);
                  val postCond = mk_comb (smallfoot_ap_bigstar_list_term, postCondL);
		  val read_var_set_postCond = foldr HOLset.union empty_tmset (map (fn (a,(b,c)) => c) resL)
               in
                  (preCond, read_var_set_preCond, postCond, read_var_set_postCond)                  
               end;

        val localV_set = HOLset.addList (empty_tmset, map string2smallfoot_var (append localV val_args));

        val write_var_set = HOLset.difference (write_var_set_body, localV_set);
        val read_var_set = let
	        val set1 =  HOLset.union (read_var_set_preCond, HOLset.union (read_var_set_postCond, read_var_set_body));
                val set2 = HOLset.difference (set1, write_var_set);
                val set3 = HOLset.difference (set2, localV_set);
                in set3 end;
        val done_funcalls = [(funname, map (fn s => (SOME (string2smallfoot_var s))) ref_args)] 
        val funcalls2 = funcalls_prune localV_set done_funcalls funcalls;
in
  (funname, (ref_args, write_var_set, read_var_set, localV_set,
		  funcalls2, done_funcalls),
		  (fun_body_term, val_args, localV, preCond, postCond))
end |
 Pfundecl2hol _ _ _ = Raise (smallfoot_unsupported_feature_exn ("-"));







(*

val (funname, (ref_args, write_var_set, read_var_set, local_var_set,
		  funcalls, done_funcalls),
		  (fun_body_term, val_args, localV, preCond, postCond)) = 
 hd fun_decl_parse_read_writeL3;
*)

fun type2smallfoot_data_TYPE t =
   if (t = numLib.num) then ``smallfoot_data_num_TYPE`` else 
   if (t = listSyntax.mk_list_type numLib.num) then ``smallfoot_data_num_list_TYPE`` else 
   (print "Unknown Type Used!";raise (smallfoot_unsupported_feature_exn ("Unknown Type Used!")));


fun smallfoot_data_var___add_GET (v,t) =
   if (type_of v = numLib.num) then 
      (v, mk_comb (``smallfoot_data_GET_num``, t)) else
   if (type_of v = listSyntax.mk_list_type numLib.num) then 
      (v, mk_comb (``smallfoot_data_GET_num_list``, t)) else
   (print "Unknown Type Used!";raise (smallfoot_unsupported_feature_exn ("Unknown Type Used!")));




fun smallfoot_free_var2smallfoot_data_TYPE_tuple v =
let
   val var_name = (fst o dest_var) v;
   val var_name_term = stringLib.fromMLstring var_name;

   val var_type = type_of v;
   val var_type_term = type2smallfoot_data_TYPE var_type;
in
   pairLib.mk_pair(var_type_term, var_name_term)
end;




fun Pfundecl2hol_final (funname, (ref_args, write_var_set, read_var_set, local_var_set,
		  funcalls, done_funcalls),
		  (fun_body_term, val_args, localV, preCond, postCond)) = 
   let
	val fun_body_local_var_term = foldr smallfoot_mk_local_var fun_body_term localV;

	val used_vars = ref (free_vars fun_body_local_var_term);
        fun mk_new_var x = let
	                      val v = variant (!used_vars) (mk_var x);
		              val _ = used_vars := v::(!used_vars);
		           in v end;
	val arg_ref_term = mk_new_var ("arg_refL", Type `:smallfoot_var list`);
	val arg_val_term = mk_new_var ("arg_valL", Type `:num list`);
	val arg_term = pairLib.mk_pair (arg_ref_term, arg_val_term);
	val arg_valL = mk_el_list (length val_args) arg_val_term;

	val fun_body_val_args_term = foldr smallfoot_mk_val_arg fun_body_local_var_term (zip val_args arg_valL);

	val arg_refL = mk_el_list (length ref_args) arg_ref_term;
	val arg_ref_varL = map string2smallfoot_var ref_args;
	val arg_ref_subst = map (fn (vt, s) => (vt |-> s)) (zip arg_ref_varL arg_refL)
	val fun_body_final_term = subst arg_ref_subst fun_body_val_args_term;
	val fun_term = pairLib.mk_pabs (pairLib.mk_pair(arg_ref_term, arg_val_term), fun_body_final_term);

	val arg_val_varL = map (fn s => mk_comb (smallfoot_ae_var_term, string2smallfoot_var s)) val_args;
	val arg_val_expL = map (fn c => mk_comb (smallfoot_ae_const_term, c)) arg_valL;
	val arg_val_subst = map (fn (vt, s) => (vt |-> s)) (zip arg_val_varL arg_val_expL);



	val preCond2 = mk_smallfoot_prop_input write_var_set read_var_set (SOME arg_ref_varL) preCond;
	val postCond2 = mk_smallfoot_prop_input write_var_set read_var_set (SOME arg_ref_varL) postCond;

	val preCond3 = subst (append arg_val_subst arg_ref_subst) preCond2;
	val postCond3 = subst (append arg_val_subst arg_ref_subst) postCond2;


	val cond_free_var_list = 
	       let
	          val set1 = HOLset.addList(empty_tmset, free_vars preCond3);
	          val set2 = HOLset.addList(set1, free_vars postCond3);
		  val set3 = HOLset.delete (set2, arg_ref_term) handle HOLset.NotFound => set2;
		  val set4 = HOLset.delete (set3, arg_val_term) handle HOLset.NotFound => set3;
	       in
		  HOLset.listItems set4
               end;
	
        val free_var_names_list_term = listLib.mk_list (map smallfoot_free_var2smallfoot_data_TYPE_tuple cond_free_var_list, 
                                       pairLib.mk_prod (``:smallfoot_data_type``, stringLib.string_ty));
	val free_vars_term = mk_new_var ("fvL", listLib.mk_list_type ``:smallfoot_data``);
        val free_vars_subst_terms = mk_el_list (length cond_free_var_list) free_vars_term;
	val free_vars_subst = map (fn (vt, s) => (vt |-> s)) 
                                  (map smallfoot_data_var___add_GET
				  (zip cond_free_var_list free_vars_subst_terms));
	val preCond4 = subst free_vars_subst preCond3;
	val postCond4 = subst free_vars_subst postCond3;

	    

	val preCond5 = pairLib.mk_pabs (free_vars_term, preCond4);
	val postCond5 = pairLib.mk_pabs (free_vars_term, postCond4);

	val preCond6 = pairLib.mk_pabs (arg_term, preCond5);
	val postCond6 = pairLib.mk_pabs (arg_term, postCond5);

	val ref_arg_names = listLib.mk_list (map stringLib.fromMLstring ref_args, stringLib.string_ty);
        val val_args_const = map (fn s => s ^ "_const") val_args;
	val val_arg_names = listLib.mk_list (map stringLib.fromMLstring val_args_const, stringLib.string_ty);

	val wrapped_preCond = list_mk_icomb (smallfoot_input_preserve_names_wrapper_term,
		[ref_arg_names, val_arg_names,
		 free_var_names_list_term,
		 preCond6]);
in
	(funname, fun_term, wrapped_preCond, postCond6)
end



fun p_item___is_fun_decl (Pfundecl _) = true |
     p_item___is_fun_decl _ = false;


fun p_item___is_resource (Presource _) = true |
     p_item___is_resource _ = false;

(*
val examplesDir = concat [Globals.HOLDIR, "/examples/separationLogic/src/smallfoot/EXAMPLES/"]

val file = concat [examplesDir, "dummy.sf"]; 

val prog2 = parse file
val t = parse_smallfoot_file file
fun dest_Pprogram (Pprogram (ident_decl, program_item_decl)) = 
	(ident_decl, program_item_decl);

val (ident_decl, program_item_decl) = dest_Pprogram prog2;
*)



fun Pprogram2term (Pprogram (ident_decl, program_item_decl)) =
	let
		(*ignore ident_decl*)

		val resource_list = filter p_item___is_resource program_item_decl;
		val resource_parseL = map Presource2hol resource_list;
                val resource_parse_termL =
                    map (fn (name, (prop, vars)) =>
                            let
				val name_term = stringLib.fromMLstring name;
				val varL = listLib.mk_list (HOLset.listItems vars, Type `:smallfoot_var`);
                            in
                               pairLib.mk_pair(name_term, pairLib.mk_pair(varL, prop))
                            end) resource_parseL
                val resource_parseL_term = listLib.mk_list (resource_parse_termL,
							    Type `:string # smallfoot_var list # smallfoot_a_proposition`);


		val fun_decl_list = filter p_item___is_fun_decl program_item_decl;
		(*parse without knowledge about the functions read- write requirements*)
		val fun_decl_parse_read_writeL = map (Pfundecl2hol [] resource_parseL) fun_decl_list
		(*calculate the functions read- write requirements*)
                val fun_decl_parse_read_writeL2 = fun_decl_update_read_write fun_decl_parse_read_writeL [];

		(*parse again*)
		val fun_decl_parse_read_writeL3 = map (Pfundecl2hol fun_decl_parse_read_writeL2 resource_parseL) fun_decl_list

 
		val fun_decl_parseL = map Pfundecl2hol_final fun_decl_parse_read_writeL3;


		fun mk_pair_terms (s, fun_body, pre, post) =
			pairLib.list_mk_pair [stringLib.fromMLstring s, fun_body, pre, post];
		val fun_decl_parse_pairL = map mk_pair_terms fun_decl_parseL;
		val input = listLib.mk_list (fun_decl_parse_pairL, type_of (hd fun_decl_parse_pairL));

	in
		list_mk_icomb (SMALLFOOT_SPECIFICATION_term, [resource_parseL_term, input])
	end;




val parse_smallfoot_file = Pprogram2term o parse;




end
