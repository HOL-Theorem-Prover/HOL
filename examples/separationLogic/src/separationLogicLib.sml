structure separationLogicLib :> separationLogicLib =
struct

(*
quietdec := true;
loadPath := 
            (Globals.HOLDIR ^ "/examples/separationLogic/src") :: 
            (Globals.HOLDIR ^ "/examples/separationLogic/src/holfoot") :: 
            !loadPath;
show_assums := true;
*)

open HolKernel Parse boolLib bossLib;
open listTheory rich_listTheory
open separationLogicTheory;
open separationLogicSyntax
open vars_as_resourceTheory
open quantHeuristicsLib
open quantHeuristicsArgsLib
open ConseqConv
open Profile

(*
quietdec := false;
*)


(*Aplies functional equality (FUN_EQ_THM
 |- (f = g) <=> !x. f x = g x) to
 replace allquantified variables in 
 equations with lambda abstractions.
 For example
  
val t = ``!a b c. f a b c = g a b c``
 
 is converted to

``f = (\a b c. g a b c)``

 This conversion can be used to preprocess
 rewrite rules, allowing the rewriter to 
 use these rules, even if not all parameters are
 present, yet.*)

fun GSYM_FUN_EQ_CONV t =
let
   val (vars, b_term) = strip_forall t;
   val (l_term,r_term) = dest_eq b_term;
   val (l_f, l_args) = strip_comb l_term;
   fun split_vars [] acc = ([], acc)
     | split_vars (t::ts) acc =
       if op_mem eq t vars then
	   split_vars ts (t::acc) 
       else
	   (rev (t::ts), acc)
   val (rest_args, elim_args) = split_vars (rev l_args) [];
   val _ = if (null elim_args) then raise UNCHANGED else ();
   val rest_vars = filter (fn v => not (op_mem eq v elim_args)) vars;

   val l_term' = list_mk_comb (l_f, rest_args);
   val r_term' = list_mk_abs (elim_args, r_term);
   val b_term' = mk_eq (l_term', r_term');
   val t' = list_mk_forall (rest_vars, b_term');

   val thm_term = mk_eq (t,t');
   val thm = prove (thm_term, SIMP_TAC std_ss [FUN_EQ_THM] THEN
			      EQ_TAC THEN SIMP_TAC std_ss [])
in
   thm
end



(*Given a theorem of the form |- l = r it returns a theorem
  r |- l. If r is T, then |- l is returned *)
fun EQ_ELIM thm = 
   let
      val (l,r) = dest_eq (concl thm);
   in
      if (same_const r T) then EQT_ELIM thm else
         EQ_MP (GSYM thm) (ASSUME r)
   end

(*Applies a conversion to the rhs of an equational theorem*)
fun RHS_CONV_RULE conv thm = 
((CONV_RULE (RHS_CONV conv)) thm) handle UNCHANGED => thm;

(*Applies a conversion to the antecedent of an implication*)
val ANTE_CONV = (RATOR_CONV o RAND_CONV);
fun ANTE_CONV_RULE conv thm = ((CONV_RULE o ANTE_CONV) conv) thm
 handle UNCHANGED => thm;



(***************************************************************
 * PROGRAM ABSTRACTION
 *
 * The following functions are intended to abstract programs.
 * A typical one of these functions has the following signature
 *
 * abst_function sys xenv penv prog
 *
 * given a program prog, this functions tries to find an abstration
 * prog' and return a theorem of the form
 *
 * |- FASL_PROGRAM_IS_ABSTRACTION xenv penv prog prog'
 *
 * The parameter sys is a call to the system to ask it to abstract 
 * subprograms. It has the signature sys xenv penv prog.
 * Calls to system never may fail, i.e. no useful abstraction can be found.
 * In this case NONE is returned. Notice that 
 * prove_FASL_PROGRAM_ABSTRACTION_REFL may be used to produce
 * |- FASL_PROGRAM_IS_ABSTRACTION xenv penv prog prog.
 *
 * If abst_function can not find an abstraction it should return NONE,
 * throw an UNCHANGED exception or an HOL_ERR exception.
 *
 * There are abst_functions for the most common program constructs.
 * Instantions of the framework might need to provide additional ones.
 * These abstraction functions are combined by
 * search_FASL_PROGRAM_ABSTRACTION fL abstL xenv penv prog
 *
 * - fL 
 *     a list of abst_functions
 * - abstL 
 *     a list of already know abstraction, i.e. theorems of the form 
 *     something? |- FASL_PROGRAM_IS_ABSTRACTION xnev penv prog1 prog2
 ****************************************************************)
 

fun prove_FASL_PROGRAM_ABSTRACTION_REFL xenv penv p =
    (ISPECL [xenv,penv,p] FASL_PROGRAM_IS_ABSTRACTION___REFL);


type simple_fasl_program_abstraction =  term -> term -> term -> thm option;
type fasl_program_abstraction =  (term -> term) -> thm list -> simple_fasl_program_abstraction -> simple_fasl_program_abstraction;


local 
(*
  fun check_thm_opt xenv penv p NONE = NONE
    | check_thm_opt xenv penv p (SOME thm) = 
      let
          val (xenv', penv', p', _) = dest_FASL_PROGRAM_IS_ABSTRACTION (concl thm);
      in
          if (xenv = xenv') andalso
             (penv = penv') andalso (p = p') then SOME thm else 
          let
             val ps = (term_to_string p);
             val xenvs = term_to_string xenv;
             val penvs = term_to_string penv;
             val thms = thm_to_string thm; 
             val s = "Abstraction of "^ps^
                     " in ("^xenvs^","^penvs^") resulted in "^
                     thms^"!";
             val _ = print s;
          in
             NONE
          end
      end;
*)
  fun check_thm_opt xenv penv p thm_opt = thm_opt

  fun search_FASL_PROGRAM_ABSTRACTION_int (pf:term->term) true fL orgfL cref abstL xenv penv p =
       let
          val p_thm_opt_opt = Redblackmap.peek (!cref, p);
          val thm_opt = 
             if (isSome p_thm_opt_opt) then (
               (valOf p_thm_opt_opt)
             ) else (
               let
                  val thm1_opt = search_FASL_PROGRAM_ABSTRACTION_int pf false fL orgfL cref abstL xenv penv p;
                  val nc = Redblackmap.insert (!cref, p, thm1_opt)
                  val _ = cref := nc
               in
                  thm1_opt
               end
             )                                 
       in
           check_thm_opt xenv penv p thm_opt 
       end      
     | search_FASL_PROGRAM_ABSTRACTION_int pf false [] orgfL cref abstL xenv penv p = NONE     
     | search_FASL_PROGRAM_ABSTRACTION_int pf false (f1::fL) orgfL cref abstL xenv penv p =
       let
          val sys = search_FASL_PROGRAM_ABSTRACTION_int pf true orgfL orgfL cref abstL; 
          val thm1_opt = ((f1 pf abstL sys xenv penv p)
                            handle HOL_ERR _ => NONE)
                            handle UNCHANGED => NONE;           
       in
          if not (isSome thm1_opt) then
             search_FASL_PROGRAM_ABSTRACTION_int pf false fL orgfL cref abstL xenv penv p
          else
             check_thm_opt xenv penv p thm1_opt          
       end;
in
  fun search_FASL_PROGRAM_ABSTRACTION pf (fL:fasl_program_abstraction list) abstL (xenv:term) (penv:term) =
    let
       val cref = ref (Redblackmap.mkDict (Term.compare))
       val abstL' = (flatten (map BODY_CONJUNCTS abstL));
       val sys = search_FASL_PROGRAM_ABSTRACTION_int pf true fL fL cref abstL' xenv penv;

       fun search p = 
          let
             val thm_opt = sys p;    
          in
             if not (isSome thm_opt) then NONE else
             let
                val thm1 = valOf thm_opt;
                val (_,_,_,p') = dest_FASL_PROGRAM_IS_ABSTRACTION (concl thm1);
                val thm2_opt = search p';
             in
                if not(isSome thm2_opt) then thm_opt else
                SOME (MATCH_MP (MATCH_MP 
                       FASL_PROGRAM_IS_ABSTRACTION___TRANSITIVE thm1)
                       (valOf thm2_opt))
             end
          end
    in
       search 
    end
end;



(*
val thmL = BODY_CONJUNCTS (ASSUME proc_abst_t)
val t = ``fasl_prog_procedure_call "merge" ([],[]):holfoot_program``
*)

fun FASL_PROGRAM_ABSTRACTION___match thmL sys xenv penv t = 
  let
     val part = list_mk_icomb (FASL_PROGRAM_IS_ABSTRACTION_term, [xenv, penv, t]);
  in
     (tryfind (fn thm => SOME (PART_MATCH rator thm part)) thmL) 
        handle HOL_ERR _ => raise UNCHANGED
  end;

(*
fun FASL_PROGRAM_ABSTRACTION___match thmL sys xenv penv t = 
  let
     fun check_thm thm = 
         let
            val (xenv', penv', p, p') = dest_FASL_PROGRAM_IS_ABSTRACTION t;
            val m = match_term p t;
            val _ = if (aconv xenv xenv') then () else fail();
            val _ = if (aconv penv penv') then () else fail();
         in
            INST_TY_TERM m thm
         end;
  in
     (tryfind check_thm thmL) 
        handle HOL_ERR _ => raise UNCHANGED
  end;
*)


(* 
fun sys xenv penv t = NONE:thm option;
val xenv = ``xenv :'a bin_option_function # ('b -> 'a -> bool)``
val penv = ``penv :'c |-> ('d -> ('d, 'b, 'c, 'a) fasl_program)``
val p = ``(fasl_prog_block (p1::pL)):('d, 'b, 'c, 'a) fasl_program``
*)

fun FASL_PROGRAM_ABSTRACTION___block pf abstL sys xenv penv p =
   let      
      (*destruct block*)
      val bodyL = dest_fasl_prog_block p;
      val (h,restBodyL) = listSyntax.dest_cons bodyL handle HOL_ERR _ => raise UNCHANGED;
  
      (*Abstract parts*)
      val thm_h_opt = sys xenv penv h;
      val rest = mk_fasl_prog_block restBodyL;
      val thm_rest_opt = sys xenv penv rest;

      (*Has something been achived? If not abort*)
      val _ = if (not (isSome thm_h_opt) andalso not (isSome thm_rest_opt)) then raise UNCHANGED else ();

      (*create dummy abstractions if needed*)
      val thm_h = if (isSome thm_h_opt) then valOf thm_h_opt else 
          prove_FASL_PROGRAM_ABSTRACTION_REFL xenv penv h;
      val thm_rest = if (isSome thm_rest_opt) then valOf thm_rest_opt else 
          prove_FASL_PROGRAM_ABSTRACTION_REFL xenv penv rest;

      (*make sure the second abstraction is again a block, 
        if necessary create one*)
      val (_, _, _, p1) = dest_FASL_PROGRAM_IS_ABSTRACTION (concl thm_h);
      val (_, _, _, p2) = dest_FASL_PROGRAM_IS_ABSTRACTION (concl thm_rest);

      val (thm_rest', pL) = if (is_fasl_prog_block p2) then (thm_rest, dest_fasl_prog_block p2) else
                            let
                               val pL = listSyntax.mk_list ([p2], type_of p2);
                               val thm_rest' = ONCE_REWRITE_RULE [GSYM FASL_PROGRAM_IS_ABSTRACTION___block_intro] thm_rest; 
		            in
                               (thm_rest', pL)
                            end;

      (* instantiate everything*)
      val thm = ISPECL [xenv, penv, h, restBodyL,p1,pL] FASL_PROGRAM_IS_ABSTRACTION___block; 
      val thm1 = MP thm thm_h
      val thm2 = MP thm1 thm_rest'
   in
      SOME thm2
   end;


(* 
fun sys xenv penv t = NONE:thm option;
val xenv = ``xenv :'a bin_option_function # ('b -> 'a -> bool)``
val penv = ``penv :'c |-> ('d -> ('d, 'b, 'c, 'a) fasl_program)``
val p = ``(fasl_prog_block (p1::(fasl_prog_block L)::p3::L')):('d, 'b, 'c, 'a) fasl_program``
*)

val append_thm_comment_nil1 = prove (``
   (fasl_comment_location c []) ++ h::hs =
   (fasl_comment_location c (h:'a))::hs``, REWRITE_TAC[fasl_comment_location_def, APPEND])
fun is_comment_nil t =
   listSyntax.is_nil (#3 (dest_fasl_comment t)) handle HOL_ERR _ => false

val append_thm_nil1 = CONJUNCT1 APPEND
val append_thm_nil2 = CONJUNCT1 APPEND_NIL
val append_thm_cons = CONJUNCT2 APPEND

fun list_append_norm_CONV tt =
let
   val (l1,l2) = listSyntax.dest_append tt;
in
   if ((listSyntax.is_append l1) orelse (listSyntax.is_append l2)) then 
      (((RATOR_CONV o RAND_CONV) list_append_norm_CONV)  THENC
       ((RAND_CONV) list_append_norm_CONV) THENC
       list_append_norm_CONV) tt
   else if (listSyntax.is_nil l1) then 
      ISPEC l2 append_thm_nil1
   else if (listSyntax.is_nil l2) then 
      ISPEC l1 append_thm_nil2
   else if (is_comment_nil l1) then 
      REWR_CONV append_thm_comment_nil1 tt
   else let
        val (h, l1') = listSyntax.dest_cons l1;
        val thm0 = ISPECL [l1', l2, h] append_thm_cons
        val thm1 = CONV_RULE (RHS_CONV (RAND_CONV list_append_norm_CONV)) thm0
     in
        thm1
     end
end handle HOL_ERR _ => raise UNCHANGED;



fun FASL_PROGRAM_ABSTRACTION___block_flatten pf abstL sys xenv penv p =
   let      
      (* destruct input *)
      val bodyL = dest_fasl_prog_block p;
      val (body_termL,body_term_rest) = listSyntax.strip_cons bodyL handle HOL_ERR _ => raise UNCHANGED;
      val body_term_type = listSyntax.dest_list_type (type_of body_term_rest)

      (* find another block *)
      val pos = index is_fasl_prog_block body_termL 
                   handle HOL_ERR _ => raise UNCHANGED;

      (* split into the list before and after the found block *)
      val L1_termL = List.take (body_termL,pos)
      val L1_term = listSyntax.mk_list (L1_termL, body_term_type);

      val L23_termL = List.drop (body_termL,pos);
      val L2_term = dest_fasl_prog_block (hd L23_termL);

      val L3_termL = tl L23_termL;
      val L3_term = itlist (curry listSyntax.mk_cons) L3_termL body_term_rest;

      (*instantiate the corresponding theorem *)
      val thm0 = ISPECL [xenv, penv, L1_term, L2_term, L3_term] FASL_PROGRAM_IS_ABSTRACTION___block_flatten;

      (*However, this theorem contains append, it needs to be normalised*)
      val (_,_,orgL, newL) = dest_FASL_PROGRAM_IS_ABSTRACTION (concl thm0);

      val orgL_thm =  (RAND_CONV list_append_norm_CONV) orgL;
      val newL_thm =  (RAND_CONV list_append_norm_CONV) newL;

      val thm1 = CONV_RULE 
                   (((RATOR_CONV o RAND_CONV) (K orgL_thm)) THENC
                    (RAND_CONV (K newL_thm))) thm0
   in
      SOME thm1
   end;


val FASL_PROGRAM_ABSTRACTION___block_flatten___no_rec =
   FASL_PROGRAM_ABSTRACTION___block_flatten I [] (fn x => NONE)

(* 
fun sys xenv penv t = NONE:thm option;
val xenv = ``xenv :'a bin_option_function # ('b -> 'a -> bool)``
val penv = ``penv :'c |-> ('d -> ('d, 'b, 'c, 'a) fasl_program)``
val p = ``(fasl_prog_cond c p1 p2):('d, 'b, 'c, 'a) fasl_program``
*)
fun FASL_PROGRAM_ABSTRACTION___cond pf abstL sys xenv penv p =
   let      
      (*destruct*)
      val (c,p1,p2) = dest_fasl_prog_cond p;

      (*search abstractions*)
      val p1_thm_opt = sys xenv penv p1;
      val p2_thm_opt = sys xenv penv p2;
      
      (*found something?*)
      val _ = if (not (isSome p1_thm_opt) andalso not (isSome p2_thm_opt)) then raise UNCHANGED else ();
      val p1_thm = if (isSome p1_thm_opt) then valOf p1_thm_opt else 
          prove_FASL_PROGRAM_ABSTRACTION_REFL xenv penv p1;
      val p2_thm = if (isSome p2_thm_opt) then valOf p2_thm_opt else 
          prove_FASL_PROGRAM_ABSTRACTION_REFL xenv penv p2;


      (*prove the final theorem*)
      val (_,_,_,p1') = dest_FASL_PROGRAM_IS_ABSTRACTION (concl p1_thm);
      val (_,_,_,p2') = dest_FASL_PROGRAM_IS_ABSTRACTION (concl p2_thm);

      val thm = ISPECL [xenv, penv, c, p1,p1',p2,p2'] FASL_PROGRAM_IS_ABSTRACTION___cond; 
      val thm1 = MP thm p1_thm
      val thm2 = MP thm1 p2_thm
   in
      SOME thm2
   end;


(* 
fun sys xenv penv t = SOME (prove_FASL_PROGRAM_ABSTRACTION_REFL xenv penv t)
fun sys xenv penv t = NONE:thm option;
val xenv = ``xenv :'a bin_option_function # ('b -> 'a -> bool)``
val penv = ``penv :'c |-> ('d -> ('d, 'b, 'c, 'a) fasl_program)``
val p = ``(fasl_prog_while c p):('d, 'b, 'c, 'a) fasl_program``
*)
fun FASL_PROGRAM_ABSTRACTION___while pf abstL sys xenv penv p =
   let      
      val (c,p) = dest_fasl_prog_while p;

      (*search abstraction*)
      val p_thm_opt = sys xenv penv p;
      val p_thm = if (isSome p_thm_opt) then valOf p_thm_opt else raise UNCHANGED;
      val (_,_,_,p') = dest_FASL_PROGRAM_IS_ABSTRACTION (concl p_thm);

      val thm = ISPECL [xenv, penv, c, p,p'] FASL_PROGRAM_IS_ABSTRACTION___while; 
      val thm1 = MP thm p_thm;
   in
      SOME thm1
   end;

fun FASL_PROGRAM_ABSTRACTION___comment pf abstL sys xenv penv p =
   let      
      val (_, c, p', def_thm) = dest_fasl_comment p;

      (*search abstraction*)
      val p_thm_opt = sys xenv penv p';
      val p_thm = if (isSome p_thm_opt) then valOf p_thm_opt else raise UNCHANGED;

      val (_,_,_,p'') = dest_FASL_PROGRAM_IS_ABSTRACTION (concl p_thm);
      val thm_p' = ISPECL [c, p'] def_thm
      val thm_p'' = ISPECL [c, p''] def_thm

      val thm0 = CONV_RULE ((RAND_CONV) (K (GSYM thm_p''))) p_thm
      val thm1 = CONV_RULE ((RATOR_CONV o RAND_CONV) (K (GSYM thm_p'))) thm0
   in
      SOME thm1
   end;


val basic_fasl_program_abstractions = [
    FASL_PROGRAM_ABSTRACTION___block_flatten,
    FASL_PROGRAM_ABSTRACTION___block,
    FASL_PROGRAM_ABSTRACTION___cond,
    FASL_PROGRAM_ABSTRACTION___comment,
    FASL_PROGRAM_ABSTRACTION___while]:fasl_program_abstraction list;


(*

val fL = append basic_fasl_program_abstractions [
   FASL_PROGRAM_ABSTRACTION___local_var,
   FASL_PROGRAM_ABSTRACTION___call_by_value_arg,
   FASL_PROGRAM_ABSTRACTION___eval_expressions]

val t = rand (snd (strip_forall (el 1 (strip_conj specs_t))))
val abstL = [ASSUME proc_abst_t]

*)

fun FASL_PROGRAM_HOARE_TRIPLE___ABSTRACTION___CONSEQ_CONV fL abstL t =   
   let
     val _ = if (is_FASL_PROGRAM_HOARE_TRIPLE t) then () else raise UNCHANGED;
     val (xenv, penv, pre, body, post) = dest_FASL_PROGRAM_HOARE_TRIPLE t;

     val thm_opt =  search_FASL_PROGRAM_ABSTRACTION I fL abstL xenv penv body;
     val thm = if (isSome thm_opt) then valOf thm_opt else raise UNCHANGED;

     val thm2 = ISPECL [xenv, penv, pre, body, post] FASL_PROGRAM_HOARE_TRIPLE_ABSTRACTION___INTRO;
     val thm3 = MATCH_MP thm2 thm;
   in
     thm3
   end;


(*
   val t = ``FASL_PROGRAM_IS_ABSTRACTION xenv penv p1 p2``

   val SOME (fL, abstL, t) = !t_opt

*)

fun FASL_PROGRAM_IS_ABSTRACTION___ABSTRACTION___CONSEQ_CONV fL abstL t =   
   let
     val (xenv, penv, p1, p3) = dest_FASL_PROGRAM_IS_ABSTRACTION t handle HOL_ERR _ => raise UNCHANGED

     val print_fun =
     let
         val (a1, a2, _, x) = dest_fasl_procedure_call_preserve_names_wrapper
              (find_term is_fasl_procedure_call_preserve_names_wrapper p3)
         val (x1,x2) = pairSyntax.dest_pair x;
         fun mk_list_term x a =
           let
               val ty = listSyntax.dest_list_type (type_of x)
               val sL = map (fst o dest_var) (fst (listSyntax.dest_list a))
               val vL = map (fn s => mk_var (s, ty)) sL;
           in
               listSyntax.mk_list (vL, ty)
           end;
         val l1 = mk_list_term x1 a1;
         val l2 = mk_list_term x2 a2
         val su = subst [x1 |-> l1, x2 |-> l2]                   
     in
         fn p1 => (rhs (concl (SIMP_CONV list_ss [] (su p1)))) handle UNCHANGED => su p1
     end handle UNCHANGED => I
              | HOL_ERR _ => I

     val thm_opt =  search_FASL_PROGRAM_ABSTRACTION print_fun fL abstL xenv penv p1;
     val thm = if (isSome thm_opt) then valOf thm_opt else raise UNCHANGED;

     val (_, _, _, p2) = dest_FASL_PROGRAM_IS_ABSTRACTION (concl thm);

     val thm2 = ISPECL [xenv, penv, p1, p2, p3] FASL_PROGRAM_IS_ABSTRACTION___TRANSITIVE;
     val thm3 = MP thm2 thm;
   in
     thm3
   end;





(***************************************************************
 * HANDLE SPECIFICATIONS
 *
 * Elininate function calls
 ****************************************************************)


val names_all_distinct_cs = computeLib.bool_compset ();
val _ = computeLib.add_thms [listTheory.MAP, pairTheory.FST, pairTheory.SND,
                             listTheory.ALL_DISTINCT,
                             listTheory.MEM] names_all_distinct_cs;
val _ = computeLib.add_conv (``($=):'a -> 'a -> bool``, 2, stringLib.string_EQ_CONV) names_all_distinct_cs;



val proc_free_specs_cs = computeLib.bool_compset ();
val _ = computeLib.add_thms [listTheory.EVERY_DEF, pairTheory.SND, pairTheory.FST,
    REWRITE_RULE [fasl_prog_IS_RESOURCE_AND_PROCCALL_FREE___ALTERNATIVE_DEF] fasl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prim_command,
    REWRITE_RULE [fasl_prog_IS_RESOURCE_AND_PROCCALL_FREE___ALTERNATIVE_DEF] fasl_prog_IS_RESOURCE_AND_PROCCALL_FREE___SIMPLE_REWRITES] proc_free_specs_cs;
val _ = computeLib.add_conv (pairSyntax.uncurry_tm, 2, pairLib.GEN_BETA_CONV) proc_free_specs_cs;



(*
fun proc_call_free_CONV t = REWRITE_CONV [
   REWRITE_RULE [fasl_prog_IS_RESOURCE_AND_PROCCALL_FREE___ALTERNATIVE_DEF]
      fasl_prog_IS_RESOURCE_AND_PROCCALL_FREE___var_res_bla] t;

val prog_rewrites = [var_res_prog_procedure_call_THM]

val abstrL = append basic_fasl_program_abstractions [
   FASL_PROGRAM_ABSTRACTION___local_var,
   FASL_PROGRAM_ABSTRACTION___call_by_value_arg,
   FASL_PROGRAM_ABSTRACTION___eval_expressions]

   val thm_strengthen_specs = 
      DEPTH_CONSEQ_CONV (FASL_PROGRAM_IS_ABSTRACTION___ABSTRACTION___CONSEQ_CONV abstrL [ASSUME proc_abst_t])
                        specs_t

val t = ``fasl_comment_location_string "XXX" YYY``
*)
fun fasl_comment_location_string_ELIM_CONV t =
let
   val (c, p) = dest_fasl_comment_location_string t
   val c_label = mk_var(stringLib.fromHOLstring c, markerSyntax.label_ty)
   val c_list = listSyntax.mk_list ([c_label], markerSyntax.label_ty)

   val thm1 = ISPECL [c,p] fasl_comment_location_string_def
   val thm2 = GSYM (ISPECL [c_list, p] fasl_comment_location_def)
in
   TRANS thm1 thm2
end;


val precond1_cs = computeLib.bool_compset ();
val _ = computeLib.add_thms [listTheory.EVERY_DEF,
    pairTheory.FST, pairTheory.SND] precond1_cs;
val _ = computeLib.add_conv (pairSyntax.uncurry_tm, 2, pairLib.GEN_BETA_CONV) precond1_cs;
val _ = computeLib.add_conv (fasl_comment_location_string_term, 2, fasl_comment_location_string_ELIM_CONV) precond1_cs;


val precond1_conv = 
   (QUANT_INSTANTIATE_CONV [pair_default_qp]) THENC
   DEPTH_CONV (pairLib.GEN_BETA_CONV)



fun FASL_SPECIFICATION___CONSEQ_CONV (proc_call_free_CONV, abstrL) t =
let
   (* apply SPECIFICATION INFERENCE *)
   fun apply_inference_rule t =
      let
         val (f_term, res_decls_term, p_specs_term) = dest_FASL_SPECIFICATION t;
         val thm1 = ISPECL [f_term, res_decls_term, p_specs_term] FASL_INFERENCE___SPECIFICATION;

         val side_conds_term = fst (dest_imp (concl thm1));
         val (proc_free_specs_term, distinct_proc_names_term) = dest_conj side_conds_term;


         val proc_free_specs_thm = EQ_ELIM ((computeLib.CBV_CONV proc_free_specs_cs THENC
                                            proc_call_free_CONV) proc_free_specs_term) handle HOL_ERR _ =>
               failwith ("Could not prove that specifications are well formed!");

         val distinct_proc_names_thm = EQ_ELIM (computeLib.CBV_CONV names_all_distinct_cs distinct_proc_names_term) handle HOL_ERR _ =>
               failwith ("Could not prove that all procedure names are distinct!");

         val thm2 = MP thm1 (CONJ proc_free_specs_thm distinct_proc_names_thm);
      in
         thm2
      end;



   (*Simplify*)
   fun simplify_precond thm = 
      let
         val thm1 = CONV_RULE (RATOR_CONV (RAND_CONV (computeLib.CBV_CONV precond1_cs))) thm;
         val thm2 = CONV_RULE (RATOR_CONV (RAND_CONV (Conv.QUANT_CONV (RAND_CONV precond1_conv)))) thm1;
      in
         thm2
      end;




   (* Eliminate procedure calls, locks, etc. *)
   fun eliminate_environment thm =
   let
      val precond = fst (dest_imp (concl thm));
      val (penv_var, body) = dest_forall precond;
      val (proc_abst_t, specs_t) = dest_imp body;

      val thm_strengthen_specs = 
         DEPTH_STRENGTHEN_CONSEQ_CONV (FASL_PROGRAM_IS_ABSTRACTION___ABSTRACTION___CONSEQ_CONV abstrL [ASSUME proc_abst_t])
                           specs_t handle UNCHANGED => REFL_CONSEQ_CONV specs_t;
  

      val thm2 = let
         val precond' = fst (dest_imp (concl thm_strengthen_specs));
         val x_thm0 = ADD_ASSUM  proc_abst_t (UNDISCH thm_strengthen_specs)
         val x_thm1 = DISCH proc_abst_t x_thm0
         val x_thm2 = DISCH precond' x_thm1
         val x_thm3 = GEN_IMP penv_var x_thm2
         val precond'' = fst (dest_imp (concl x_thm3));
         val x_thm4 = UNDISCH x_thm3
         val x_thm5 = MP thm x_thm4 
         val x_thm6 = DISCH precond'' x_thm5
         in x_thm6 end;
   in
     thm2
   end;



   val current_thm = apply_inference_rule t;
   val current_thm2 = simplify_precond current_thm;
   val current_thm3 = eliminate_environment current_thm2;
in
   current_thm3
end;

    

(******************************************************************************)
(* Remove procedure_call_preserve_names_wrapper                               *)
(******************************************************************************)

(*
val tt = ``fasl_procedure_call_preserve_names_wrapper ["r"]
                         ["p_const"] c ([q],[x])``
*)

fun fasl_procedure_call_preserve_names_wrapper_ELIM_CONV tt =
let
   val thm0 = PART_MATCH (lhs o snd o dest_imp_only) 
      fasl_procedure_call_preserve_names_wrapper_ELIM tt;
   val precond = (fst o dest_imp o concl) thm0
   val precond_thm = EQT_ELIM (REWRITE_CONV [LENGTH,
       pairTheory.SND, pairTheory.FST] precond)
in
   MP thm0 precond_thm
end;

(******************************************************************************)
(* HANDLE location comments                                                   *)
(******************************************************************************)
(*
   val c = fasl_comment_modify_INC c
*)

fun get_last_num_token c =
let
   val (la, cL) = listSyntax.dest_cons c
   val s = fst (dest_var la)

   val sL = String.tokens (fn c => c = #" ") s;
   val ls = last sL;

   val n_opt = Int.fromString ls
   val (n, s') = if isSome n_opt then (valOf n_opt, String.concatWith " " (butlast sL))
                    else (0, s)
in
   (n, s', cL, isSome n_opt)
end handle HOL_ERR _ => (0, "", c, false)


fun fasl_comment_modify_NUM_OP f c =
let

   val (n, s', c', num_found) = get_last_num_token c

   val ns = Int.toString (f n)
   val s'' = s' ^ " " ^ ns;
   val l = mk_var (s'', markerSyntax.label_ty)
   val c'' = listSyntax.mk_cons (l, c')
in
   c''
end;

fun fasl_comment_modify_NUM_COPY_INIT i c =
let
   val (n, s', c', num_found) = get_last_num_token c
in
   if num_found then c else
   let
      val s'' = s' ^ " " ^ (Int.toString i);
      val l = mk_var (s'', markerSyntax.label_ty)
      val c'' = listSyntax.mk_cons (l, c')
   in
      c''
   end
end;


val fasl_comment_modify_INC =
  fasl_comment_modify_NUM_OP (fn n => n+1);

val fasl_comment_modify_COPY_INIT =
  fasl_comment_modify_NUM_COPY_INIT 1;

fun fasl_comment_modify_APPEND s c =
let
   val l = mk_var (s, markerSyntax.label_ty)
   val c' = listSyntax.mk_cons (l, c)
in
   c'   
end;


fun fasl_comment_modify_APPEND_INC s c =
let
   val (n, s', c',_) = get_last_num_token c

   val c'' = listSyntax.mk_cons (mk_var 
                (s', markerSyntax.label_ty), c')

   val ns = Int.toString (n + 1)
   val s'' = s ^ " " ^ ns;
   val c''' = listSyntax.mk_cons (mk_var 
                (s'', markerSyntax.label_ty), c'')
in
   c'''
end;


fun fasl_comment_modify_APPEND_DEC s c =
let
   val (n, s', c',_) = get_last_num_token c

   val c'' = listSyntax.mk_cons (mk_var 
                (s', markerSyntax.label_ty), c')

   val ns = Int.toString (n - 1)
   val s'' = s ^ " " ^ ns;
   val c''' = listSyntax.mk_cons (mk_var 
                (s'', markerSyntax.label_ty), c'')
in
   c'''
end;


fun fasl_comment_block_CONV conv t =
   if (not (is_fasl_prog_block t)) then conv t else
   let
      val pL = dest_fasl_prog_block t;    
      val rec_call = fasl_comment_block_CONV conv
   in
      if listSyntax.is_cons pL then
         ((RAND_CONV o RATOR_CONV o RAND_CONV) rec_call) t
      else if listSyntax.is_nil pL then
         (RAND_CONV rec_call) t
      else conv t
   end;

fun fasl_comment_location_INTRO_CONV c t =
   ISPECL [c, t] (GSYM fasl_comment_location_def)

fun fasl_comment_location_BLOCK_INTRO_CONV c =
   fasl_comment_block_CONV (fasl_comment_location_INTRO_CONV c)

fun fasl_comment_location2_INTRO_CONV c t =
   ISPECL [c, t] (GSYM fasl_comment_location2_def)

fun fasl_comment_abstraction_INTRO_CONV s t =
   let
      val l = mk_var (s, markerSyntax.label_ty);
   in
      ISPECL [l, t] (GSYM fasl_comment_abstraction_def)
   end;
         

fun fasl_comment_location_CONSEQ_RULE c thm =
let
   val _ = if is_eq (concl thm) orelse
              is_imp_only (concl thm) then () else Feedback.fail ();
in
   CONV_RULE (BINOP_CONV (fasl_comment_location_INTRO_CONV c)) thm
end;


fun fasl_comment_location_CONSEQ_CONV conv t =
let
   val (c, t') = dest_fasl_comment_location t;
   val thm0 = conv t';
in
   fasl_comment_location_CONSEQ_RULE c thm0
end;


fun fasl_comment_location___TF_ELIM___CONV t =
let
   val (c, t') = dest_fasl_comment_location t;
   val _ = if (aconv t' T) orelse (aconv t' F) then () else raise UNCHANGED;
in
   ISPECL [c, t'] fasl_comment_location_def
end;


fun CONSEQ_CONV_CONGRUENCE___location_comment context sys dir t =
  let
     val (c, body) = dest_fasl_comment_location t
     val (n1, thm0_opt) = sys [] context 0  dir body; 
     val _ = if (isSome thm0_opt) then () else raise UNCHANGED;

     val thm1 = fasl_comment_location_CONSEQ_RULE c (valOf thm0_opt)
  in
     (n1, thm1)
  end
 

(******************************************************************************)
(* Remove asl_exists_list                                                     *)
(******************************************************************************)

(*
val tt = ``asl_exists_list [aa; bb; cc] (\x s. (sdds x /\ D /\ (LENGTH x = 3)))``
val tt = ttt
val base_name = "name"
val t2s = term_to_string
val t2s = holfoot_term_to_string
*)

local
   val conv_nil = REWR_CONV (CONJUNCT1 asl_exists_list___REWRITE)
   val conv_cons = REWR_CONV (CONJUNCT2 asl_exists_list___REWRITE)
   fun asl_exists_list_CONV_int [] = 
       conv_nil THENC (TRY_CONV BETA_CONV)
     | asl_exists_list_CONV_int (n::ns) =
       conv_cons THENC (RAND_CONV (RENAME_VARS_CONV [n])) THENC
       RAND_CONV (ABS_CONV (
           (RAND_CONV (ABS_CONV (TRY_CONV BETA_CONV))) THENC
           asl_exists_list_CONV_int ns))
in

fun asl_exists_list_CONV base_name t2s tt =
let
   val (argL, P) = dest_asl_exists_list tt;
   fun t2s' t = concat [base_name, "_", t2s t]
   val namesL = map t2s' (fst (listSyntax.dest_list argL))
   val P_v = genvar (type_of P)

   val new_t = list_mk_icomb (asl_exists_list_term, [argL, P_v])
   val thm0 = asl_exists_list_CONV_int namesL new_t;
   val thm1 = INST [P_v |-> P] thm0
   val thm2 = CONV_RULE (RHS_CONV (DEPTH_CONV BETA_CONV)) thm1
in
   thm2
end;

end;

(*
fun VAR_RES_LOCATION_COMMENT_step___CONV tt =
let
   val (c, body) = dest_fasl_comment_location tt;
in
end
*)




(*
open holfootParser
open holfoot_pp_print
val examplesDir = concat [Globals.HOLDIR, "/examples/separationLogic/src/holfoot/EXAMPLES/"]
val file = concat [examplesDir, "mergesort.sf"]; 
val file = concat [examplesDir, "mergesort.dsf"]; 
val t = parse_holfoot_file file
val t = parse_holfoot_file_restrict ["mergesort"] file

temp_remove_holfoot_pp ();temp_add_holfoot_pp ();t
temp_remove_holfoot_pp ();t



open Profile
add_holfoot_pp()
reset_all ();
val thm = time (FASL_SPECIFICATION___CONSEQ_CONV (proc_call_free_CONV, abstrL)) t;
print_profile_results (results());


open Profile
reset_all ()
print_profile_results (results())
val cref = 0

*)



end
