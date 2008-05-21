structure separationLogicLib :> separationLogicLib =
struct

(*
quietdec := true;
loadPath := 
            (concat Globals.HOLDIR "/examples/separationLogic/src") :: 
            (concat Globals.HOLDIR "/examples/separationLogic/src/smallfoot") :: 
            !loadPath;

map load ["finite_mapTheory", "relationTheory", "congLib", "sortingTheory",
   "rich_listTheory", "generalHelpersTheory", "latticeTheory", "separationLogicTheory",
   "stringTheory", "Parser", "Lexer","Lexing", "Nonstdio",
   "stringLib", "listLib"];
show_assums := true;
*)

open HolKernel Parse boolLib bossLib;

open generalHelpersTheory finite_mapTheory relationTheory pred_setTheory congLib sortingTheory
   listTheory rich_listTheory arithmeticTheory operatorTheory optionTheory latticeTheory separationLogicTheory;

(*
quietdec := false;
*)



fun logical_mk_neg t = 
    if is_neg t then dest_neg t else mk_neg t;


fun rewrite_eq t1 t2 = 
      aconv t1 t2 orelse
      (is_eq t1 andalso is_eq t2 andalso
       let
           val (t1l, t1r) = dest_eq t1;
           val (t2l, t2r) = dest_eq t2;
       in
          (aconv t1r t2l) andalso (aconv t1l t2r)
       end);


  fun logical_mem e [] = false 
    | logical_mem e (h::l) =
      (rewrite_eq e h) orelse logical_mem e l;


  fun findMatches ([], l2) = []
    | findMatches (a::l1, l2) =
	 let val l1' = filter (fn e => not (e = a)) l1;
             val l2' = filter (fn e => not (e = a)) l2;
	     val l = (findMatches (l1',l2')); in
         if logical_mem a l2 then a::l else l end;

  fun find_negation_pair [] = NONE |
      find_negation_pair (e::l) = 
      if logical_mem (logical_mk_neg e) l then SOME e else
      find_negation_pair l;


fun dest_quant t = dest_abs (snd (dest_comb t));
fun is_quant t = is_forall t orelse is_exists t orelse
		 is_exists1 t;


  (*returns a list of terms that imply the whole term and
    a list of terms that are implied

    
    (x ==> X, x <== X)
   *)    



  fun get_impl_terms t =
      if is_disj t then
	  (let val (t1,t2)=dest_disj t; 
               val (l11,l12)= get_impl_terms t1;
               val (l21,l22)= get_impl_terms t2;
	   in
              (t::(l11 @ l21), t::findMatches (l12, l22))    
           end)
      else
      if is_conj t then
	  (let val (t1,t2)=dest_conj t;
               val (l11,l12)= get_impl_terms t1;
               val (l21,l22)= get_impl_terms t2;
	   in
              (t::findMatches (l11, l21), t::(l12 @ l22))    
           end)
      else
      if is_neg t then 
	  (let val (l1,l2) = get_impl_terms (dest_neg t) in
	      (map logical_mk_neg l2, map logical_mk_neg l1)
          end)
      else
      if is_imp t then
	  (let val (t1,t2)=dest_imp t;
               val neg_t1 = logical_mk_neg t1;
               val new_t = mk_disj (neg_t1, t2) 
           in get_impl_terms new_t end)
      else
      if is_quant t then
          (let
	      val (v, b) = dest_quant t;
	      val (l1,l2) = get_impl_terms b;
	      fun filter_pred t = not (mem v (free_vars t));
	  in
              (t::(filter filter_pred l1), t::(filter filter_pred l2))
          end)
      else
      ([t],[t]);





val bool_eq_imp_solve_TAC = ASM_REWRITE_TAC[] THEN
                            ASM_SIMP_TAC std_ss [] THEN
                            METIS_TAC[];

fun neg_eq_ASSUME_TAC tac =
   tac THENL [
      ALL_TAC,  
      POP_ASSUM (fn thm => ASSUME_TAC thm THEN ASSUME_TAC (GSYM thm))
   ];


fun bool_eq_imp_case_TAC h = 
      let 
	  val (h', n) = strip_neg h;
          val org_cases_tac = ASM_CASES_TAC h';
          val cases_tac = if (n mod 2 = 0) then org_cases_tac else
                          Tactical.REVERSE org_cases_tac;
      in
	  if (is_eq h') then neg_eq_ASSUME_TAC cases_tac else cases_tac
      end;


fun bool_eq_imp_solve_CONV c t = 
   let
      val thm = prove (t, bool_eq_imp_case_TAC c THEN 
			  bool_eq_imp_solve_TAC);
   in
      EQT_INTRO thm
   end;


fun bool_eq_imp_real_imp_TAC [] = bool_eq_imp_solve_TAC
  | bool_eq_imp_real_imp_TAC (h::l) =
      bool_eq_imp_case_TAC h THENL [
          bool_eq_imp_real_imp_TAC l,
          bool_eq_imp_solve_TAC
      ];








fun bool_eq_imp_real_imp_CONV matches t =
   let
      val goal_term = mk_imp (list_mk_conj matches,
                              rhs (concl (REWRITE_CONV (map ASSUME matches) t))); 
      (* set_goal ([], mk_eq(t, goal_term)) *)
      val thm = prove (mk_eq(t, goal_term), bool_eq_imp_real_imp_TAC matches);
   in
      thm
   end;



fun bool_eq_imp_CONV t = 
   let
      val (l,r) = dest_eq t;
      val _ = if (type_of l = bool) then () else raise mk_HOL_ERR "Conv" "bool_eq_imp_CONV" "";
      val (disj_l, conj_l) = get_impl_terms l;
      val (disj_r, conj_r) = get_impl_terms r;

      val disj_matches = findMatches (disj_l, disj_r);
      val conj_matches = findMatches (conj_l, conj_r);

      val matches = (map logical_mk_neg disj_matches) @ conj_matches; 
      val _ = if matches = [] then raise UNCHANGED else ();
      val solving_case_split = find_negation_pair matches;
   in
      if isSome solving_case_split then bool_eq_imp_solve_CONV (valOf solving_case_split) t else
         bool_eq_imp_real_imp_CONV matches t
   end;



fun bool_neg_pair_CONV t = 
   let
      val _ = if (type_of t = bool) then () else raise mk_HOL_ERR "Conv" "bool_negation_pair_CONV" "";
      val (disj_t, conj_t) = get_impl_terms t;
      val solving_case_split = find_negation_pair disj_t;
      val disj = isSome solving_case_split;
      val solving_case_split = if disj then solving_case_split else
			       find_negation_pair conj_t;

      val _ = if (isSome solving_case_split) then () else raise UNCHANGED;

      val thm_term = mk_eq (t, if disj then T else F);
      val thm = prove (thm_term, bool_eq_imp_case_TAC (valOf solving_case_split) THEN 
			  bool_eq_imp_solve_TAC);
   in
      thm
   end;







val bool_eq_imp_ss = simpLib.conv_ss {name = "bool_eq_imp_CONV",
            trace = 2,
            key = SOME ([],``(a:bool) = (b:bool)``),
            conv = K (K bool_eq_imp_CONV)};


val bool_neg_pair_ss = simpLib.conv_ss {name = "bool_neg_pair_CONV",
            trace = 2,
            key = SOME ([],``a:bool``),
            conv = K (K bool_neg_pair_CONV)};



end
