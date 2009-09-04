structure boolTools :> boolTools =
struct

(*
quietdec := true;
*)

open HolKernel Parse boolLib bossLib;

(*
quietdec := false;
*)

fun dest_neg_eq t = dest_eq (dest_neg t);
val is_neg_eq = can dest_neg_eq;

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
       end) orelse
      (is_neg_eq t1 andalso is_neg_eq t2 andalso
       let
           val (t1l, t1r) = dest_neg_eq t1;
           val (t2l, t2r) = dest_neg_eq t2;
       in
          (aconv t1r t2l) andalso (aconv t1l t2r)
       end);


  fun logical_mem e [] = false
    | logical_mem e (h::l) =
      (rewrite_eq e h) orelse logical_mem e l;


  fun findMatches ([], l2) = []
    | findMatches (a::l1, l2) =
	 let val l1' = filter (fn e => not (eq e a)) l1;
             val l2' = filter (fn e => not (eq e a)) l2;
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
	      fun filter_pred t = not (op_mem eq v (free_vars t));
	  in
              (t::(filter filter_pred l1), t::(filter filter_pred l2))
          end)
      else
      ([t],[t]);





val bool_eq_imp_solve_TAC = ASM_REWRITE_TAC[] THEN
                            ASM_SIMP_TAC std_ss [] THEN
                            METIS_TAC[];

(*
fun neg_eq_ASSUME_TAC tac =
   tac THENL [
      POP_ASSUM (fn thm => ASSUME_TAC thm THEN ASSUME_TAC (GSYM thm)),
      ALL_TAC
   ];
*)


fun bool_eq_imp_case_TAC h =
      let
	  val (h', n) = strip_neg h;
          val org_cases_tac = ASM_CASES_TAC h';
          val cases_tac = if (n mod 2 = 0) then org_cases_tac else
                          Tactical.REVERSE org_cases_tac;
      in
	  cases_tac
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
      val matches_thms1 = map ASSUME matches
      val matches_thms2 = map GSYM (filter (fn thm => is_neg_eq (concl thm)) matches_thms1);
      val conc_term = rhs (concl (REWRITE_CONV (matches_thms1 @ matches_thms2) t));
      val _ = if (eq conc_term F) then raise UNCHANGED else ();

      val goal_term = if (eq conc_term T) then T else mk_imp (list_mk_conj matches, conc_term);
      val _ = if (eq t goal_term) then raise UNCHANGED else ();
      (* set_goal ([], mk_eq(t, goal_term)) *)
      val thm = prove (mk_eq(t, goal_term), bool_eq_imp_real_imp_TAC matches);
   in
      thm
   end;



fun clean_disj_matches [] acc = acc
  | clean_disj_matches (t::ts) acc =
    let
       val (disj_imp,_) = get_impl_terms t;
       val acc' = if (null (op_intersect eq disj_imp (ts@acc))) then
		     t::acc
                  else
		     acc;
    in
       clean_disj_matches ts acc'
    end;


fun clean_conj_matches [] acc = acc
  | clean_conj_matches (t::ts) acc =
    let
       val (_, conj_imp) = get_impl_terms t;
       val acc' = if (null (op_intersect eq conj_imp (ts@acc))) then
		     t::acc
                  else
		     acc;
    in
       clean_conj_matches ts acc'
    end;







fun bool_eq_imp_CONV t =
   let
      val (l,r) = dest_eq t;
      val _ = if (type_of l = bool) then () else raise mk_HOL_ERR "Conv" "bool_eq_imp_CONV" "";
      val (disj_l, conj_l) = get_impl_terms l;
      val (disj_r, conj_r) = get_impl_terms r;

      val disj_matches = clean_disj_matches (findMatches (disj_l, disj_r)) [];
      val conj_matches = clean_conj_matches (findMatches (conj_l, conj_r)) [];

      val matches = (map logical_mk_neg disj_matches) @ conj_matches;
      val _ = if null matches then raise UNCHANGED else ();
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



fun bool_imp_extract_CONV t =
   let
      val _ = if (type_of t = bool) then () else raise mk_HOL_ERR "Conv" "bool_imp_extract_CONV" "";
      val (disj_t_refl,_) = get_impl_terms t;
      val disj_t = tl disj_t_refl;
      val disj_matches = clean_disj_matches disj_t [];

      val matches = (map logical_mk_neg disj_t);
      val _ = if null matches then raise UNCHANGED else ();
   in
      bool_eq_imp_real_imp_CONV matches t
   end;




val bool_eq_imp_ss = simpLib.conv_ss {name = "bool_eq_imp_CONV",
            trace = 2,
            key = SOME ([],``(a:bool) = (b:bool)``),
            conv = K (K bool_eq_imp_CONV)};

val bool_imp_extract_ss = simpLib.conv_ss {name = "bool_imp_extract_ss",
            trace = 2,
            key = SOME ([],``a:bool``),
            conv = K (K bool_imp_extract_CONV)};

val bool_neg_pair_ss = simpLib.conv_ss {name = "bool_neg_pair_CONV",
            trace = 2,
            key = SOME ([],``a:bool``),
            conv = K (K bool_neg_pair_CONV)};






val imp_thm_conj = prove (``!b1 c1 b2 c2. (b1 ==> c1) ==>
					   (b2 ==> c2) ==>
			                   (b1 /\ b2) ==>
					   (c1 /\ c2)``, SIMP_TAC std_ss []);
val imp_thm_disj = prove (``!b1 c1 b2 c2. (b1 ==> c1) ==>
					   (b2 ==> c2) ==>
			                   (b1 \/ b2) ==>
					   (c1 \/ c2)``, SIMP_TAC std_ss [DISJ_IMP_THM]);

val imp_thm_forall = prove (``(!x. (b1 x ==> b2 x)) ==> ((!x. b1 x) ==> (!x. b2 x))``,
			      SIMP_TAC std_ss []);


fun GEN_IMP v thm =
  let
     val thm1 = GEN v thm;
     val thm2 = HO_MATCH_MP imp_thm_forall thm1;
  in
     thm2
  end;



fun REFL_IMP_CONV t = DISCH t (ASSUME t);

fun GEN_ASSUM v thm =
  let
    val assums = filter (fn t => op_mem eq v (free_vars t)) (hyp thm);
    val thm2 = foldl (fn (t,thm) => DISCH t thm) thm assums;
    val thm3 = GEN v thm2;
    val thm4 = foldl (fn (_,thm) => UNDISCH (HO_MATCH_MP MONO_ALL thm))
                     thm3 assums;
  in
    thm4
  end


fun STRENGTHEN_CONV_WRAPPER conv t =
let
   val thm = conv t;
   val thm_term = concl thm;
in
   if (is_imp thm_term) then
      let
	 val (t1, t2) = dest_imp thm_term;
	 val _ = if not (eq t2 t) then raise UNCHANGED else ();
	 val _ = if (eq t1 t2) then raise UNCHANGED else ();
      in
         thm
      end
   else if (is_eq thm_term) then
      if ((eq (lhs thm_term) t) andalso not (eq (rhs thm_term) t)) then
	 snd (EQ_IMP_RULE thm)
      else raise UNCHANGED
   else if (eq thm_term t andalso not (eq t T)) then
      snd (EQ_IMP_RULE (EQT_INTRO thm))
   else
      raise UNCHANGED
end;


fun DEPTH_STRENGTHEN_CONV conv t =
  if (is_conj t) then
     let
	 val (b1,b2) = dest_conj t;
         val thm1 = DEPTH_STRENGTHEN_CONV conv b1;
         val thm2 = DEPTH_STRENGTHEN_CONV conv b2;

	 val (b1,c1) = dest_imp (concl thm1);
	 val (b2,c2) = dest_imp (concl thm2);
         val thm3 = ISPECL [b1,c1,b2,c2] imp_thm_conj;
	 val thm4 = MP thm3 thm1;
	 val thm5 = MP thm4 thm2;
     in
        thm5
     end handle HOL_ERR _ => (raise UNCHANGED)
   else if (is_disj t) then
     let
	 val (b1,b2) = dest_disj t;
         val thm1 = DEPTH_STRENGTHEN_CONV conv b1;
         val thm2 = DEPTH_STRENGTHEN_CONV conv b2;

	 val (b1,c1) = dest_imp (concl thm1);
	 val (b2,c2) = dest_imp (concl thm2);
         val thm3 = ISPECL [b1,c1,b2,c2] imp_thm_disj;
	 val thm4 = MP thm3 thm1;
	 val thm5 = MP thm4 thm2;
     in
        thm5
     end
   else if (is_forall t) then
     let
        val (var, body) = dest_forall t;
	val thm_body = DEPTH_STRENGTHEN_CONV conv body;
        val thm = GEN_ASSUM var thm_body;
        val thm2 = HO_MATCH_MP imp_thm_forall thm;
     in
        thm2
     end
   else
     ((let
	 val thm = (STRENGTHEN_CONV_WRAPPER conv) t;
         val (ante,_) = dest_imp (concl thm);
         val thm2 = DEPTH_STRENGTHEN_CONV conv ante;
	 val thm3 = IMP_TRANS thm2 thm;
     in
         thm3
     end handle HOL_ERR _ => REFL_IMP_CONV t)
         handle UNCHANGED => REFL_IMP_CONV t);

fun UNCHANGED_STRENGTHEN_CONV conv t =
    let
       val thm = conv t;
       val (ante,conc) = dest_imp (concl thm);
       val _ = if (eq ante conc) then raise UNCHANGED else ();
    in
       thm
    end;


fun ORELSE_STRENGTHEN_CONV [] t = raise UNCHANGED
  | ORELSE_STRENGTHEN_CONV (c1::L) t =
    c1 t handle UNCHANGED =>
    ORELSE_STRENGTHEN_CONV L t;





fun CONJ_ASSUMPTIONS_STRENGTHEN_CONV conv preserve_hyps t =
let
    val thm = conv t;
    val new_hyps = filter (fn t => not (op_mem eq t preserve_hyps)) (hyp thm);
    val hyp_thms = map (fn t =>
                       ((SOME (CONJ_ASSUMPTIONS_STRENGTHEN_CONV conv preserve_hyps t))
		        handle HOL_ERR _ => NONE)
                        handle UNCHANGED => NONE) new_hyps;

    val hyp_thms2 = filter (fn thm_opt => (isSome thm_opt andalso
					   let val (l,r) = dest_imp (concl (valOf thm_opt)) in (not (eq l r)) end handle HOL_ERR _ => false)) hyp_thms;
    val hyp_thms3 = map (UNDISCH o valOf) hyp_thms2;

    val thm2 = foldr (fn (thm1,thm2) => PROVE_HYP thm1 thm2) thm hyp_thms3;


    val new_hyps2 = filter (fn t => not (op_mem eq t preserve_hyps)) (hyp thm2);
    val thm3 = foldr (fn (t,thm) => SUBST_MATCH (SPEC_ALL AND_IMP_INTRO) (DISCH t thm)) thm2 (new_hyps2);
    val thm4 = CONV_RULE (RATOR_CONV (REWRITE_CONV [])) thm3
in
    thm4
end;


fun CONJ_ASSUMPTIONS_DEPTH_STRENGTHEN_CONV conv =
    CONJ_ASSUMPTIONS_STRENGTHEN_CONV (DEPTH_STRENGTHEN_CONV conv) []


fun IMP_STRENGTHEN_CONV_RULE conv thm = let
   val (imp_term,_) = dest_imp (concl thm);
   val imp_thm = conv imp_term;
  in
   IMP_TRANS imp_thm thm
  end


fun STRENGTHEN_CONV_TAC conv (asm,t) =
    HO_MATCH_MP_TAC (conv t) (asm,t);


fun DEPTH_STRENGTHEN_CONV_TAC conv =
    STRENGTHEN_CONV_TAC (DEPTH_STRENGTHEN_CONV conv)









fun COND_REWR_CONV___with_match thm =
  if (is_imp (concl thm)) then
     if (is_eq (snd (dest_imp (concl thm)))) then
        (UNDISCH o (PART_MATCH (lhs o snd o dest_imp) thm),
	 (lhs o snd o dest_imp o concl) thm)
     else
        (EQT_INTRO o UNDISCH o (PART_MATCH (snd o dest_imp) thm),
         (snd o dest_imp o concl) thm)
  else
     if (is_eq (concl thm)) then
        (PART_MATCH lhs thm,
         (lhs o concl) thm)
     else
        (EQT_INTRO o PART_MATCH I thm,
	 concl thm)


fun COND_REWR_CONV thm =
    fst (COND_REWR_CONV___with_match thm);




fun COND_REWRITE_CONV thmL =
   let
     val thmL' = flatten (map BODY_CONJUNCTS thmL);
     val conv_termL = map COND_REWR_CONV___with_match thmL';
     val net = foldr (fn ((conv,t),net) => Net.insert (t,conv) net) Net.empty conv_termL;
   in
     REPEATC (fn t =>
        let
	  val convL = Net.match t net;
	in
          FIRST_CONV convL t
	end)
   end


fun GUARDED_COND_REWRITE_CONV p thmL =
   let
      val conv = COND_REWRITE_CONV thmL
   in
      fn t => if p t then conv t else NO_CONV t
   end


(*
fun COND_REWRITE_RULE r thm =
   let
      val rs = flatten (map (fn thm => CONJUNCTS thm) r);
      val rs = map UNDISCH_ALL rs;
      val thm' = repeat (fn thm => tryfind (fn thm2 => SUBST_MATCH thm2 thm) rs) thm
   in
      thm'
   end;


*)

end
