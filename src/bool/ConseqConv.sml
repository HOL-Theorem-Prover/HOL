(* ===================================================================== *)
(* FILE          : ConseqConv.sml                                        *)
(* DESCRIPTION   : Infrastructure for 'Consequence Conversions'.         *)
(*		   A ConseqConv is a conversion that turns a term        *)
(*		   t into a theorem of the form "t' ==> t"               *)
(*                                                                       *)
(* AUTHORS       : Thomas Tuerk                                          *)
(* DATE          : July 3, 2008                                          *)
(* ===================================================================== *)


structure ConseqConv :> ConseqConv =
struct

(*
quietdec := true;
*)

open HolKernel Parse boolLib Drule;

(*
quietdec := false;
*)





(*---------------------------------------------------------------------------
 * generalise a variable in an implication of ==>
 *
 *   A |- t1 v ==> t2 v  
 * ---------------------------------------------
 *   A |- (!v. t1 v) ==> (!v. t2 v)
 *
 *---------------------------------------------------------------------------*)

fun GEN_IMP v thm = 
  let
     val thm1 = GEN v thm;
     val thm2 = HO_MATCH_MP MONO_ALL thm1;
  in
     thm2
  end;


(*---------------------------------------------------------------------------
 * REFL for implications
 *
 * REFL_IMP_CONV t = (t ==> t)
 *---------------------------------------------------------------------------*)
fun REFL_IMP_CONV t = DISCH t (ASSUME t);


(*---------------------------------------------------------------------------
 * generalises a thm body and as well the ASSUMPTIONS
 *
 *   A |- body
 * ---------------------------------------------
 *   (!v. A) |- !v. body
 *
 *---------------------------------------------------------------------------*)

fun GEN_ASSUM v thm = 
  let
    val assums = filter (fn t => mem v (free_vars t)) (hyp thm);
    val thm2 = foldl (fn (t,thm) => DISCH t thm) thm assums; 
    val thm3 = GEN v thm2;
    val thm4 = foldl (fn (_,thm) => UNDISCH (HO_MATCH_MP MONO_ALL thm)) 
                     thm3 assums;
  in
    thm4
  end








(*---------------------------------------------------------------------------
 * A normal conversion converts a term t to a theorem of
 * the form t = t'. In contrast a CONSEQ_CONV converts it to
 * a theorem of the form t' ==> t, i.e. it tries to strengthen a boolean expression
 *---------------------------------------------------------------------------*)
 


(*---------------------------------------------------------------------------
 * Converts a conversion returning theorems of the form 
 *    t' ==> t, t = t' or t
 * to a CONSEQ_CONV. Also some checks are performed that the resulting
 * theorem is really of the form t' ==> t with t being the original input
 * and t' not being equal to t
 *---------------------------------------------------------------------------*)

fun CONSEQ_CONV_WRAPPER___CONVERT_RESULT thm t =
let
   val thm_term = concl thm;
in
   if (thm_term = t andalso not (t = T)) then
      snd (EQ_IMP_RULE (EQT_INTRO thm)) else
   if (is_imp thm_term) then
      let
	 val (t1, t2) = dest_imp thm_term;
	 val _ = if not (t2 = t) then raise UNCHANGED else ();
	 val _ = if (t1 = t2) then raise UNCHANGED else ();
      in
         thm
      end
   else if (is_eq thm_term) then
      if ((lhs thm_term = t) andalso not (rhs thm_term = t)) then
	 snd (EQ_IMP_RULE thm)
      else raise UNCHANGED
   else
      raise UNCHANGED
end;


fun CONSEQ_CONV_WRAPPER conv t =
let
   val _ = if (type_of t = bool) then () else raise UNCHANGED;
   val thm = conv t;   
in
   CONSEQ_CONV_WRAPPER___CONVERT_RESULT thm t
end;


fun CHANGED_CHECK_CONSEQ_CONV conv t =
    let
       val thm = conv t;
       val (ante,conc) = dest_imp (concl thm);
       val _ = if (ante = conc) then raise UNCHANGED else ();
    in
       thm
    end;


(*like CHANGED_CONV*)
fun QCHANGED_CONSEQ_CONV conv t =
    conv t handle UNCHANGED => raise mk_HOL_ERR "bool" "ConseqConv" "QCHANGED_CONSEQ_CONV"

fun CHANGED_CONSEQ_CONV conv =
    QCHANGED_CONSEQ_CONV (CHANGED_CHECK_CONSEQ_CONV conv)


(*like ORELSEC*)
fun ORELSE_CONSEQ_CONV (c1:conv) c2 t =     
    ((c1 t handle HOL_ERR _ => raise UNCHANGED) handle UNCHANGED =>
     (c2 t handle HOL_ERR _ => raise UNCHANGED));


(*like FIRST_CONV*)
fun FIRST_CONSEQ_CONV [] t = raise UNCHANGED
  | FIRST_CONSEQ_CONV ((c1:conv)::L) t =
    ORELSE_CONSEQ_CONV c1 (FIRST_CONSEQ_CONV L) t;




fun CONSEQ_CONV_WRAPPER___GET_ANTECEDENT thm t =
   let
      val thm1 = CONSEQ_CONV_WRAPPER___CONVERT_RESULT thm t;
      val (t', _) = dest_imp (concl thm1);
   in
      (t', SOME thm1)
   end;



(*like THENC*)
fun THEN_CONSEQ_CONV (c1:conv) c2 t =     
    let
       val thm0_opt = (SOME (c1 t) handle HOL_ERR _ => raise UNCHANGED) handle UNCHANGED => NONE;
       val ((t2, thm0_imp_opt), thm0_opt) = 
            ((if (isSome thm0_opt) then CONSEQ_CONV_WRAPPER___GET_ANTECEDENT (valOf thm0_opt) t else (t, NONE)),
	     thm0_opt) handle UNCHANGED => ((t, NONE), NONE);

       val thm1_opt = (SOME (c2 t2) handle HOL_ERR _ => raise UNCHANGED) handle UNCHANGED => NONE;
       val ((t3, thm1_imp_opt), thm1_opt) = 
            (if (isSome thm1_opt) then CONSEQ_CONV_WRAPPER___GET_ANTECEDENT (valOf thm1_opt) t2 else (t2, NONE),
	     thm1_opt) handle UNCHANGED => ((t2, NONE), NONE);
    in
       if (isSome thm0_opt) andalso (isSome thm1_opt) then
       (
         if (is_eq (concl (valOf thm0_opt))) andalso (is_eq (concl (valOf thm1_opt))) then
	     TRANS (valOf thm0_opt) (valOf thm1_opt)
         else
	     IMP_TRANS (valOf thm1_imp_opt) (valOf thm0_imp_opt)
       ) else 
       if (isSome thm0_opt) then valOf thm0_opt else
       if (isSome thm1_opt) then valOf thm1_opt else
       raise UNCHANGED
    end;




(*Like QUANT_CONV for CONSEQ_CONVS. Explicit versions
  for FORALL and EXISTS are exported, since they have
  to be handeled separately anyhow.*)

fun FORALL_CONSEQ_CONV conv t =
   let
      val (var, body) = dest_forall t;
      val thm_body = conv body;
      val thm = GEN_ASSUM var thm_body;
      val thm2 = HO_MATCH_MP MONO_ALL thm;
   in
      thm2
   end;

fun EXISTS_CONSEQ_CONV conv t =
   let
      val (var, body) = dest_exists t;
      val thm_body = conv body;
      val thm = GEN_ASSUM var thm_body;
      val thm2 = HO_MATCH_MP boolTheory.MONO_EXISTS thm;
   in
      thm2
   end;

fun QUANT_CONSEQ_CONV conv t =
    if (is_forall t) then
       FORALL_CONSEQ_CONV conv t 
    else if (is_exists t) then
       EXISTS_CONSEQ_CONV conv t 
    else
       NO_CONV t;




(*Like DEPTH_CONV for CONSEQ_CONVS. The conversion
  may generate theorems containing assumptions. These
  assumptions are propagated to the top level*)


fun step_opt_sub NONE n = NONE
  | step_opt_sub (SOME m) n = SOME (m - n);


fun DEPTH_CONSEQ_CONV_num step_opt conv t = 
  if (step_opt = SOME 0) then
     (0, REFL_IMP_CONV t)
  else if (is_conj t) then
     let
	 val (b1,b2) = dest_conj t;
         val (n1, thm1) = DEPTH_CONSEQ_CONV_num step_opt conv b1;
         val (n2, thm2) = DEPTH_CONSEQ_CONV_num (step_opt_sub step_opt n1) conv b2;
          
	 val (b1,c1) = dest_imp (concl thm1);
	 val (b2,c2) = dest_imp (concl thm2);
	 val thm3 = MATCH_MP MONO_AND (CONJ thm1 thm2);
     in
        (n1+n2, thm3)
     end handle HOL_ERR _ => (raise UNCHANGED)
   else if (is_disj t) then
     let
	 val (b1,b2) = dest_disj t;
         val (n1, thm1) = DEPTH_CONSEQ_CONV_num step_opt conv b1;
         val (n2, thm2) = DEPTH_CONSEQ_CONV_num (step_opt_sub step_opt n1) conv b2;

	 val (b1,c1) = dest_imp (concl thm1);
	 val (b2,c2) = dest_imp (concl thm2);
	 val thm3 = MATCH_MP MONO_OR (CONJ thm1 thm2);
     in
        (n1+n2, thm3)
     end
   else if (is_imp t) then
     let
	 val (b1,b2) = dest_imp t;
	 val thm1 = REFL_IMP_CONV b1;
         val (n2, thm2) = DEPTH_CONSEQ_CONV_num step_opt conv b2;

	 val (b2,c2) = dest_imp (concl thm2);
	 val thm3 = MATCH_MP MONO_IMP (CONJ thm1 thm2);
     in
        (n2, thm3)
     end
   else if (is_forall t) then
     let
        val (var, body) = dest_forall t;
	val (n1, thm_body) = DEPTH_CONSEQ_CONV_num step_opt conv body;
        val thm = GEN_ASSUM var thm_body;
        val thm2 = HO_MATCH_MP MONO_ALL thm;
     in
        (n1, thm2)
     end
   else if (is_exists t) then
     let
        val (var, body) = dest_exists t;
	val (n1, thm_body) = DEPTH_CONSEQ_CONV_num step_opt conv body;
        val thm = GEN_ASSUM var thm_body;
        val thm2 = HO_MATCH_MP boolTheory.MONO_EXISTS thm;
     in
        (n1, thm2)
     end
   else 
     ((let
	 val thm = (CONSEQ_CONV_WRAPPER conv) t;
         val (ante,_) = dest_imp (concl thm);
 	 val (n2, thm2) = DEPTH_CONSEQ_CONV_num (step_opt_sub step_opt 1) conv ante;
	 val thm3 = IMP_TRANS thm2 thm;
     in
         (n2 + 1, thm3)
     end handle HOL_ERR _ => (0, REFL_IMP_CONV t))
         handle UNCHANGED => (0, REFL_IMP_CONV t));




fun DEPTH_CONSEQ_CONV conv  = 
 CHANGED_CHECK_CONSEQ_CONV (fn t => 
   if (type_of t = bool) then 
      (snd (DEPTH_CONSEQ_CONV_num NONE conv t))
   else raise UNCHANGED)


fun NUM_DEPTH_CONSEQ_CONV n conv = 
   CHANGED_CHECK_CONSEQ_CONV (fn t => 
     if (type_of t = bool) then 
       (snd (DEPTH_CONSEQ_CONV_num (SOME n) conv t))
     else raise UNCHANGED)

val ONCE_DEPTH_CONSEQ_CONV = NUM_DEPTH_CONSEQ_CONV 1;



(*---------------------------------------------------------------------------
 * Takes the assumptions returned by a STRENGTEN_CONV,
 * tries to simplify them recursively with the same CONSEQ_CONV and
 * add the results to the assumptions. Assumptions in preserve_hyps are 
 * not simplified. 
 *---------------------------------------------------------------------------*)

fun CONJ_ASSUMPTIONS_CONSEQ_CONV conv preserve_hyp_pred t =
let
    val thm = conv t;
    val new_hyps = filter (fn t => not (preserve_hyp_pred t)) (hyp thm);
    val hyp_thms = map (fn t => 
                       ((SOME (CONJ_ASSUMPTIONS_CONSEQ_CONV conv preserve_hyp_pred t))
		        handle HOL_ERR _ => NONE) 
                        handle UNCHANGED => NONE) new_hyps;

    val hyp_thms2 = filter (fn thm_opt => (isSome thm_opt andalso
					   let val (l,r) = dest_imp (concl (valOf thm_opt)) in (not (l = r)) end handle HOL_ERR _ => false)) hyp_thms; 
    val hyp_thms3 = map (UNDISCH o valOf) hyp_thms2; 

    val thm2 = foldr (fn (thm1,thm2) => PROVE_HYP thm1 thm2) thm hyp_thms3;


    val new_hyps2 = filter (fn t => not (preserve_hyp_pred t)) (hyp thm2);
    val thm3 = foldr (fn (t,thm) => SUBST_MATCH (SPEC_ALL AND_IMP_INTRO) (DISCH t thm)) thm2 (new_hyps2);
    val thm4 = CONV_RULE (RATOR_CONV (REWRITE_CONV [])) thm3
in
    thm4
end;


fun CONJ_ASSUMPTIONS_DEPTH_CONSEQ_CONV conv =
    CONJ_ASSUMPTIONS_CONSEQ_CONV (DEPTH_CONSEQ_CONV conv) (K false)


(*---------------------------------------------------------------------------
 * if conv ``A`` = |- (A' ==> A) then 
 * IMP_CONSEQ_CONV_RULE ``(A ==> B)`` = |- (A' ==> B)
 *---------------------------------------------------------------------------*)

fun IMP_CONSEQ_CONV_RULE conv thm = let
   val (imp_term,_) = dest_imp (concl thm);
   val imp_thm = conv imp_term;   
  in
   IMP_TRANS imp_thm thm
  end


(*A tactic that strengthens a boolean goal*)
fun CONSEQ_CONV_TAC conv (asm,t) = 
    HO_MATCH_MP_TAC ((CHANGED_CONSEQ_CONV conv) t) (asm,t) handle UNCHANGED =>
    raise mk_HOL_ERR "ConseqConv" "CONSEQ_CONV_TAC" "UNCHANGED";


fun DEPTH_CONSEQ_CONV_TAC conv =
    CONSEQ_CONV_TAC (DEPTH_CONSEQ_CONV conv)


fun ONCE_DEPTH_CONSEQ_CONV_TAC conv =
    CONSEQ_CONV_TAC (ONCE_DEPTH_CONSEQ_CONV conv)








end
