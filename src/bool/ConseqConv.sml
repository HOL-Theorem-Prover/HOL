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

fun CONSEQ_CONV_WRAPPER conv t =
let
   val thm = conv t;
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



(*Like DEPTH_CONV for CONSEQ_CONVS. The conversion
  may generate theorems containing assumptions. These
  assumptions are propagated to the top level*)

fun DEPTH_CONSEQ_CONV conv t = 
  if (is_conj t) then
     let
	 val (b1,b2) = dest_conj t;
         val thm1 = DEPTH_CONSEQ_CONV conv b1;
         val thm2 = DEPTH_CONSEQ_CONV conv b2;
          
	 val (b1,c1) = dest_imp (concl thm1);
	 val (b2,c2) = dest_imp (concl thm2);
	 val thm3 = MATCH_MP MONO_AND (CONJ thm1 thm2);
     in
        thm3
     end handle HOL_ERR _ => (raise UNCHANGED)
   else if (is_disj t) then
     let
	 val (b1,b2) = dest_disj t;
         val thm1 = DEPTH_CONSEQ_CONV conv b1;
         val thm2 = DEPTH_CONSEQ_CONV conv b2;

	 val (b1,c1) = dest_imp (concl thm1);
	 val (b2,c2) = dest_imp (concl thm2);
	 val thm3 = MATCH_MP MONO_OR (CONJ thm1 thm2);
     in
        thm3
     end
   else if (is_forall t) then
     let
        val (var, body) = dest_forall t;
	val thm_body = DEPTH_CONSEQ_CONV conv body;
        val thm = GEN_ASSUM var thm_body;
        val thm2 = HO_MATCH_MP MONO_ALL thm;
     in
        thm2
     end
   else 
     ((let
	 val thm = (CONSEQ_CONV_WRAPPER conv) t;
         val (ante,_) = dest_imp (concl thm);
         val thm2 = DEPTH_CONSEQ_CONV conv ante;
	 val thm3 = IMP_TRANS thm2 thm;
     in
         thm3
     end handle HOL_ERR _ => REFL_IMP_CONV t)
         handle UNCHANGED => REFL_IMP_CONV t);


(*like CHANGED_CONV*)
fun CHANGED_CONSEQ_CONV conv t =
    let
       val thm = conv t;
       val (ante,conc) = dest_imp (concl thm);
       val _ = if (ante = conc) then raise UNCHANGED else ();
    in
       thm
    end;

(*like FIRST_CONV*)
fun FIRST_CONSEQ_CONV [] t = raise UNCHANGED
  | FIRST_CONSEQ_CONV ((c1:conv)::L) t =
    ((c1 t handle HOL_ERR _ => raise UNCHANGED) handle UNCHANGED =>
    FIRST_CONSEQ_CONV L t);




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
 * if conv A = (A' ==> A) then 
 * IMP_CONSEQ_CONV_RULE (A ==> B) = (A' ==> B)
 *---------------------------------------------------------------------------*)

fun IMP_CONSEQ_CONV_RULE conv thm = let
   val (imp_term,_) = dest_imp (concl thm);
   val imp_thm = conv imp_term;   
  in
   IMP_TRANS imp_thm thm
  end


(*A tactic that strengthens a boolean goal*)
fun CONSEQ_CONV_TAC conv (asm,t) = 
    HO_MATCH_MP_TAC (conv t) (asm,t);


fun DEPTH_CONSEQ_CONV_TAC conv =
    CONSEQ_CONV_TAC (DEPTH_CONSEQ_CONV conv)








end
