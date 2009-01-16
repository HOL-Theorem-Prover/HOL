structure ctl2muTools =
struct

local

open Globals HolKernel Parse

open boolSyntax pairSyntax pairTools PairRules bossLib muTheory
     muCheck ctlTheory ctl2muTheory Tactical Tactic Drule Rewrite
     cearTheory ksTheory setLemmasTheory pred_setTheory boolTheory
     Conv PrimitiveBddRules ksTools lazyTools lzPairRules muSyntax
     commonTools

(*fun mk_bool_var v = mk_var(v,``:bool``);
fun mk_primed_bool_var v = mk_bool_var (v^"'");
fun term_to_string2 t = with_flag (show_types,false) term_to_string t;
*)
val dpfx = "c2m_"

in

(* normalise ctl formula to only use constructors from the minimal set *)
fun ctl_norm_CONV f = Rewrite.REWRITE_CONV [C_IMP2_def,B_IMP2_def,B_AND2_def,B_OR2_def,C_AND2_def,C_OR2_def,C_AX_def,C_AG_def,C_AU_def,C_EF_def,C_IMP_def,C_IFF_def,C_AF_def,B_IMP_def,B_IFF_def,C_OR_def,B_OR_def] f handle ex => (REFL f);

local
fun ctl2mu_aux  f (cons as (mu_t,mu_f,mu_ap,mu_rv,mu_neg,mu_conj,mu_disj,mu_dmd,mu_box,mu_mu,mu_nu)) =
  let
      val (opr,args) = HolKernel.strip_comb f;
      val (name,ty) = dest_const opr;
  in case name of
         "B_PROP" => mu_ap(List.hd args) (* ``AP ^(List.hd args)``*)
       | "B_NOT"  => mu_neg(ctl2mu_aux (List.hd args) cons) (* ``~^(ctl2mu_aux prop_type (List.hd args))``*)
       | "B_AND"  => let val (f1,f2) = pairSyntax.dest_pair (List.hd args)
                     in mu_conj (ctl2mu_aux f1 cons) (ctl2mu_aux f2 cons) end
       (*``^(ctl2mu_aux prop_type f1) /\ ^(ctl2mu_aux prop_type f2)`` *)
       | "B_OR"  => let val (f1,f2) = pairSyntax.dest_pair (List.hd args)
                     in mu_disj (ctl2mu_aux f1 cons) (ctl2mu_aux f2 cons) end
       (*``^(ctl2mu_aux prop_type f1) \/ ^(ctl2mu_aux prop_type f2)`` *)
       | "B_TRUE" => mu_t
       | "B_FALSE" => mu_neg(mu_t) (* as this is how B_FALSE is represented syntactically *)
       | "C_BOOL" => ctl2mu_aux (List.hd args) cons
       | "C_NOT"  => mu_neg(ctl2mu_aux (List.hd args) cons)
       | "C_AND"  => let val (f1,f2) = pairSyntax.dest_pair (List.hd args)
                     in mu_conj (ctl2mu_aux f1 cons) (ctl2mu_aux f2 cons) end
       | "C_OR"  => let val (f1,f2) = pairSyntax.dest_pair (List.hd args)
                     in mu_disj (ctl2mu_aux f1 cons) (ctl2mu_aux f2 cons) end
       | "C_EX"   => mu_dmd dotacn  (ctl2mu_aux (List.hd args) cons) (*``<<".">> ^(ctl2mu_aux prop_type (List.hd args))``*)
       (*| "O_AX"   => ``[["."]] ^(ctl2mu_aux prop_type (List.hd args))``*)
       | "C_EU"   => let val (f1,f2) = pairSyntax.dest_pair (List.hd args)
                     in mu_mu concRV (mu_disj (ctl2mu_aux f2 cons) (mu_conj (ctl2mu_aux f1 cons) (mu_dmd dotacn (mu_rv concRV))))  end
       (*``mu "Q" .. ^(ctl2mu_aux prop_type f2) \/ (^(ctl2mu_aux prop_type f1)  /\ (<<".">> (RV "Q")))``*)
       | "C_EG"   => mu_nu concRV (mu_conj (ctl2mu_aux (List.hd args) cons) (mu_dmd dotacn (mu_rv concRV)))
       (*  ``nu "Q" .. ^(ctl2mu_aux prop_type (List.hd args)) /\ (<<".">> (RV "Q"))``*)
       | _ => (print name; Raise Match)
  end
in
fun ctl2mu f =
    let val f' = rhs(concl (ctl_norm_CONV f))
    in ctl2mu_aux f' (get_ty_cons (get_prop_type f)) end

end

val _ = set_trace "notify type variable guesses" 0;
val ctl2mu_tm = ``ctl2mu$CTL2MU``
val _ = set_trace "notify type variable guesses" 1;

(* convert ctl formula to mu formula *)
fun ctl2mu_CONV f =
    let val jf = (fn _ => REWRITE_CONV [CTL2MU_def,BEXP2MU_def,C_IMP2_def,B_IMP2_def,B_AND2_def,B_OR2_def,C_AND2_def,C_OR2_def,C_AX_def,
					C_AG_def,C_AU_def,C_EF_def,C_IMP_def,C_IFF_def,C_AF_def,B_IMP_def,B_IFF_def,C_OR_def,B_OR_def,
					B_FALSE_def] (mk_comb(inst [alpha|->get_prop_type f] ctl2mu_tm,f)))
    in mk_lthm (fn _ => (mk_eq(mk_comb(inst [alpha|->get_prop_type f] ctl2mu_tm,f),ctl2mu f),jf)) jf end


(* convert ctl model to mu model *)
fun ctl2muks_CONV Ithm Rthm cks_def =
    let val _ = dbgTools.DEN dpfx "c2mks"(*DBG*)
	val th1 = (ISPEC (rhs(concl cks_def)) ctl2muks_def)
	val th2 = PURE_REWRITE_RULE [SYM cks_def,combinTheory.K_THM,kripke_structure_accfupds] th1
	val th3 =  CONV_RULE (RHS_CONV (T_CONV (PURE_REWRITE_CONV [SYM Rthm]))) th2
	val _ = dbgTools.DTH (dpfx^"c2mks_th3") th3 (*DBG*)
	val th4 = CONV_RULE (RHS_CONV (S0_CONV (PURE_REWRITE_CONV [SYM Ithm]))) th3
	val _ = dbgTools.DTH (dpfx^"c2mks_th4") th4 (*DBG*)
	val th5 = CONV_RULE (RHS_CONV (S0_CONV lzPETA_CONV)) th4
	val th6 = CONV_RULE (RHS_CONV (T_CONV (ABS_CONV lzPETA_CONV))) th5
	val _ = dbgTools.DEX dpfx "c2mks"(*DBG*)
    in th5 end

end
end
