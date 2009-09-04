structure decompTools = struct

local

open HolKernel Parse boolLib bossLib

(* app load ["bddTools","amba_apb_def","mod16Theory","amba_ahb_def","decompTheory","commonTools","muSyntax","muTheory","muCheck","envTheory"];*)
open boolSyntax bossLib Ho_Rewrite Tactical Tactic PairRules pairSyntax pred_setTheory
open bddTools commonTools ksTheory muSyntaxTheory muSyntax decompTheory ksTools muCheck envTheory

in

(* FIXME: this is gross right now because the REPEAT PGEN takes ages. fix it *)
(* note that s2 is not the state of ks2. That's (s1,s2)*)
fun prove_ap_ext_ap ks1_def ks2_def s1 s2 =
    let val ksname1 = lhs(concl ks1_def)
	val ksname2 = lhs(concl ks2_def)
    in
	prove(``!p. p IN (^ksname1).ap ==> ?p'. !s1 s2. p IN (^ksname1).L s1 = p' IN (^ksname2).L (s1,s2)``,
	      REPEAT STRIP_TAC
	      THEN CONV_TAC (QUANT_CONV (LAST_FORALL_CONV (GEN_PALPHA_CONV s2)))
	      THEN CONV_TAC (QUANT_CONV (GEN_PALPHA_CONV s1))
	      THEN FULL_SIMP_TAC std_ss [KS_accfupds,combinTheory.K_THM,ks1_def,ks2_def]
	      THEN SIMP_TAC std_ss [IN_DEF]
	      THEN POP_ASSUM (MP_TAC o (CONV_RULE IN_FIN_CONV))
	      THEN PURE_REWRITE_TAC [DISJ_IMP_THM]
	      THEN REPEAT CONJ_TAC
	      THEN DISCH_TAC
	      THEN POP_ASSUM (fn t => SIMP_TAC std_ss [t] THEN EXISTS_TAC (mk_pabs(mk_pair(s1,s2),pbody(rhs (concl t)))))
	      THEN PBETA_TAC
	      THEN REPEAT PGEN_TAC
	      THEN REFL_TAC)
    end

fun prove_ap_ext_ksL ks_def s =
    let val ksname =  lhs(concl ks_def)
    in
	prove(``!p. !s. p IN (^ksname).L s = p s``,
	      SIMP_TAC std_ss [KS_accfupds,combinTheory.K_THM,ks_def,IN_DEF]
	      THEN CONV_TAC (QUANT_CONV (GEN_PALPHA_CONV s))
	      THEN PBETA_TAC
	      THEN REPEAT PGEN_TAC
	      THEN REFL_TAC)
    end

fun prove_ap_ext_ksT ks1_def ks2_def s1 s2 ks1_t_def ks2_t_def =
    let val s1' = ksTools.mk_primed_state s1
	val s2' = ksTools.mk_primed_state s2
        val ksname1 = lhs(concl ks1_def)
	val ksname2 = lhs(concl ks2_def)
    in
	prove(``!a s1 s1' s2 s2'. s1>--(^ksname1)/a-->s1' = (s1,s2)>--(^ksname2)/a-->(s1',s2')``,
              EVERY (List.map (fn t => CONV_TAC (LAST_FORALL_CONV (GEN_PALPHA_CONV t))) [s2',s2,s1',s1])
	      THEN PURE_REWRITE_TAC [KS_TRANSITION_def,KS_accfupds,combinTheory.K_THM,
				ks1_def,ks2_def,IN_DEF, ks1_t_def,ks2_t_def]
              THEN SIMP_TAC std_ss []
	      THEN REPEAT PGEN_TAC
	      THEN ACCEPT_TAC TRUTH)
    end

(*FIXME: I'm being lazy here by assuming empty environments. Generalise this. *)
fun prove_ap_ext_e ks1_def ks2_def s1 s2 e1 e2 =
    let val ksname1 = lhs(concl ks1_def)
	val ksname2 = lhs(concl ks2_def)
    in
	prove(``!Q. !s1 s2. s1 IN ^e1 Q = (s1,s2) IN ^e2 Q``,
	      SIMP_TAC std_ss [NOT_IN_EMPTY,EMPTY_ENV_def])
    end

fun prove_ap_ext_sub ks_def s f =
    let val ksname = lhs(concl ks_def)
    in
	prove (``!p. AP p SUBF ^f ==> p IN (^ksname).ap``,
	       SIMP_TAC std_ss (IN_INSERT::ks_def::KS_accfupds::combinTheory.K_DEF::
				MU_SUB_def::NNF_def::RVNEG_def::(tsimps ``:'a mu``))
	       THEN RW_TAC std_ss [])
    end

(* note that s2 is not the state of ks2. That's (s1,s2)*)
(* other than that, all the args here are from the stuff returned by ksTools.mk_formal_KS *)
fun gen_prove_ap_ext ks1_def ks2_def wfks1 wfks2 s1 s2 e1 e2 ks1_t_def ks2_t_def =
    let val ksname1 = lhs(concl ks1_def)
	val ksname2 = lhs(concl ks2_def)
	val apth = prove_ap_ext_ap ks1_def ks2_def s1 s2
	val ksl1 = prove_ap_ext_ksL ks1_def s1
	val ksl2 = CONV_RULE (QUANT_CONV ELIM_TUPLED_QUANT_CONV)
	    (CONV_RULE (QUANT_CONV (GEN_PALPHA_CONV (inst [alpha|->type_of s1,beta|->type_of s2] ``(s1,s2)``)))
			     (prove_ap_ext_ksL ks2_def (mk_pair(s1,s2))))
	val ksTth = prove_ap_ext_ksT ks1_def ks2_def s1 s2 ks1_t_def ks2_t_def
	val eth = prove_ap_ext_e ks1_def ks2_def s1 s2 e1 e2
    in
      List.foldl (fn (ass,th) => MATCH_MP th ass) (ISPECL [ksname1,ksname2,s1,s2,e1,e2] AP_EXT_THM)
      [wfks1,wfks2,ksl1,ksl2,apth,ksTth,eth]
    end

fun spec_prove_ap_ext gapeth ks1_def s1 f =
    let val subth = prove_ap_ext_sub ks1_def s1 f
	val imfth = prove_imf f
    in (MATCH_MP (MATCH_MP gapeth imfth) subth) end

fun prove_psd_ap ks1_def ks2_def =
    let val ksname1 = lhs(concl ks1_def)
	val ksname2 = lhs(concl ks2_def)
    in prove(``(^ksname1).ap = (^ksname2).ap``,PURE_REWRITE_TAC [KS_accfupds,combinTheory.K_THM,ks1_def,ks2_def]
					 THEN REFL_TAC)
    end

fun prove_psd_L ks1_def ks2_def =
    let val ksname1 = lhs(concl ks1_def)
	val ksname2 = lhs(concl ks2_def)
    in prove(``(^ksname1).L = (^ksname2).L``,PURE_REWRITE_TAC [KS_accfupds,combinTheory.K_THM,ks1_def,ks2_def]
					 THEN REFL_TAC)
    end

(* here I am assuming that the rhs of ks1 is just the full rhs of the lifted ks (e.g. apb_h)
   which is just the lhs of the unlifted ks (talking about the ks_t_def's produced by mk_formal_KS here)
   and the rhs of ks2 is just the conjunction of the lhs's of the lifted ks and the ks it was composed with (e.g. ahb)
   so we only rewrite out the defn of ks2_t *)
(* we also need the defn of the transition system of ks1: ks1T_def, to get ks2_t in lifted rather than unlifted terms
   note that this ks1T is not the same as the ks1T needed in the ap_ext proof: that was for the unlifted ks (e.g. apb),
   this is for the lifted ks (e.g. apb_h)*)
fun prove_psd_T ks1_def ks2_def ks1_t_def ks2_t_def s =
    let val ksname1 = lhs(concl ks1_def)
	val ksname2 = lhs(concl ks2_def)
	val s' = ksTools.mk_primed_state s
	(*val ks1d = PURE_ONCE_REWRITE_RULE [GSYM ks1T_def] ks1_t_def*)
    in
	prove(``!a s s'. (^ksname2).T a (s,s') ==> (^ksname1).T a (s,s')``,
		 CONV_TAC (QUANT_CONV (LAST_FORALL_CONV (GEN_PALPHA_CONV s')))
		 THEN CONV_TAC (QUANT_CONV (GEN_PALPHA_CONV s))
		 THEN PURE_REWRITE_TAC  [KS_accfupds,combinTheory.K_THM,ks1_def,ks2_def,
							   (*ks1d,*)ks1_t_def,ks2_t_def]
		 THEN PURE_REWRITE_TAC [PURE_ONCE_REWRITE_RULE [combinTheory.I_THM] (hd (get_ss_rewrs boolSimps.LET_ss)),
					AND1_THM]
		 THEN REPEAT PGEN_TAC
		 THEN ACCEPT_TAC TRUTH)
    end

(* imfth is an option type in case we already have that |- IMF f
   the rest we can all get from mk_formal_KS
   except ks1T_def, which is the TRANS def for ks1 and e1, which is the env *)
fun gen_prove_par_sync_decomp wfks1 wfks2 ks1_def ks2_def ks1_t_def ks2_t_def s e1 =
	let val ksname1 = lhs(concl ks1_def)
	    val ksname2 = lhs(concl ks2_def)
	    val apth = prove_psd_ap ks1_def ks2_def
	    val lth = prove_psd_L ks1_def ks2_def
	    val tth = prove_psd_T ks1_def ks2_def ks1_t_def ks2_t_def s
	in  List.foldl (fn (ass,th) => MATCH_MP th ass) (ISPECL [s,e1,ksname1,ksname2] PAR_SYNC_DECOMP)
		       [wfks1,wfks2,apth,lth,tth]
	end

fun prove_psd_imf imfth f ns_ty =
    let val th1 = PURE_ONCE_REWRITE_RULE [ISPEC f APEXT_IMF] imfth
    in INST_TYPE [beta|->ns_ty] th1 end

(* copied from cearTools.mk_abs_cons_mf_thms *)
fun prove_psd_subf f' =
let val p_ty = muSyntax.get_prop_type f'
    val g = inst [alpha|->p_ty] (mk_var("g",mu_ty))
    val avar = mk_var("a",stringLib.string_ty)
    val gl =  list_mk_forall([avar,g],mk_neg(list_mk_comb(get_mu_ty_sub_tm p_ty,
						   [mu_dmd avar g,mk_comb(get_mu_ty_nnf_tm p_ty,f')])))
    in prove (gl,Induct_on `g` THEN SIMP_TAC std_ss ([AP_EXT_def,(GSYM APEXT_NNF),MU_SUB_def,NNF_def,RVNEG_def]
						     @(tsimps ``:'a mu``))) end

fun spec_prove_par_sync_decomp gpsdth f imfth =
    let val ps_ty = List.hd(snd(dest_type(get_prop_type f))) (* unlifted state type*)
	val ns_ty =  List.last(snd(dest_type(List.hd(snd(dest_type
			(get_prop_type (fst (dest_forall (concl gpsdth)))))))))(* lifted type's state's snd comp *)
	val f' = mk_comb(inst [alpha|->ps_ty,beta|->ns_ty] ``AP_EXT``,f) (* lifted f *)
	val imfth = prove_psd_imf (if isSome imfth then valOf imfth else prove_imf f) f ns_ty
	val subth = prove_psd_subf f'
    in (MATCH_MP (MATCH_MP (ISPEC f' gpsdth) imfth) subth) end

(* decomp generation on full auto: this gives a theorem that says that f holds in M then it holds in M x M',
   as long as f is universal and well formed *)
(*FIXME: at the moment only the env=EMPTY_ENV will work here *)
(*FIXME: at the moment there must be no overlap in the vars of s1 and s2 (I think this can be fixed)*)
fun mk_gen_par_sync_comp_thm S01 TS1 nm1 S02 TS2 nm2 env =
    let val s1 = mk_state S01 TS1
	val s2 = mk_state S02 TS2
	val sc = mk_pair(s1,s2) (* state of the composed model *)
	val (ks1_ap,ks1_def,ks1_wf,(*SOME(ks1_s0,ks1_t)*)_,ks1_t_def,ks1_s',ks1_avar) =
	    ksTools.mk_formal_KS S01 TS1 s1 true NONE NONE (SOME nm1)
	val s1' = ks1_s'
	val (ks2_ap,ks2_def,ks2_wf,(*SOME(ks2_s0,ks2_t)*)_,ks2_t_def,ks2_s',ks2_avar) =
	    ksTools.mk_formal_KS S01 TS1 sc true NONE NONE (SOME (nm1^"_lift"))
	val s2' = ks2_s'
	val gapeth = gen_prove_ap_ext ks1_def ks2_def ks1_wf ks2_wf s1 s2
				      (inst [alpha|->type_of s1] ``\(s:string).{}``)
				      env ks1_t_def ks2_t_def
	val S0c = mk_conj(S01,S02)
	val TSc = [(".",mk_conj(snd(hd TS1),snd(hd TS2)))] (*ASSERT: sync, so assume TSi are of the form [(".",ts)] *)
	val (ksc_ap,ksc_def,ksc_wf,(*SOME(ksc_s0,ksc_t)*)_,ksc_t_def,ksc_s',ksc_avar) =
	    ksTools.mk_formal_KS S0c TSc sc true NONE NONE (SOME (nm1^"_"^nm2))
	val sc' = ksc_s'
	val gpsdth = gen_prove_par_sync_decomp ks2_wf ksc_wf ks2_def ksc_def ks2_t_def ksc_t_def sc env
	val f = fst (dest_forall (concl gapeth))
        val f' = fst (dest_forall (concl gpsdth))
        val aef = mk_comb(inst [alpha|->type_of s1,beta|->type_of s2] ``AP_EXT``,f)
        val sgpsdth = SPEC aef gpsdth
	val sgapeth = PURE_ONCE_REWRITE_RULE [APEXT_IMF] gapeth
	val psdl = strip_imp (concl sgpsdth)
	val apel = strip_imp (snd(dest_forall (concl sgapeth)))
	val th = prove(list_mk_imp([concl ks1_wf,concl ks2_wf,concl ksc_wf], (* these are needed because of lazy thms*)
			     mk_forall(f,list_mk_imp([hd (fst psdl),List.nth(fst psdl,1),List.nth(fst apel,1)],
					 mk_imp(lhs(snd apel),snd psdl)))),METIS_TAC [gpsdth,gapeth,APEXT_IMF])
	val th = PURE_ONCE_REWRITE_RULE [GSYM APEXT_IMF] (List.foldl (fn (ass,th) => MATCH_MP th ass) th
		       [ks1_wf,ks2_wf,ksc_wf])
    in (th,ks1_def,s1,s2) end

(* takes the output f mk_gen_par_sync_comp_thm and an f and return thm that says f holds in M x M' *)
(* FIXME: ideally this should take the thm produced by hc rather than just f, for full auto compositionality
   but in that case we'll need to fix things so that it uses the ks already generated in the hc model
   which means this will have to called from with modelTools so it has access to the internal cache  *)
fun mk_par_sync_comp_thm (gpscth,ks1_def,s1,s2) f imfth =
    let val imfth = if isSome imfth then valOf imfth else prove_imf f
	val ps_ty = type_of s1 (* unlifted state type*)
	val ns_ty =  type_of s2 (* lifted type's state's snd comp *)
	val f' = mk_comb(inst [alpha|->ps_ty,beta|->ns_ty] ``AP_EXT``,f) (* lifted f *)
	val psdsubth = prove_psd_subf f'
	val apesubth = prove_ap_ext_sub ks1_def s1 f
    in
	(List.foldl (fn (ass,th) => MATCH_MP th ass) gpscth [imfth,psdsubth,apesubth])
    end

end
end
