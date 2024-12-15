
structure cearTools =
struct

local

open Globals HolKernel Parse

open boolSyntax pairSyntax pairTools PairRules bossLib Tactical Tactic
     Drule Rewrite pred_setTheory boolTheory Conv pairTheory
     pred_setTheory pred_setLib stringLib listTheory rich_listTheory
     simpLib pairLib PrimitiveBddRules DerivedBddRules Binarymap
     HolSatLib sumSyntax numSyntax

open cearTheory ksTheory setLemmasTheory muSyntaxTheory muSyntax
     muTheory muTools ksTheory muCheck bddTools envTheory ksTools
     commonTools lazyTools lzPairRules lzConv

val _ = numLib.temp_prefer_num();

val dpfx = "crt_"

in

val _ = set_trace "notify type variable guesses" 0;
val abs_ks_tm = ``cear$ABS_KS``
val is_abs_fun_tm = ``cear$IS_ABS_FUN``
val _ = set_trace "notify type variable guesses" 1;

fun get_astate_ty hname = (snd o pairSyntax.dest_prod o hd o snd o dest_type o type_of) hname

(* prove that ABS_KS ks h = aks  *)
(* where hd is the definition h(s,sh) = ... (required only to get our hands on the constant h) *)
fun mk_abs_eq_thm state state' astate astate' n hd_def ks_def aks_def goal =
    prove(goal,
          REWRITE_TAC [GSYM hd_def]
          THEN REWRITE_TAC [ks_def,aks_def,ABS_KS_def,KS_component_equality,KS_accfupds,combinTheory.K_DEF]
          THEN BETA_TAC
          THEN REPEAT CONJ_TAC THENL
          [
           REWRITE_TAC [EXTENSION]
           THEN CONV_TAC (PairRules.GEN_PALPHA_CONV astate)
           THEN PairRules.PGEN_TAC
           THEN CONV_TAC (RHS_CONV pred_setLib.SET_SPEC_CONV)
           THEN CONV_TAC (RHS_CONV (PairRules.GEN_PALPHA_CONV state))
           THEN CONV_TAC (RHS_CONV commonTools.ELIM_TUPLED_QUANT_CONV)
           THEN SIMP_TAC std_ss [IN_DEF,CONJ_COMM] THEN PairRules.PBETA_TAC, (* S0 *)
           CONV_TAC (RHS_CONV (ABS_CONV (GEN_PALPHA_CONV (mk_pair(astate,astate')))))
           THEN CONV_TAC (RHS_CONV (PABS_CONV (PABS_CONV(QUANT_CONV(GEN_PALPHA_CONV state')))))
           THEN CONV_TAC (RHS_CONV (ABS_CONV (PABS_CONV(GEN_PALPHA_CONV state))))
           THEN PBETA_TAC
           THEN REFL_TAC, (* T *)
           REWRITE_TAC [SET_SPEC,BIGUNION]
           THEN ONCE_REWRITE_TAC [FUN_EQ_THM]
           THEN CONV_TAC (GEN_PALPHA_CONV astate)
           THEN PairRules.PGEN_TAC
           THEN CONV_TAC (FORK_CONV(PBETA_CONV,PBETA_CONV))
           THEN ONCE_REWRITE_TAC [FUN_EQ_THM]
           THEN GEN_TAC
           THEN CONV_TAC (FORK_CONV(PBETA_CONV,ONCE_REWRITE_CONV [GSYM SPECIFICATION]))
           THEN CONV_TAC (RHS_CONV (SIMP_CONV std_ss [SET_SPEC]))
           THEN CONV_TAC (RHS_CONV (QUANT_CONV (LAND_CONV(GEN_PALPHA_CONV state))))
           THEN PBETA_TAC
           THEN CONV_TAC (RHS_CONV (QUANT_CONV (LAND_CONV commonTools.ELIM_TUPLED_QUANT_CONV)))
           THEN NTAC n (CONV_TAC (RHS_CONV (STRIP_QUANT_CONV LEFT_AND_EXISTS_CONV)))
           THEN RW_TAC std_ss [IN_DEF]
           THEN REFL_TAC
          ])

(* abs_fun is (ap_0 = av_0) /\ (ap_1 = av_1) /\ ... where the ap_i are atomic propositions extracted (currently) from the properties to
   be checked. Thus the size of the abstract state is the same as the total number of atomic props over all the properties.
   In case this is >= the number of concrete state vars (possible in very small models), hct.maA ensures we do not bother abstracting *)
fun mk_abs_fun aapl vm state hname =
    let val _ = dbgTools.DEN dpfx "maf" (*DBG*)
        val state' = mk_primed_state state
        val nabsv = List.length aapl (* # of abs state vars needed *)
        (*FIXME: what happens if there is a concrete state var called av_i? bad things *)
        val astate = pairSyntax.list_mk_pair(List.tabulate(nabsv,fn i => mk_bool_var("av"^(int_to_string i))))
        val vm = List.foldl (* add any newly created abstract vars to the varmap *)
                     (fn (v,bm) =>
                         if isSome(Binarymap.peek(bm,v)) then bm
                         else let val n = Binarymap.numItems bm
                              in Binarymap.insert(Binarymap.insert(bm,v,n+1),v^"'",n) end)
                     vm  (List.map term_to_string (strip_pair astate))
        val _ = if (bdd.getVarnum()<(Binarymap.numItems vm))
                then bdd.setVarnum (Binarymap.numItems vm) else ()
        (*FIXME: it would be nice to use Lexis.nameStrm here, but then need to restructure init_abs to return stuff other than
                 what comes from the cache, since I want to be able to eventually persist the cache, and nameStrm is a closure *)
        val hn = if (isSome hname) then valOf hname else "af"
        val _ = new_constant(hn,(mk_prod(type_of state,type_of astate)) --> bool)
        val hnc = mk_const(hn,(mk_prod(type_of state,type_of astate)) --> bool)
        val apl = List.map pbody aapl
        val apll = listSyntax.mk_list (apl,bool)
        val ast = strip_pair astate
        val shl = listSyntax.mk_list (ast,bool)
        val hd_def =  hd(Defn.eqns_of(Hol_defn hn
                                `(^hnc) (^state,^(astate)) = AND_EL (MAP (UNCURRY $=) (ZIP(^apll,^shl)))`))
        val utjf = (fn _ => CONV_RULE (STRIP_QUANT_CONV (RHS_CONV ((funpow (nabsv-1) RAND_CONV) (* get rid of trailing ``/\ T`` *)
                                                                     (PURE_ONCE_REWRITE_CONV [AND_CLAUSES]))))
                                    (PURE_REWRITE_RULE
                                         [MAP,ZIP,UNCURRY_DEF,AND_EL_DEF,combinTheory.I_THM,combinTheory.C_THM,ALL_EL] hd_def))
        val utgl = list_mk_forall(((strip_pair state)@ast),
                             mk_eq(lhs(snd(strip_forall(concl hd_def))),
                                   list_mk_conj(List.map mk_eq (ListPair.zip(apl,ast)))))
        val unwind_thm = mk_lthm (fn _ => (utgl,utjf)) utjf
        val _ = dbgTools.CBTH (dpfx^"maf_unwind_thm") unwind_thm
        val _ = lazyTools.testlz (dpfx^"maf_unwind_thm") utjf unwind_thm
        val abs_fun = BddEqMp (SYM (SPEC_ALL unwind_thm)) (t2tb vm (rhs(snd(strip_forall(concl unwind_thm)))))
        val _ = dbgTools.DTH (dpfx^"maf_ hd_def") hd_def (*DBG*)
        val _ = dbgTools.DEX dpfx "maf" (*DBG*)
    in (astate,unwind_thm,Binarymap.mkDict Int.compare,hd_def,abs_fun) end


(* prove that the concrete abs_funs is total, by building the bdd *)
(* FIXME: can we prove this offline by completely formalizing the construction of the abs fun? *)
fun mk_abs_fun_total_thm abs_fun =
    let val _ = dbgTools.DEN dpfx "maftt" (*DBG*)
        val (st,ast) = (strip_pair ## strip_pair) (dest_pair(snd(dest_comb(getTerm abs_fun))))
        val gl = mk_pforall(list_mk_pair st, mk_pexists(list_mk_pair ast,getTerm abs_fun))
        val jf = (fn _ => (REWRITE_RULE [SYM (CONV_RULE (RHS_CONV (STRIP_QUANT_CONV ELIM_TUPLED_QUANT_CONV))
                                                 (ELIM_TUPLED_QUANT_CONV gl))]
                                 (BddThmOracle(BddForall st (BddExists ast abs_fun)))))
        val res = mk_lthm (fn _ => (gl,jf)) jf
        val _ = lazyTools.testlz (dpfx^"maftt_res") jf res
        val _ = dbgTools.DTH (dpfx^"maftt_res") res (*DBG*)
        val _ = dbgTools.DEX dpfx "maftt" (*DBG*)
    in res end

(* function that alpha-convs IS_ABS_FUN_def to use concrete state, astate and h *)
(* FIXME: clean this up*)
fun mk_conc_is_abs_fun_def st1 st2 state astate abs_fun ks_def =
    let val _ = dbgTools.DEN dpfx "mciafd" (*DBG*)
        val hit_tot = STRIP_QUANT_CONV o RHS_CONV  o LAND_CONV
        val th = INST_TYPE [``:'state`` |-> type_of st1, ``:'astate`` |-> type_of astate] IS_ABS_FUN_def
        val th1 = CONV_RULE (hit_tot (QUANT_CONV (GEN_PALPHA_CONV astate))) th
        val th2 = CONV_RULE (hit_tot (GEN_PALPHA_CONV state)) th1
        val hit_ap = STRIP_QUANT_CONV o RHS_CONV  o RAND_CONV
        val th3 = CONV_RULE (hit_ap (QUANT_CONV (QUANT_CONV (GEN_PALPHA_CONV astate)))) th2
        val th4 = CONV_RULE (hit_ap (QUANT_CONV (GEN_PALPHA_CONV st2))) th3
        val th5 = CONV_RULE (hit_ap (GEN_PALPHA_CONV st1)) th4
        val aht  = mk_pabs(mk_pair(state,astate),getTerm abs_fun)
        val ksname = lhs(concl ks_def)
        val res = PBETA_RULE (GEN_ALL (ISPECL [ksname,mk_var("e",stringLib.string_ty-->(type_of st1)-->bool),aht] th5))
        val _ = dbgTools.DTH (dpfx^"mciafd_ cons is abs fun") res (*DBG*)
        val _ = dbgTools.DEX dpfx "mciafd" (*DBG*)
    in res end

(* mk refined abstraction function and the is_abs_fun thm for it as well (to be used by mk_abs_cons_thm) *)
(* as1 is the abs state that got split into dead and bad (which are conrete state sets) *)
fun mk_ref_abs_fun af state astate ks_def ath_lem1 ath_lem2 hd_def idx as1 dead bad k =
    let val _ = dbgTools.DEN dpfx "mraf" (*DBG*)
        (*val nabsv = Real.ceil(log2(Real.fromInt(k+1))) (* to check if new abstract state requires another abs var to be added *)*)
        val ast = strip_pair astate
        val nabsv = (List.length ast)+1 (* FIXME: we add one abs var per refinement. could do better (see Mar 20, 2005, notes) *)
        val vm = getVarmap af
        val navn = "av"^(int_to_string(nabsv-1))
        val nav = mk_var(navn,bool)
        val vmn = listmax(List.map snd (Binarymap.listItems vm))+1 (* can't use bddVarnum because the cnf stuff in ca' adds to it *)
        val vm' = Binarymap.insert(Binarymap.insert(vm,navn,vmn+1),navn^"'",vmn)
        val astate2 = list_mk_pair (nav::(strip_pair(astate)))
        val _ = if (bdd.getVarnum()<((Binarymap.numItems vm')))
                then bdd.setVarnum ((Binarymap.numItems vm')) else ()
        val (navtb,nnavtb) = (BddVar true vm' nav,BddVar false vm' nav)
        (* refined abs fun af' is (bad /\ nav /\ af) \/ (dead /\ ~nav /\ af) \/ (~bad /\ ~dead /\ af) *)
        val (bad2,dead2,af2) = (BddExtendVarmap vm' bad,BddExtendVarmap vm' dead,BddExtendVarmap vm' af)
        val _ = dbgTools.DBD (dpfx^"mraf_bad2_bdd") (getBdd bad2)(*DBG*)
        val _ = dbgTools.DBD (dpfx^"mraf_dead2_bdd") (getBdd dead2)(*DBG*)
        val _ = dbgTools.DBD (dpfx^"mraf_af2_bdd") (getBdd af2)(*DBG*)
        val af' = BddListDisj vm' [BddListConj vm' [bad2,navtb,af2],BddListConj vm' [dead2,nnavtb,af2],
                                  BddListConj vm' [BddNot bad2,BddNot dead2,af2]]
        val _ = dbgTools.DBD (dpfx^"mraf_af'_bdd") (getBdd af')(*DBG*)
        val hn = term_to_string2(rator(lhs(snd(strip_forall(concl hd_def)))))^"'"
        val harg_ty = mk_prod(type_of state,type_of astate2)
        val _ = new_constant(hn,harg_ty --> bool)
        val hnc = mk_const(hn,harg_ty --> bool)
        val hd_def2 = hd(Defn.eqns_of(Hol_defn hn  `(^hnc)(^state,^(astate2)) = ^(getTerm af')`))
        val _ = dbgTools.DTH (dpfx^"mraf_hd_def2") hd_def2 (*DBG*)
        val _ = dbgTools.CBTH (dpfx^"mraf_hd_def2") hd_def2 (*DBG*)
        (* FIXME: the variant here does not really help avoid a name clash with vars already in state, because I add _1 etc*)
        val vn = fst(dest_var(variant ((strip_pair state)@(strip_pair (mk_primed_state state))) ``v:bool``))
        val lst1 = List.tabulate(List.length (strip_pair state),fn n => mk_bool_var(vn^(int_to_string n)^"_1"))
        val lst2 = List.tabulate(List.length (strip_pair state),fn n => mk_bool_var(vn^(int_to_string n)^"_2"))
        val subst1 = ListPair.map (fn (v,v') => v |-> v') (strip_pair state,lst1)
        val subst2 = ListPair.map (fn (v,v') => v |-> v') (strip_pair state,lst2)
        val hd_lhs = lhs(snd(strip_forall(concl hd_def2)))
        val goal = mk_imp(mk_conj(subst subst1 hd_lhs,subst subst2 hd_lhs),rand(concl ath_lem1))
        val _ = dbgTools.CBTM (dpfx^"mraf_goal") goal (*DBG*)
        val _ = dbgTools.CBTH (dpfx^"mraf_ath_lem1") ath_lem1 (*DBG*)
        val (al1ante1,al1ante2) = dest_conj(land(concl ath_lem1))
        val jfal1' = (fn _ =>  (*PURE_ONCE_REWRITE_RULE [GSYM hd_def2]*) (* prove new ath_lem1 using the old one *)
                        (prove(goal,
                               PURE_ONCE_REWRITE_TAC [hd_def2]
                               THEN RW_TAC pure_ss []
                               THEN PAT_ASSUM al1ante1 (fn t1 => PAT_ASSUM al1ante2 (fn t2 =>
                                                        LIST_ACCEPT_TAC (CONJUNCTS (MP (lazyTools.prove_lthm ath_lem1) (CONJ t1 t2))))
                               ))))
        val ath_lem1' = (*PURE_ONCE_REWRITE_RULE [GSYM hd_def2]*) (mk_lthm (fn _ => (goal,jfal1')) jfal1')
        val _ = dbgTools.DTH (dpfx^"mraf_ath_lem1'") ath_lem1' (*DBG*)
        val _ = dbgTools.CBTH (dpfx^"mraf_ath_lem1'") ath_lem1' (*DBG*)
        val _ = lazyTools.testlz (dpfx^"mraf_ath_lem1'") jfal1' ath_lem1'
        val _ = dbgTools.DTH (dpfx^"mraf_ath_lem2") ath_lem2 (*DBG*)
        val _ = dbgTools.CBTH (dpfx^"mraf_ath_lem2") ath_lem2 (*DBG*)
        val st1 = list_mk_pair lst1
        val st2 = list_mk_pair lst2
        val jfafap = (fn _ => (PGENL [st1,st2,astate2] (IMP_TRANS ath_lem1' (SPEC_ALL ath_lem2))))
        val afapgl = list_mk_pforall ([st1,st2,astate2],mk_imp((fst o dest_imp) (concl ath_lem1'),
                                                              (snd o dest_imp o snd o strip_forall) (concl ath_lem2)))
        val afap = mk_lthm (fn _ => (afapgl,jfafap)) jfafap
        val _ = dbgTools.DTH (dpfx^"mraf_afap") afap (*DBG*)
        val _ = lazyTools.testlz (dpfx^"mraf_afap") jfafap afap
        val af' = BddEqMp (SYM (SPEC_ALL hd_def2)) af'
        val aftot = mk_abs_fun_total_thm af'
        val jfiaf = (fn _ =>  (CONV_RULE (DEPTH_CONV PETA_CONV)
            (REWRITE_RULE [GSYM hd_def2] (REWRITE_RULE [CONJ aftot afap] (mk_conc_is_abs_fun_def st1 st2 state astate2 af' ks_def)))))
        val ksname = lhs(concl ks_def)
        val ((p_ty,st_ty),ast_ty) = (get_types ksname,type_of astate2)
        val e_var = inst [alpha |-> st_ty] envTools.env_tm
        val iaf = mk_lthm (fn _ =>  (mk_forall(e_var,list_mk_comb(inst [alpha|->p_ty,beta|->st_ty,gamma|->ast_ty] is_abs_fun_tm,
                                                                      [ksname,e_var,mk_const(hn,harg_ty --> bool)])),
                                                                 jfiaf)) jfiaf
        val _ = dbgTools.DTH (dpfx^"mraf_iaf") iaf (*DBG*)
        val _ = lazyTools.testlz (dpfx^"mraf_iaf") jfiaf iaf
        val _ = dbgTools.DEX dpfx "mraf" (*DBG*)
    in (af',ath_lem1',astate2,hd_def2,iaf) end

fun is_pabs_cond tm =
    (can (match_term ``COND x y z``) tm)
    andalso pairSyntax.is_pabs (#2(dest_cond tm)) andalso pairSyntax.is_pabs(#3(dest_cond tm))
    andalso Term.compare(fst (pairSyntax.dest_pabs (#2(dest_cond tm))),fst (pairSyntax.dest_pabs (#3(dest_cond tm))))=EQUAL

(* any subterm of tm matching the pattern ``if b then \x. P else \x. Q`` is converted to ``\x. if b then P else Q`` *)
fun ABS_COND_CONV tm =
    if is_pabs_cond tm
    then let val ab = fst (pairSyntax.dest_pabs (#2(dest_cond tm)))
         in  (REWRITE_CONV [GSYM COND_ABS] THENC PairRules.GEN_PALPHA_CONV ab THENC (DEPTH_CONV PairRules.PBETA_CONV)) tm end
    else NO_CONV tm

(* creates abstracted Tm and I and passes them to mk_wfKS and returns the results *)
(* h is the abs_fun as returned by mk_abs_fun *)
fun mk_abs_ks I1 ITdf RTm state astate Ric af aksname (apl,ks_def,wfKS_ks) hd_def =
    let val _ = dbgTools.DEN dpfx "mak"(*DBG*)
        val _ = profTools.bgt (dpfx^"mak") (*PRF*)
        val _ = profTools.bgt (dpfx^"mak_init") (*PRF*)
        val T1 = Binarymap.listItems RTm
        val st = strip_pair state
        val st_ty = type_of state
        val state' = mk_primed_state state
        val st' =  strip_pair state'
        val vm = getVarmap af
        val s2s' = List.map (fn(v,v') => (BddVar true vm v,BddVar true vm v')) (ListPair.zip(st,st'))
        val _ = List.app (fn (s,_) => dbgTools.DST (dpfx^ s) ) (Binarymap.listItems vm) val _ = dbgTools.DST (dpfx^ "vm\n")
        val vmabs = List.filter (fn (t,_) => (String.size t) >= 3 andalso String.compare("av",String.substring(t,0,2))=EQUAL )
                                (Binarymap.listItems vm)
        val abst = strip_pair astate
        val astate' = mk_primed_state astate
        val abst' = strip_pair astate'
        val abstcnj = t2tb vm (list_mk_conj abst)
        val abstcnj' = t2tb vm (list_mk_conj abst')
        val as2as' =  List.map (fn(v,v') => (BddVar true vm v,BddVar true vm v')) (ListPair.zip(abst,abst'))
        val _ = profTools.ent (dpfx^"mak_init") (*PRF*)
        val _ = profTools.bgt (dpfx^"mak_Ih") (*PRF*)
        val Itb = BddEqMp (SYM (fst (valOf ITdf))) (t2tb vm I1) (* abbrev Itb to use either ctlks.S0 or muks.S0 *)
        val Ih = BddExists st (BddOp(bdd.And,af,Itb))
        val Iht = getTerm Ih
        val _ = profTools.ent (dpfx^"mak_Ih") (*PRF*)
        val _ = profTools.bgt (dpfx^"mak_Th") (*PRF*)
        val Th = List.map (fn (actnm,act) => (actnm,BddExists st (BddExists st'
                                (BddOp(bdd.And,BddExtendVarmap vm act,BddOp(bdd.And,af,BddReplace as2as' (BddReplace s2s' af))))))) T1
        val Th' = List.map (fn (nm,tb) => (nm,
                                           BddEqMp (SYM ((lzELIM_TUPLED_QUANT_CONV THENC STRIP_QUANT_CONV lzELIM_TUPLED_QUANT_CONV)
                                                             (list_mk_pexists([state,state'],snd(strip_pexists(getTerm tb)))))) tb)) Th
        val T1h = List.map (fn (nm,tb) => (nm,getTerm tb)) Th'
        val _ = profTools.ent (dpfx^"mak_Th") (*PRF*)
        val _ = profTools.bgt (dpfx^"mak_ks") (*PRF*)
        val (aapl,aks_def,wfKS_aks,aRTm,_) = mk_wfKS Iht T1h (SOME (list2map Th')) astate vm Ric NONE
                                                     (SOME (af,getT (rhs(concl ks_def)),state,state')) (SOME aksname)
        val _ = profTools.ent (dpfx^"mak_ks") (*PRF*)
        val _ = profTools.ent (dpfx^"mak") (*PRF*)
        val _ = dbgTools.DTH (dpfx^"mak_ aks_def") aks_def (*DBG*)
        val _ = dbgTools.DTM (dpfx^"mak_ aks_def.T") (getT (rhs(concl aks_def))) (*DBG*)
        val _ = dbgTools.DEX dpfx "mak"(*DBG*)
    in (Iht,T1h,Ih,(aapl,aks_def,wfKS_aks,aRTm)) end

(*  |- aks = ABS_KS ks h *)
fun mk_abs_aks_thm state astate af state' astate' st hd_def ks_def aks_def =
    let val _ = dbgTools.DEN dpfx "makt"(*DBG*)
        val jf = (fn _ =>
            let val aht = mk_pabs(mk_pair(state,astate),getTerm af)
                val _ = dbgTools.DTM (dpfx^"makt_ goal") ``^(lhs (concl aks_def)) = ABS_KS ^(lhs (concl ks_def)) ^aht`` (*DBG*)
                val _ = dbgTools.DTH (dpfx^"makt_ hd_def") hd_def (*DBG*)
                val _ = dbgTools.DTH (dpfx^"makt_ ks_def") ks_def (*DBG*)
                val _ = dbgTools.DTH (dpfx^"makt_ aks_def") aks_def (*DBG*)
                val _ = dbgTools.DTM (dpfx^"makt_ aht") aht (*DBG*)
                val aksth = mk_abs_eq_thm state state' astate astate' (List.length st) hd_def ks_def aks_def
                                          ``^(lhs (concl aks_def)) = ABS_KS ^(lhs (concl ks_def)) ^aht``
                val abs_aks = CONV_RULE (RHS_CONV (RAND_CONV PETA_CONV)) aksth
            in abs_aks end)
        val (p_ty,st_ty,ast_ty) = (mk_type("fun",[type_of state,bool]),type_of state,type_of astate)
        val ksname = lhs(concl ks_def)
        val aksname = lhs(concl aks_def)
        val hname = rator(lhs(concl(SPEC_ALL hd_def)))
        val abs_aks = mk_lthm (fn _ => (mk_eq(aksname,
                                              list_mk_comb(inst [alpha|->p_ty,beta|->st_ty,gamma|->ast_ty] abs_ks_tm,[ksname,hname])),
                                        jf)) jf
        val _ = dbgTools.DTH (dpfx^"makt_abs_aks") abs_aks (*DBG*)
        val _ = dbgTools.CBTH (dpfx^"makt_abs_aks") abs_aks (*DBG*)
        val _ = dbgTools.DEX dpfx "makt"(*DBG*)
    in abs_aks end

(* prove the second part of the IS_ABS_FUN assum (the first part is totality) *)
fun mk_abs_fun_ap_thm state astate hR_defs_ unwind_thm (apl,ks_def,wfKS_ks) hd_def =
    let val _ = dbgTools.DEN dpfx "mafat"(*DBG*)
        val state' = mk_primed_state state
        (*FIXME: will need to fix this once state vars can be other than bools *)
        (* FIXME: the variant here does not really help avoid a name clash with vars already in state, because I add _1 etc*)
        val vn = fst(dest_var(variant ((strip_pair state)@(strip_pair state')) ``v:bool``))
        val lst1 = List.tabulate(List.length (strip_pair state),fn n => mk_bool_var(vn^(int_to_string n)^"_1"))
        val lst2 = List.tabulate(List.length (strip_pair state),fn n => mk_bool_var(vn^(int_to_string n)^"_2"))
        val st1 = list_mk_pair lst1 (*the s1 in IS_ABS_FUN_ap*)
        val st2 = list_mk_pair lst2 (*the s2 in IS_ABS_FUN_ap*)
        val st2vw = List.map (op |->) (ListPair.zip((strip_pair state)@(strip_pair state'),lst1@lst2))
        val (lht,rht) = dest_eq(snd(strip_forall(concl hd_def)))
        val _ = dbgTools.DTH (dpfx^"mafat_ hd_def") hd_def (*DBG*)
        val ath_lem1 =   hd (CONJUNCTS (PURE_ONCE_REWRITE_RULE [EQ_IMP_THM]
                         (ONCE_REWRITE_CONV [unwind_thm] (mk_conj (subst [state|->st1] lht,subst [state|->st2] lht)))))
        val _ = dbgTools.DTH (dpfx^"mafat_ath_lem1") ath_lem1 (*DBG*)
        val _ = dbgTools.CBTH (dpfx^"mafat_ath_lem1") ath_lem1 (*DBG*)
        val ksname = lhs(concl ks_def)
        val ap_eqs = rand(concl ath_lem1) (*(ap0 = av0) /\ (ap1 = av1) /\ ...  *)
        val _ = dbgTools.DTM (dpfx^"mafat_ap_eqs") ap_eqs (*DBG*)
        val gl2  = mk_forall(mk_var("e",stringLib.string_ty --> (type_of state) --> bool),
                             mk_imp(ap_eqs,``!p. p IN (^ksname).ap ==>
                                          ((^st1) IN STATES (AP p) (^ksname) e = (^st2) IN STATES (AP p) (^ksname) e)``))
        val jf2 = (fn _ =>
            let val apl' = List.map (fn ap => mk_pabs(st2,subst (List.map (fn (v,w) => v |-> w)
                                                                          (ListPair.zip(lst1,lst2))) (pbody ap))) apl
                val ap_thms =  List.map (*FIXME:clean this up, too much duplication in creation of the msa's, Lth and gen_ap_thms*)
                                   (fn th => PURE_ONCE_REWRITE_RULE [MU_SAT_def] (GSYM th))
                                   (let val (prop_type,state_type) = get_types ksname
                                        val Lth = ksTools.mk_Lth ks_def
                                        val (msa1,msa2) = Lib.pair_map (fn t => PBETA_RULE (PURE_REWRITE_RULE [Lth]        (MATCH_MP
                                                (CONV_RULE FORALL_IMP_CONV (ISPECL [t,ksname] MU_SAT_AP)) wfKS_ks))) (st1,st2)
                                    in (List.map (fn mf =>muCheck.mk_gen_ap_thm ksname st1 msa1 mf)(List.map (fn ap => ``AP ^ap``) apl))
                                     @ (List.map (fn mf =>muCheck.mk_gen_ap_thm ksname st2 msa2 mf)(List.map (fn ap =>``AP ^ap``) apl'))
                                    end)
                val _ = dbgTools.DST (dpfx^"mafat_ before ath_lem2")  (*DBG*)
                val _ = dbgTools.CBTM (dpfx^"mafat_gl2") gl2(*DBG*)
                val _ = dbgTools.CBTHL (dpfx^"mafat_ksthl") [lazyTools.prove_lthm ks_def,KS_accfupds,combinTheory.K_DEF] (*DBG*)
                val _ = dbgTools.CBTHL (dpfx^"mafat_fstthl") (List.map lazyTools.prove_lthm (ap_thms)) (*DBG*)
                val ath_lem2 = prove(gl2, (* note we unlazify any thms used in any proof that uses tactics (VALID fails otherwise)*)
                                     NTAC 3 STRIP_TAC
                                          THEN CONV_TAC (LAND_CONV (PURE_REWRITE_CONV [lazyTools.prove_lthm ks_def,
                                                                                      KS_accfupds,combinTheory.K_DEF]))
                                          THEN BETA_TAC
                                          THEN RW_TAC pure_ss [IN_INSERT,NOT_IN_EMPTY]
                                          THEN ASM_REWRITE_TAC (List.map lazyTools.prove_lthm (ap_thms)))
                val _ = dbgTools.CBTH (dpfx^"mafat_ath_lem2") ath_lem2(*DBG*)
                val _ = dbgTools.DTH (dpfx^"mafat_ath_lem2") ath_lem2 (*DBG*)
            in ath_lem2 end)
        val ath_lem2 =  mk_lthm (fn _ => (gl2,jf2)) jf2
        val _ = lazyTools.testlz (dpfx^"mafat_ath_lem2") jf2 ath_lem2
        val jfap = (fn _ => PGENL [st1,st2,astate]  (IMP_TRANS ath_lem1 (SPEC_ALL ath_lem2)))
        val afap = mk_lthm (fn _ => (list_mk_pforall([st1,st2,astate],mk_imp(land(concl ath_lem1),
                                                                             rand(snd(strip_forall(concl ath_lem2))))), jfap)) jfap
        val _ = lazyTools.testlz (dpfx^"mafat_afap") jfap afap
        val _ = dbgTools.DEX dpfx "mafat"(*DBG*)
    in (st1,st2,ath_lem1,ath_lem2,afap) end

local

val Qvar = mk_var("Q",stringLib.string_ty)
val gvar = mk_var("g",mu_ty)
val avar = mk_var("a",stringLib.string_ty)
fun pvar p_ty = mk_var("p",p_ty)
fun mk_glno_rv p_ty f =
    mk_forall(Qvar,mk_neg(list_mk_comb(get_mu_ty_sub_tm p_ty,
                                       [mu_neg(mu_RV p_ty Qvar),
                                        mk_comb(get_mu_ty_nnf_tm p_ty,f)])))
fun mk_glno_dmd p_ty f =
    let val g = inst [alpha|->p_ty] gvar
    in list_mk_forall([avar,g],mk_neg(list_mk_comb(get_mu_ty_sub_tm p_ty,
                                                   [mu_dmd avar g,mk_comb(get_mu_ty_nnf_tm p_ty,f)]))) end
fun mk_glp_in_ap p_ty f ksname =
    let val p = pvar p_ty
    in mk_forall(p,mk_imp(list_mk_comb(get_mu_ty_sub_tm p_ty,[mu_AP p,f]),
                          list_mk_comb(inst [alpha|->p_ty] pred_setSyntax.in_tm,[p,mk_ks_dot_ap ksname]))) end

in
(* prove the three formula related assumptions to ABS_CONS_MODEL *)
fun mk_abs_cons_mf_thms mf (apl,ks_def,wfKS_ks) vm =
let val _ = dbgTools.DEN dpfx "macmt"(*DBG*)
    val _ = profTools.bgt (dpfx^"macmt")(*PRF*)
    val ksname = lhs(concl ks_def)
    val (p_ty,s_ty) = get_types ksname
    val _ = profTools.bgt (dpfx^"macmt_no_rv")(*PRF*)
    val _ = profTools.bgt (dpfx^"macmt_no_rv_gl")(*PRF*)
    val glno_rv = mk_glno_rv p_ty mf (*``!Q. ~SUBFORMULA (~RV Q) (NNF (^mf))``*)
    val _ = profTools.ent (dpfx^"macmt_no_rv_gl")(*PRF*)
    val jfno_rv = (fn _ =>  (prove (glno_rv,SIMP_TAC std_ss (MU_SUB_def::NNF_def::RVNEG_def::(tsimps ``:'a mu``)))))
    val no_rv = mk_lthm (fn _ =>  (glno_rv,jfno_rv)) jfno_rv
    val _ = lazyTools.testlz (dpfx^"macmt_no_rv") jfno_rv no_rv(*DBG*)
    val _ = profTools.ent (dpfx^"macmt_no_rv")(*PRF*)
    val _ = profTools.bgt (dpfx^"macmt_no_dmd")(*PRF*)
    val _ = profTools.bgt (dpfx^"macmt_no_dmd_gl")(*PRF*)
    val glno_dmd = mk_glno_dmd p_ty mf (*``(!a g. ~SUBFORMULA <<a>> g (NNF (^mf)))``*)
    val _ = profTools.ent (dpfx^"macmt_no_dmd_gl")(*PRF*)
    val jfno_dmd = (fn _ =>  (prove (glno_dmd,Induct_on `g` THEN SIMP_TAC std_ss (MU_SUB_def::NNF_def::RVNEG_def::(tsimps ``:'a mu``)))))
    val no_dmd = mk_lthm (fn _ =>  (glno_dmd,jfno_dmd)) jfno_dmd
    val _ = lazyTools.testlz (dpfx^"macmt_no_dmd") jfno_dmd no_dmd(*DBG*)
    val _ = profTools.ent (dpfx^"macmt_no_dmd")(*PRF*)
    val _ = profTools.bgt (dpfx^"macmt_p_in_ap")(*PRF*)
    val _ = profTools.bgt (dpfx^"macmt_p_in_ap_gl")(*PRF*)
    val glp_in_ap = mk_glp_in_ap p_ty mf ksname (*``!p. SUBFORMULA (AP p) (^mf) ==> p IN (^(lhs(concl ks_def))).ap``*)
    val _ = dbgTools.CBTM (dpfx^"macmt_glp") glp_in_ap (*DBG*)
    val _ = dbgTools.CBTHL (dpfx^"macmt_glpl1") (ks_def::KS_accfupds::combinTheory.K_DEF::MU_SUB_def::NNF_def::RVNEG_def::(tsimps ``:'a mu``))
    val _ = profTools.ent (dpfx^"macmt_p_in_ap_gl")(*PRF*)
    val jfp_in_ap = (fn _ =>  (prove (glp_in_ap,
                       PURE_REWRITE_TAC (*SIMP_TAC std_ss *)
                                (List.map lazyTools.prove_lthm
                                          (ks_def::KS_accfupds::combinTheory.K_DEF::MU_SUB_def::NNF_def::RVNEG_def::(tsimps ``:'a mu``)))
                       THEN BETA_TAC
                       THEN RW_TAC pure_ss []
                       THEN CONV_TAC (pred_setLib.IN_CONV (AP_EQ vm)))))
    val p_in_ap = mk_lthm (fn _ =>  (glp_in_ap,jfp_in_ap)) jfp_in_ap
    val _ = lazyTools.testlz (dpfx^"macmt_p_in_ap") jfp_in_ap p_in_ap(*DBG*)
    val _ = profTools.ent (dpfx^"macmt_p_in_ap")(*PRF*)
    val _ = profTools.ent (dpfx^"macmt")(*PRF*)
    val _ = dbgTools.DEX dpfx "macmt"(*DBG*)
in [no_rv,no_dmd,p_in_ap] end
end

(* create the concrete thm to discharge the IS_ABS_FUN assum to ABS_CONS_MODEL *)
(* could not prove this offline:
     could not do totality because STRIP_PAIR/LIST_MK_PAIR are not well typed in the logic
     could not do the ap thm because I ran out of time plus it required an induction on ZIP(apl,shl) that I could not figure out *)
fun mk_is_abs_fun_thm ksname hname abs_fun state astate hR_defs_ unwind_thm (apl,ks_def,wfKS_ks) hd_def =
    let val _ = dbgTools.DEN dpfx "miaft"(*DBG*)
        val aftot = mk_abs_fun_total_thm abs_fun
        val _ = dbgTools.DTH (dpfx^"miaft_ aftot") aftot (*DBG*)
        val (st1,st2,ath_lem1,ath_lem2,afap) = mk_abs_fun_ap_thm state astate hR_defs_ unwind_thm (apl,ks_def,wfKS_ks) hd_def
        val _ = dbgTools.DTH (dpfx^"miaft_ath_lem1") ath_lem1(*DBG*)
        val _ = dbgTools.CBTH (dpfx^"miaft_ath_lem1") ath_lem1(*DBG*)
        val _ = dbgTools.DTH (dpfx^"miaft_ath_lem2") ath_lem2 (*DBG*)
        val _ = dbgTools.CBTH (dpfx^"miaft_ath_lem2") ath_lem2 (*DBG*)
        val _ = dbgTools.DTH (dpfx^"miaft_ afap1") afap (*DBG*)
        val iafjf = (fn _ => let val afap = REWRITE_RULE [GSYM hd_def] afap (* FIXME: do I need the rewr? it's already in terms of af *)
                                 val _ = dbgTools.DTH (dpfx^"miaft_ afap2") afap (*DBG*)
                                 val ciafd =  (mk_conc_is_abs_fun_def st1 st2 state astate abs_fun ks_def)
                                 val _ = dbgTools.DTH (dpfx^"miaft_ ciafd") ciafd (*DBG*)
                                 val iaf = CONV_RULE (DEPTH_CONV PETA_CONV) (* combine aftot and afap into iaf*)
                                                     (REWRITE_RULE [GSYM hd_def] (REWRITE_RULE [CONJ aftot afap] ciafd))
                                 val _ = dbgTools.DTH (dpfx^"miaft_ iaf") iaf (*DBG*)
                             in iaf end)
        val ((p_ty,st_ty),ast_ty) = (get_types ksname,type_of astate)
        val e_var = inst [alpha |-> st_ty] envTools.env_tm
        val iaf = mk_lthm (fn _ => (mk_forall(e_var,list_mk_comb(inst [alpha|->p_ty,beta|->st_ty,gamma|->ast_ty] is_abs_fun_tm,
                                                                      [ksname,e_var,hname])),
                                                                 iafjf)) iafjf
        val _ = dbgTools.DTH (dpfx^"miaft_iaf") iaf (*DBG*)
        val _ = dbgTools.CBTH (dpfx^"miaft_iaf") iaf (*DBG*)
        val _ = dbgTools.DEX dpfx "miaft"(*DBG*)
    in (ath_lem1,ath_lem2,iaf) end

(* discharge, online, the assumptions to ABS_CONS_MODEL *)
(* note enveq thm requires that both env and aenv be empty: this is true for instance if mf was originally in CTL*/LTL/CTL etc. *)
(* FIXME: split this so that we can discharge the non-mf_assums once in one func, and discharge mf_assums again and again for each mf,
   thus saving time, since iaf is at the moment expensive to compute but does not change with mf *)
fun mk_abs_cons_thm mf (apl,ks_def,wfKS_ks) env aenv hd_def iaf_ vm =
    let val _ = dbgTools.DEN dpfx "mact"(*DBG*)
        val _ = profTools.bgt (dpfx^"mact")(*PRF*)
        val mf_assums = mk_abs_cons_mf_thms mf (apl,ks_def,wfKS_ks) vm
        val (p_ty,s_ty) = get_types (lhs(concl ks_def))
        val (hnc,args) = dest_comb(lhs(snd(strip_forall(concl hd_def))))
        val Qvar = mk_var("Q",stringLib.string_ty)
        val svar = mk_var("s",s_ty)
        val as_ty = snd(dest_prod(type_of args))
        val asvar = mk_var("sh",as_ty)
        val glenveq = list_mk_forall([Qvar,svar,asvar],
                                     mk_imp(mk_comb(hnc,mk_pair(svar,asvar)),
                                            mk_imp(list_mk_comb(inst [alpha|->as_ty] pred_setSyntax.in_tm,[asvar,mk_comb(aenv,Qvar)]),
                                                   list_mk_comb(inst [alpha|->s_ty] pred_setSyntax.in_tm,[svar,mk_comb(env,Qvar)]))))
        val _ = dbgTools.CBTM (dpfx^"mact_glenveq") glenveq (*DBG*)
        (*``(!Q s sh. (^hnc) (s,sh) ==> sh IN (^aenv) Q ==> s IN (^env) Q)``*)
        val jfenveq = (fn _ =>  (prove(glenveq, SIMP_TAC std_ss [EMPTY_ENV_def,NOT_IN_EMPTY])))
        val enveq = mk_lthm (fn _ =>  (glenveq,jfenveq)) jfenveq
        val _ = lazyTools.testlz (dpfx^"mact_enveq") jfenveq enveq
        val _ = dbgTools.DTM (dpfx^"mact_ env") env (*DBG*)
        val _ = dbgTools.DTY (dpfx^"mact_ env") (type_of env) (*DBG*)
        val _ = dbgTools.DTH (dpfx^"mact_ iaf_") iaf_ (*DBG*)
        val iaf = ISPEC env iaf_
        val ast_ty = get_astate_ty hnc
        val jfact = (fn _ => (List.foldl (fn (mpth,th) => MATCH_MP th mpth)
                                         (ISPECL [mf,hnc,lhs(concl(ks_def)),env,aenv] ABS_CONS_MODEL)
                                  ([wfKS_ks]@mf_assums@[iaf,enveq])))
        val glact = let val (vl,bod) = strip_forall (concl ABS_CONS_MODEL)
                        val (imps,bod2) = strip_imp bod
                        val conc = mk_imp(last imps,bod2)
                        val instf = (inst  (mk_subst ([ks_p_ty,ks_s_ty,ks_as_ty])([p_ty,s_ty,ast_ty])))
                    in subst (mk_subst (List.map instf vl)
                                        [mf,hnc,lhs(concl(ks_def)),env,aenv]) (instf conc) end
        val act = mk_lthm (fn _ =>  (glact,jfact)) jfact
        val _ = dbgTools.DTH (dpfx^"mact_act") act (*DBG*)
        val _ = lazyTools.testlz (dpfx^"mact_act") jfact act
        val _ = profTools.ent (dpfx^"mact")(*PRF*)
        val _ = dbgTools.DEX dpfx "mact"(*DBG*)
 in act end

(* ASSERT: t must be a QBF *)
(* transforms input QBF to pure propositional formula using |- (?x. P x) = P T \/ P F and |- (!x. P x) = P F /\ P T *)
fun elim_quant t =
if is_exists t then let val (v,t') = dest_exists t
                    in mk_disj(elim_quant (subst [v |-> ``T``] t'),elim_quant (subst [v |-> ``F``] t')) end
else if is_forall t then let val (v,t') = dest_forall t
                    in mk_conj(elim_quant (subst [v |-> ``T``] t'),elim_quant (subst [v |-> ``F``] t')) end
else if is_neg t then mk_neg (elim_quant(dest_neg t))
else if is_conj t then mk_conj(elim_quant(fst(dest_conj t)),elim_quant(snd(dest_conj t)))
else if is_disj t then mk_disj(elim_quant(fst(dest_disj t)),elim_quant(snd(dest_disj t)))
else if is_eq t then mk_eq(elim_quant(fst(dest_eq t)),elim_quant(snd(dest_eq t)))
else if is_imp t then mk_imp(elim_quant(fst(dest_imp t)),elim_quant(snd(dest_imp t)))
else t

fun mlval tm = if tm=T then true else if tm=F then false else raise Match

fun mk_ass vm red res = bdd.assignment (ListPair.map (fn (v,c) => (Binarymap.find(vm,term_to_string2 v),mlval c)) (red,res))

(* check whether abstract counterexample atr has concrete counterpart upto nth state of the abstract counterexample trace*)
(* FIXME: amba_ahb example spends a lot of time here (ctl_grant_always). is ap collapse not working? *)
fun check_ace' atr I1 RTm(*T1*) state Ric astate h n =
    if (n=0) then SOME [] else
    let
        val _ = dbgTools.DEN dpfx "ca'"(*DBG*)
        val state' = mk_primed_state state
        val _ = dbgTools.DTM (dpfx^"ca'_state'") state'(*DBG*)
        val (st,st') = (strip_pair state,strip_pair state')
        val s = List.map term_to_string2 st
        val ace_states = atr
        val _ = List.app (dbgTools.DTM (dpfx^"ca'_ace_states")) ace_states (*DBG*)
        val ast = pairSyntax.strip_pair astate
        val _ = dbgTools.DTM (dpfx^"ca'_astate") astate(*DBG*)
        val cce_states = List.tabulate(n,fn i => pairSyntax.list_mk_pair(List.map (fn v => mk_bool_var(v^"_"^(Int.toString i))) s))
        val _ = List.app (dbgTools.DTM (dpfx^"ca'_cce_states")) cce_states (*DBG*)
        val vm = getVarmap h
        val _ = List.app (fn (k,v) => (dbgTools.DST (dpfx^"ca'_vm_k: "^k); (*DBG*)
                                       dbgTools.DNM (dpfx^"ca'_vm_v: ") v)) (*DBG*)
                         (Binarymap.listItems vm) (*DBG*)
        val _ = dbgTools.DNM (dpfx^"ca'_bdd_getVarnum") (bdd.getVarnum())(*DBG*)
        val vm' = fst(List.foldl (fn (v,(bm,n)) => let val vs = term_to_string v
                                                   in if isSome (Binarymap.peek(bm,vs))
                                                      then (bm,n)
                                                      else (Binarymap.insert(bm,vs,n),n+1) end)
                                 (vm, listmax(List.map snd (Binarymap.listItems vm))+1)
                                 (List.concat (List.map free_vars cce_states)))
        val _ = List.app (fn (k,v) => (dbgTools.DST (dpfx^"ca'_vm'_k: "^k); (*DBG*)
                                       dbgTools.DNM (dpfx^"ca'_vm'_v: ") v)) (*DBG*)
                         (Binarymap.listItems vm') (*DBG*)
        val _ = if (Binarymap.numItems vm' > bdd.getVarnum()) then bdd.setVarnum (Binarymap.numItems vm') else ()
        val Ib = getBdd(t2tb vm I1)  (*FIXME : this is constructed again and again.  *)
        (*      val init_f = subst (mk_subst st (strip_pair(List.hd cce_states))) I1*)
        val init_f = bdd2cnf vm' (bdd_replace vm' Ib (mk_subst st (strip_pair(List.hd cce_states))))
        val _ = dbgTools.DTM (dpfx^"ca'_init_f") init_f(*DBG*)
        (*val R1 = (if Ric then list_mk_conj else list_mk_disj) (List.map snd T1) *)
        val Rb = getBdd(Binarymap.find(RTm,"."))
        (*val trans_f = if (n=1) then T (* special casing because list_mk_conj [] crashes *)
                      else (list_mk_conj (List.map (fn(stn,stn') =>
                                                      subst ((mk_subst st (strip_pair stn))@(mk_subst st' (strip_pair stn')))
                                                            R1) (List.tl(ListPair.zip(T::cce_states,cce_states)))))*)
        val trans_f = if (n=1) then T (* special casing because list_mk_conj [] crashes *)
                      else (list_mk_conj (List.map (fn(stn,stn') =>
                                                      bdd2cnf vm' (bdd_replace vm' Rb ((mk_subst st (strip_pair stn)) @
                                                                                  (mk_subst st' (strip_pair stn')))))
                                                   (List.tl(ListPair.zip(T::cce_states,cce_states)))))
        val _ = dbgTools.DTM (dpfx^"ca'_trans_f") trans_f(*DBG*)
        val hb = getBdd h
        val abs_f =  list_mk_conj(List.map (fn (astc,cst) => subst (mk_subst st (strip_pair cst))
                                                                  (bdd2cnf vm' (bdd.restrict hb (mk_ass vm ast (strip_pair astc)) )))
                                            (ListPair.zip(ace_states,cce_states)))
        val _ = dbgTools.DTM (dpfx^"ca'_abs_f") abs_f(*DBG*)

        (*FIXME: ideally I should generate a DIMACS file directly from the bdd's and have SAT call the file *)
        (* accoding to Sofiene Tahar, this kind of file-based interface quickly becomes a performance bottleneck
           if you make lots of calls.
           This will be an issue if I am going to do SAT-based predicate abstraction *)
        val satth = if is_F init_f orelse is_F trans_f orelse is_F abs_f
                    then NONE (*FIXME: fix TRUTH below so we can recover a concrete trace from it*)
                    else if is_T init_f andalso is_T trans_f andalso is_T abs_f then SOME TRUTH
                    else let val f = if is_T init_f (* making sure T does not end up in f which is supposed to be in cnf *)
                                     then if is_T trans_f then abs_f
                                          else if is_T abs_f then trans_f else list_mk_conj [trans_f,abs_f]
                                     else if is_T trans_f then if is_T abs_f then init_f else  list_mk_conj [init_f,abs_f]
                                          else if is_T abs_f then list_mk_conj [init_f,trans_f] else list_mk_conj [init_f,trans_f,abs_f]
                             val _ = dbgTools.DTM (dpfx^"ca'_f") f(*DBG*)
                             val _ = dbgTools.CBTM (dpfx^"ca'_f") f(*DBG*)
                             (*val cnf = defCNF.DEF_CNF_CONV f*)
                             val cnf = f
                             val _ = dbgTools.DST (dpfx^"ca'_h1") (*DBG*)
                         in SOME (SAT_PROVE (mk_neg cnf) handle HolSatLib.SAT_cex th => th) end
        val _ = dbgTools.DST (dpfx^"ca'_h2") (*DBG*)
        val ctr = if isSome satth andalso is_imp (concl (valOf satth))(* return concrete trace if one was found else NONE *)
                      then let val l = strip_conj(land(concl (valOf satth)))
                               val bm = List.foldl (fn (v,bm) => if (is_neg v) then Binarymap.insert(bm,dest_neg v,F)
                                                                 else Binarymap.insert(bm,v,T)) (Binarymap.mkDict Term.compare)
                                   (snd(List.partition
                                    (fn v =>
                                     let val vs = (*term_to_string*) (if is_neg v then dest_neg v else v)
                                     in is_genvar vs (*(String.size vs >= 10) andalso
                                         (String.compare(String.substring(vs,0,10),"%%genvar%%")=EQUAL)*) end) l))
                               val _ = List.app (fn (k,v) => (dbgTools.DTM (dpfx^"ca'_bm_k:") k; (*DBG*)
                                                              dbgTools.DTM (dpfx^"ca'_bm_v:") v)) (*DBG*)
                                                (Binarymap.listItems bm) (*DBG*)
                               val cce = List.map (fn stp => (* NotFound can happen if a conc var is in state but not in I1 and R1 *)
                                                      let val l = pairSyntax.strip_pair stp
                                                      in pairSyntax.list_mk_pair (List.map (fn v => Binarymap.find(bm,v)
                                                                                               handle NotFound => F) l) end)
                                         cce_states
                           in SOME cce end
                  else NONE
        val _ = dbgTools.DNM (dpfx^"ca'_ctrsz") (if isSome ctr then List.length (valOf ctr) else ~1) (*DBG*)
        val _ = dbgTools.DEX dpfx "ca'"(*DBG*)
    in ctr end

(* call check_ace' for increasing n until non-SAT happens then return the greatest (i.e. previous) SAT-able path *)
fun check_ace'' atr I1 T1 state Ric astate h n =
    let
        val _ = dbgTools.DEN dpfx "ca''"(*DBG*)
        val _ = dbgTools.DNM (dpfx^"ca''_n") n (*DBG*)
        val ctr = check_ace' atr I1 T1 state Ric astate h n
        val res = if (isSome ctr) then let val ctr' = check_ace'' atr I1 T1 state Ric astate h (n+1)
                                       in if (isSome ctr') then ctr' else ctr end
                  else ctr
        val _ = dbgTools.DEX dpfx "ca''"(*DBG*)
    in res end

(* check whether abstract counterexample atr has concrete counterpart *)
(* if yes return concrete counterpart else return concrete counterpart upto (not including) the state that fails satisfiability *)
(* to check if full counterexample was discovered we can compare the length of the returned counterexample with atr *)
(* atr is output from get_ce. FIXME thmfy ctr *)
fun check_ace atr I1 T1 state Ric astate h =
    let val _ = dbgTools.DEN dpfx "ca"(*DBG*)
        val atrsz = List.length atr
        val _ = dbgTools.DNM (dpfx^"ca_atrsz") atrsz(*DBG*)
        val ctr = check_ace' atr I1 T1 state Ric astate h atrsz (* check if there is a full concrete counterexample *)
        val ctr' = if (isSome ctr) then (dbgTools.DST (dpfx^"crt_ca_conc") (*DBG*); ctr)
                   else check_ace'' atr I1 T1 state Ric astate h 1 (* if not then find longest concrete prefix *)
        val _ = dbgTools.DEX dpfx "ca"(*DBG*)
    in ctr' end

fun contract_vm vl tb =  List.foldl (fn (v,tb) => BddFreevarsContractVarmap v tb) tb vl

(* h as returned by mk_abs_fun. ctr as returned by check_ace, atr as returned by find_trace1
   as_1 is abstract state to be refined. as_2 is the state after as_1 in the ace. h^-1 is inverse of h. ast is symbolic abstract state
   compute bad = <"."> h^-1(as_2) /\ h^-1(as_1)
    i.e. bad \subseteq as_1 and all states in bad and no other in h^-1(as_1) have a transition to h^-1(as_2)
   compute dead = h^-1(as_1)\bad i.e. all other states in h^-1(as_1)
   fially n is just the index of as_1    *)
(* FIXME: can we do without requiring the BDD of M.R? *)
fun ref_abs atr ctr state RTm astate h =
    let val _ = dbgTools.DEN dpfx "ra"(*DBG*)
        val as1 = pairSyntax.strip_pair(List.nth(atr,(List.length ctr)-1))
        val as2 = pairSyntax.strip_pair(List.nth(atr,(List.length ctr)))
        val ast = strip_pair astate
        val vm = getVarmap h
        fun s2res vm st vt = ListPair.zip(List.map (fn v => BddVar true vm v) st,
                                            List.map (fn v => BddCon (Term.compare(v,T)=EQUAL) vm) vt)
        val cS1 = BddRestrict (s2res vm ast as1) h (* h^-1(as_1) *)
        val cS2 = BddRestrict (s2res vm ast as2) h (* h^-1(as_2) *)
        val st = pairSyntax.strip_pair state
        val s = List.map term_to_string2 st
        val st' =  List.map mk_primed_bool_var s
        val s2s' = List.map (fn(v,v') => (BddVar true vm v,BddVar true vm v')) (ListPair.zip(st,st'))
        val bad = BddOp(bdd.And,cS1,BddAppex st' (bdd.And, BddExtendVarmap vm (Binarymap.find(RTm,".")),
                                                  (BddReplace  s2s' cS2)))
        val dead = (BddOp(bdd.And,cS1,BddNot bad))
        val n = List.foldl (fn (v,n) => if Term.compare(v,T)=EQUAL then 2*n else 2*n+1) 0 as1
        val _ = dbgTools.DEX dpfx "ra"(*DBG*)
  in (n,as1,dead,bad) end

fun absCheck_aux I1 ITdf T1 RTm Ric state (apl,ks_def,wfKS_ks) astate hd_def af aksname ath_lem1 ath_lem2 iaf
                 env aenv Ree k (nf,mf) (aksinfo,abs_aks) mu_ic_snd vm (aapl,apsubs) =
    let
        val _ = dbgTools.DEN dpfx "aca"(*DBG*)
        val _ = profTools.bgt (dpfx^"aca") (*PRF*)
        val _ = profTools.bgt (dpfx^"aca_mak") (*PRF*)
        val aksname = if isSome aksname then SOME (valOf(aksname)^"'")
                      else SOME ((despace (term_to_string (lhs(concl ks_def))))^"_aks") (*avoid overwriting prev defs*)
        val (aI1,aT1,aItb,(abpl,aks_def,wfKS_aks,aRTm)) = (* first aks is passed in by absCheck;
                                                             refined ones are created here *)
            if isSome aksinfo then valOf aksinfo
            else mk_abs_ks I1 ITdf RTm state astate Ric af (valOf aksname) (apl,ks_def,wfKS_ks) hd_def
        val aenv = inst [alpha |-> type_of astate] envTools.empty_env_tm
        val _ = dbgTools.DTB (dpfx^"aca_af") af
        val _ = dbgTools.DBD (dpfx^"aca_af_bdd") (getBdd af)
        val _ = dbgTools.DTB (dpfx^"aca_aItb") aItb
        val _ = dbgTools.DBD (dpfx^"aca_aItb_bdd") (getBdd aItb)
        val _ = dbgTools.DTB (dpfx^"aca_hd_aRTm") (snd (hd (Binarymap.listItems aRTm)))
        val _ = dbgTools.DBD (dpfx^"aca_hd_aRTm_bdd") (getBdd (snd (hd (Binarymap.listItems aRTm))))
        val _ = dbgTools.DTB (dpfx^"aca_hd_RTm") (snd (hd (Binarymap.listItems RTm)))
        val _ = dbgTools.DBD (dpfx^"aca_hd_RTm_bdd") (getBdd (snd (hd (Binarymap.listItems RTm))))
        val _ = profTools.ent (dpfx^"aca_mak") (*PRF*)
        val (state',astate',st) = (mk_primed_state state,mk_primed_state astate,strip_pair state)
        val _ = profTools.bgt (dpfx^"aca_maat") (*PRF*)
        val abs_aks = if isSome abs_aks then valOf abs_aks
                      else mk_abs_aks_thm state astate af state' astate' st hd_def ks_def aks_def
        val _ = profTools.ent (dpfx^"aca_maat") (*PRF*)
        val vm'' = PrimitiveBddRules.getVarmap (Binarymap.find(aRTm,"."))
        val _ = profTools.ent (dpfx^"aca") (*PRF*)
        (*FIXME: Since the model has changed (after refinement), we can't pass muCheck the thms from the previous checking;
                 can something from mu_ic_snc be salvaged however? *)
        val ((tb,tbth,ace),mu_ic) = muCheck.muCheck Ree aI1 aT1 astate vm'' Ric (ref NONE) ((SOME af), SOME aItb)
                                                {ks=SOME (abpl,aks_def,wfKS_aks,aRTm,NONE),th=NONE} (nf,mf)
        val _ = profTools.bgt (dpfx^"aca") (*PRF*)
        val _ = profTools.bgt (dpfx^"aca_mact") (*PRF*)
        val cth = if (not (isSome ace)) (* final success theorem *)
                      then let val acm = mk_abs_cons_thm mf (apl,ks_def,wfKS_ks) env aenv hd_def iaf vm
                               val _ = dbgTools.DTH (dpfx^"aca_abs_aks") abs_aks (*DBG*)
                               val _ = dbgTools.DTH (dpfx^"aca_tbth") (valOf tbth) (*DBG*)
                               val _ = dbgTools.CBTH (dpfx^"aca_abs_aks") abs_aks (*DBG*)
                               val _ = dbgTools.CBTH (dpfx^"aca_acm") acm (*DBG*)
                               val _ = dbgTools.CBTH (dpfx^"aca_tbth") (valOf tbth) (*DBG*)
                           in SOME (MP acm (PURE_ONCE_REWRITE_RULE [abs_aks] (valOf tbth))) end
                  else NONE
        val _ = profTools.ent (dpfx^"aca_mact") (*PRF*)
        val _ = profTools.bgt (dpfx^"aca_chkace") (*PRF*)
        val _ = if (isSome cth) then dbgTools.DTH (dpfx^"aca_cth") (valOf cth) else () (*DBG*)
        val cce = if (isSome ace)  (* concrete counter example (or prefix if ace was spurious) *)
                  then check_ace (valOf ace) I1 RTm state Ric astate af
                  else NONE
        val _ = profTools.ent (dpfx^"aca_chkace") (*PRF*)
        val _ = profTools.ent (dpfx^"aca") (*PRF*)
     in if (isSome cth)
        then (dbgTools.DEX dpfx "aca"(*DBG*); ((tb,cth,NONE),#th(mu_ic))) (* success *)
        else
            if (List.length (valOf cce)) = (List.length (valOf ace))
            then (dbgTools.DEX dpfx "aca"(*DBG*); ((tb,NONE,cce),#th(mu_ic))) (*failure*)
            else let val _ = profTools.bgt (dpfx^"aca") (*PRF*)
                     val _ = profTools.bgt (dpfx^"aca_ref") (*PRF*)
                     val (idx,as1,dead,bad) = ref_abs (valOf ace) (valOf cce) state RTm astate af (* refine *)
                     val (af,ath_lem1,astate,hd_def,iaf)=
                         mk_ref_abs_fun af state astate ks_def ath_lem1 ath_lem2 hd_def idx as1 dead bad k
                     val _ = profTools.ent (dpfx^"aca_ref") (*PRF*)
                     val _ = profTools.ent (dpfx^"aca") (*PRF*)
               in absCheck_aux I1 ITdf T1 RTm Ric state (apl,ks_def,wfKS_ks) astate
                   hd_def af aksname ath_lem1 ath_lem2 iaf env aenv Ree (k+1) (nf,mf) (NONE,NONE) (#th(mu_ic)) vm
                   (aapl,apsubs) end
    end

(* property independent theorems and data that needs to be initialised only once per model *)
fun init_abs I1 T1 state Ric vm (aapl,apsubs) ksname (ic,cc) =
    let
        val _ = dbgTools.DEN dpfx "ia"  (*DBG*)
        val _ = profTools.bgt (dpfx^"ia") (*PRF*)
        val _ = profTools.bgt (dpfx^"ia_mck") (*PRF*)
        val (apl,ks_def,wfKS_ks,RTm,ITdf) =  if isSome (#ks(#mu(ic))) then valOf (#ks(#mu(ic)))
                                             else mk_wfKS I1 T1 NONE state vm Ric aapl NONE ksname
        val _ = profTools.ent (dpfx^"ia_mck") (*PRF*)
        val _ = profTools.bgt (dpfx^"ia_maf") (*PRF*)
        val hname =  SOME ((despace (term_to_string (lhs(concl ks_def))))^"_af") (* so ctl and mu names don't collide *)
        val ((astate,af),state,env,aenv,Ree,k,unwind_thm,hR_defs_,hd_def) =
            if isSome (#abs_df(cc)) then valOf(#abs_df(cc))
            else let val (astate,unwind_thm,hR_defs_,hd_def,af) = mk_abs_fun (valOf aapl) vm state hname
                     val env = inst [alpha |-> type_of state] envTools.empty_env_tm
                     val aenv = inst [alpha |-> type_of astate] envTools.empty_env_tm
                     val Ree = Array.fromList []
                     val k = Real.round(Math.pow(2.0,Real.fromInt(List.length (strip_pair astate))))
                 in ((astate,af),state,env,aenv,Ree,k,unwind_thm,hR_defs_,hd_def) end
        val _ = profTools.ent (dpfx^"ia_maf") (*PRF*)
        val _ = profTools.bgt (dpfx^"ia_mak") (*PRF*)
        val aksname =  SOME ((despace (term_to_string (lhs(concl ks_def))))^"_aks") (* so ctl and mu names don't collide *)
        val (aI1,aT1,aItb,(abpl,aks_def,wfKS_aks,aRTm)) =
            if isSome (#ks(ic)) then valOf (#ks(ic))
            else mk_abs_ks I1 ITdf RTm state astate Ric af (valOf aksname) (apl,ks_def,wfKS_ks) hd_def
        val _ = profTools.ent (dpfx^"ia_mak") (*PRF*)
        val _ = profTools.bgt (dpfx^"ia_maat") (*PRF*)
        val (state',astate',st) = (mk_primed_state state,mk_primed_state astate,strip_pair state)
        val abs_aks = mk_abs_aks_thm state astate af state' astate' st hd_def ks_def aks_def
        val _ = profTools.ent (dpfx^"ia_maat") (*PRF*)
        val _ = profTools.bgt (dpfx^"ia_miaf") (*PRF*)
        val ksname = lhs(concl ks_def)
        val hnc = rator(lhs(snd(strip_forall(concl hd_def))))
        val (ath_lem1,ath_lem2,iaf) = mk_is_abs_fun_thm ksname hnc af state astate hR_defs_ unwind_thm (apl,ks_def,wfKS_ks) hd_def
        val _ = profTools.ent (dpfx^"ia_miaf") (*PRF*)
        val _ = profTools.ent (dpfx^"ia") (*PRF*)
        val _ = dbgTools.DEX dpfx "ia"  (*DBG*)
    in ((apl,ks_def,wfKS_ks,RTm,ITdf),(aI1,aT1,aItb,(abpl,aks_def,wfKS_aks,aRTm)),
                     ((astate,af),state,env,aenv,Ree,k,unwind_thm,hR_defs_,hd_def),
                      (ath_lem1,ath_lem2,abs_aks,iaf)) end

(* so far the res tells us that the collapsed (i.e. propositional subterms folded into single AP's ) property holds in the concrete ks*)
(* now prove that non-collapsed property holds as well (since that is what the user should see) *)
fun finalise (apl,ks_def,wfKS_ks,ITdf) apsubs state mf (*msa*) (tb,th,tr) =
    if isSome th
    then let val _ = dbgTools.DEN dpfx "fin"(*DBG*)
             val _ = profTools.bgt (dpfx^"fin") (*PRF*)
             val subs = List.map dest_subst apsubs
             val faps =  HOLset.addList(HOLset.empty Term.compare,find_APs mf)
             val fsubs = List.filter (((curry HOLset.member) faps) o snd) subs
             val (gmf,aap) = ListPair.unzip fsubs
             val ksname = lhs(concl ks_def)
             val _ = dbgTools.DTM (dpfx^"fin_ksname") ksname(*DBG*)
             val (p_ty,s_ty) = get_types ksname
             val is_prop = List.map (prove_is_prop p_ty)  gmf
             val _ = List.app (dbgTools.DTH (dpfx^"fin_is_prop")) is_prop (*DBG*)
             val _ = dbgTools.CBTHL (dpfx^"fin_is_prop") is_prop (*DBG*)
             val lm = CONV_RULE (LHS_CONV (lzGEN_PALPHA_CONV state)) (INST_TYPE [alpha|->s_ty] (SPEC T FORALL_SIMP))
             val _ = dbgTools.DTH (dpfx^"fin_lm") lm(*DBG*)
             val _ = dbgTools.CBTH (dpfx^"fin_lm") lm (*DBG*)
             val apth = MATCH_MP AP_SUBST_MODEL wfKS_ks
             val _ = dbgTools.DTH (dpfx^"fin_apth") apth(*DBG*)
             val apth = CONV_RULE (STRIP_QUANT_CONV (RAND_CONV (LAND_CONV (lzGEN_PALPHA_CONV state)))) apth
             val _ = dbgTools.DTH (dpfx^"fin_apth2") apth(*DBG*)
             val _ = dbgTools.CBTH (dpfx^"fin_apth") apth (*DBG*)
             val th = valOf th
             val _ = dbgTools.DTH (dpfx^"fin_th") th(*DBG*)
             val env = el 3 (snd(strip_comb(snd(strip_forall(concl th)))))
             val _ = dbgTools.DTM (dpfx^"fin_env") env(*DBG*)
             val msthl = List.map (fn th => MATCH_MP (CONV_RULE lzFORALL_IMP_CONV (ISPECL [state,ksname] th)) wfKS_ks)
                                  [MU_SAT_T,MU_SAT_F,MU_SAT_NEG,MU_SAT_CONJ,MU_SAT_DISJ,MU_SAT_AP]
             val _ = List.app (dbgTools.DTH (dpfx^"fin_msthl")) msthl (*DBG*)
             val _ = dbgTools.CBTHL (dpfx^"fin_msthl") msthl (*DBG*)
             val Lth = mk_Lth ks_def
             val _ = dbgTools.DTH (dpfx^"fin_Lth") Lth(*DBG*)
             val _ = dbgTools.CBTH (dpfx^"fin_Lth") Lth (*DBG*)
             val _ = dbgTools.CBTH (dpfx^"fin_wfKS_ks") wfKS_ks (*DBG*)
             val _ = dbgTools.CBTM (dpfx^"fin_state") state (*DBG*)
             val res = List.foldl (fn ((ip,(g,ap)),th) =>
                                      let val mf = hd(snd(strip_comb(snd(strip_forall(concl th)))))
                                          val _ = dbgTools.DTM (dpfx^"fin_mf") mf(*DBG*)
                                          val _ = dbgTools.CBTM (dpfx^"fin_mf") mf (*DBG*)
                                          val _ = dbgTools.DTM (dpfx^"fin_g") g(*DBG*)
                                          val _ = dbgTools.CBTM (dpfx^"fin_g") g (*DBG*)
                                          val _ = dbgTools.DTM (dpfx^"fin_ap") ap(*DBG*)
                                          val _ = dbgTools.CBTM (dpfx^"fin_ap") ap (*DBG*)
                                          val _ = dbgTools.DTM (dpfx^"fin_env") env(*DBG*)
                                          val _ = dbgTools.CBTM (dpfx^"fin_env") env (*DBG*)
                                          val sapth = ISPECL [mf,g,rand ap,env] apth
                                          val _ = dbgTools.DTH (dpfx^"fin_sapth") sapth(*DBG*)
                                          val _ = dbgTools.CBTH (dpfx^"fin_sapth") sapth (*DBG*)
                                          val _ = dbgTools.CBTM (dpfx^"fin_apeqgl") (land (rand (concl sapth))) (*DBG*)
                                          val apeq =  EQT_ELIM ((REWRITE_CONV (Lth::wfKS_ks::msthl)
                                                                    THENC (DEPTH_CONV PBETA_CONV)
                                                                    THENC REWRITE_CONV [lm]) (land (rand (concl sapth))))
                                          val _ = dbgTools.DTH (dpfx^"fin_apeq") apeq(*DBG*)
                                          val _ = dbgTools.CBTH (dpfx^"fin_apeq") apeq (*DBG*)
                                          val sapth2 = MATCH_MP (MATCH_MP sapth ip) apeq
                                          val _ = dbgTools.DTH (dpfx^"fin_sapth2") sapth2(*DBG*)
                                          val _ = dbgTools.CBTH (dpfx^"fin_sapth2") sapth2 (*DBG*)
                                      in REWRITE_RULE [sapth2,AP_SUBST_def] th end)
                                  th  (ListPair.zip(is_prop,fsubs))
             val _ = dbgTools.DTH (dpfx^"fin_res") res(*DBG*)
             val restb = tb
             val _ = profTools.ent (dpfx^"fin") (*PRF*)
             val _ = dbgTools.DEX dpfx "fin" (*DBG*)
         in (restb,SOME res,tr) end
    else  (tb,th,tr)

(* given concrete model M and a formula f, returns M |= f where the model checking has been done on an abstracted version of M *)
(* NOTE: this abstraction framework is only for universal properties; the second test for no aapl checks if hct.maA returned apl=NONE *)
(* this function just computes the init data (or picks it from the ic); the real action takes place in absCheck_aux *)
fun absCheck I1 T1 state Ric vm ksname (ic:internalCacheTools.abs_ic,cc:internalCacheTools.common_ic) (nf,mf) (aapl,apsubs) =
    let
        val _ = dbgTools.DEN dpfx "ac"(*DBG*)
        val res = if is_existential mf orelse (not (isSome aapl))
                  then let val _ = dbgTools.DST (dpfx^"ac_ No abstraction")  (*DBG*)
                           val _ = profTools.bgt (dpfx^"ac_no")(*PRF*)
                           val (apl,ks_def,wfKS_ks,RTm,ITdf) = if isSome (#ks(#mu(ic))) then valOf (#ks(#mu(ic)))
                                                               else mk_wfKS I1 T1 NONE state vm Ric NONE NONE ksname
                           val _ = profTools.ent (dpfx^"ac_no") (*PRF*)
                           val (res,mu_ic) = muCheck (Array.fromList []) I1 T1 state vm Ric (ref NONE) (NONE,NONE)
                                                     {ks=SOME (apl,ks_def,wfKS_ks,RTm,ITdf),th= #th(#mu(ic))} (nf,mf)
                           val _ = dbgTools.DST (dpfx^"ac_ absCheck done (without abstraction)")  (*DBG*)
                       in (res,({mth= #mth(ic),th= #th(ic),ks= #ks(ic),mu={ks= #ks(mu_ic),th= #th(mu_ic)}},cc)) end
                  else let val _ = dbgTools.DST (dpfx^"ac_ Abstracting")  (*DBG*)
                           val _ = profTools.bgt (dpfx^"ac_yes")(*PRF*)
                           val ((apl,ks_def,wfKS_ks,RTm,ITdf),(aI1,aT1,aItb,(abpl,aks_def,wfKS_aks,aRTm)),
                                ((astate,af),state,env,aenv,Ree,k,abst_def,hR_defs_,hd_def),
                                (ath_lem1,ath_lem2,abs_aks,iaf)) =
                               if isSome (#th(ic))
                               then (valOf(#ks(#mu(ic))),valOf(#ks(ic)),valOf(#abs_df(cc)),valOf(#th(ic)))
                               else init_abs I1 T1 state Ric vm (aapl,apsubs) ksname (ic,cc)
                           val mf2 = subst apsubs mf (*FIXME: cache the substs and use that cache somehow *)
                           val (res,mu_ic_snd) = absCheck_aux I1 ITdf T1 RTm Ric state (apl,ks_def,wfKS_ks)
                                                              astate hd_def af NONE ath_lem1 ath_lem2 iaf
                                                              env aenv Ree k (nf,mf2)
                                                              (SOME (aI1,aT1,aItb,(abpl,aks_def,wfKS_aks,aRTm)),SOME abs_aks) (#mth(ic))
                                                              vm (aapl,apsubs)
                           val res = finalise (apl,ks_def,wfKS_ks,ITdf) apsubs state mf2 res
                           val _ = profTools.ent (dpfx^"ac_yes") (*PRF*)
                           val _ = dbgTools.DST (dpfx^"ac_ absCheck done (with abstraction)")  (*DBG*)
                       in (res,
                           ({mu={ks=SOME (apl,ks_def,wfKS_ks,RTm,ITdf),th= #th(#mu(ic))},
                             mth= mu_ic_snd,
                             ks=SOME(aI1,aT1,aItb,(abpl,aks_def,wfKS_aks,aRTm)),
                             th=SOME(ath_lem1,ath_lem2,abs_aks,iaf)},
                            {abs_df=SOME((astate,af),state,env,aenv,Ree,k,abst_def,hR_defs_,hd_def)}))
                       end
        val _ = dbgTools.DEX dpfx "ac" (*DBG*)
    in res end

end
end
