open Lib;;
open Fusion;;
open Basics;;
open Hl_parser;;
open Equal;;
open Bool;;
open Drule;;
open Simp;;
open Theorems;;
open Tactics;;

let cONJ_ACI_RULE =
  let rec mk_fun th fn =
    let tm = concl th in
    if is_conj tm then
      let th1,th2 = cONJ_PAIR th in
      mk_fun th1 (mk_fun th2 fn)
    else (tm |-> th) fn
  and use_fun fn tm =
    if is_conj tm then
      let l,r = dest_conj tm in cONJ (use_fun fn l) (use_fun fn r)
    else apply fn tm in
  fun fm ->
    let p,p' = dest_eq fm in
    if p = p' then rEFL p else
    let th = use_fun (mk_fun (aSSUME p) undefined) p'
    and th' = use_fun (mk_fun (aSSUME p') undefined) p in
    iMP_ANTISYM_RULE (dISCH_ALL th) (dISCH_ALL th');;

let dISJ_ACI_RULE =
  let pth_left = uNDISCH(Sequent ([],parse_term "~(a \\/ b) ==> ~a"))
  and pth_right = uNDISCH(Sequent ([],parse_term "~(a \\/ b) ==> ~b"))
  and pth = repeat uNDISCH (Sequent ([],parse_term "~a ==> ~b ==> ~(a \\/ b)"))
  and pth_neg = uNDISCH(Sequent ([],parse_term "(~a <=> ~b) ==> (a <=> b)"))
  and a_tm = parse_term "a:bool" and b_tm = parse_term "b:bool" in
  let nOT_DISJ_PAIR th =
    let p,q = dest_disj(rand(concl th)) in
    let ilist = [p,a_tm; q,b_tm] in
    pROVE_HYP th (iNST ilist pth_left),
    pROVE_HYP th (iNST ilist pth_right)
  and nOT_DISJ th1 th2 =
    let th3 = iNST [rand(concl th1),a_tm; rand(concl th2),b_tm] pth in
    pROVE_HYP th1 (pROVE_HYP th2 th3) in
  let rec mk_fun th fn =
    let tm = rand(concl th) in
    if is_disj tm then
      let th1,th2 = nOT_DISJ_PAIR th in
      mk_fun th1 (mk_fun th2 fn)
    else (tm |-> th) fn
  and use_fun fn tm =
    if is_disj tm then
      let l,r = dest_disj tm in nOT_DISJ (use_fun fn l) (use_fun fn r)
    else apply fn tm in
  fun fm ->
    let p,p' = dest_eq fm in
    if p = p' then rEFL p else
    let th = use_fun (mk_fun (aSSUME(mk_neg p)) undefined) p'
    and th' = use_fun (mk_fun (aSSUME(mk_neg p')) undefined) p in
    let th1 = iMP_ANTISYM_RULE (dISCH_ALL th) (dISCH_ALL th') in
    pROVE_HYP th1 (iNST [p,a_tm; p',b_tm] pth_neg);;

let cONJ_CANON_CONV tm =
  let tm' = list_mk_conj(setify(conjuncts tm)) in
  cONJ_ACI_RULE(mk_eq(tm,tm'));;

let dISJ_CANON_CONV tm =
  let tm' = list_mk_disj(setify(disjuncts tm)) in
  dISJ_ACI_RULE(mk_eq(tm,tm'));;

let (gEN_NNF_CONV:bool->conv*(term->thm*thm)->conv) =
  let and_tm = parse_term "(/\\)"
  and or_tm = parse_term "(\\/)"
  and not_tm = parse_term "(~)"
  and pth_not_not = Sequent([],parse_term "~ ~ p = p")
  and pth_not_and = Sequent([],parse_term "~(p /\\ q) <=> ~p \\/ ~q")
  and pth_not_or = Sequent([],parse_term "~(p \\/ q) <=> ~p /\\ ~q")
  and pth_imp = Sequent([],parse_term "p ==> q <=> ~p \\/ q")
  and pth_not_imp = Sequent([],parse_term "~(p ==> q) <=> p /\\ ~q")
  and pth_eq = Sequent([],parse_term "(p <=> q) <=> p /\\ q \\/ ~p /\\ ~q")
  and pth_not_eq = Sequent([],parse_term "~(p <=> q) <=> p /\\ ~q \\/ ~p /\\ q")
  and pth_eq' = Sequent([],parse_term "(p <=> q) <=> (p \\/ ~q) /\\ (~p \\/ q)")
  and pth_not_eq' = Sequent([],parse_term "~(p <=> q) <=> (p \\/ q) /\\ (~p \\/ ~q)")
  and [pth_not_forall; pth_not_exists; pth_not_exu] =
   (cONJUNCTS (Sequent ([], parse_term
   "(~((!) P) <=> ?x:A. ~(P x)) /\\
     (~((?) P) <=> !x:A. ~(P x)) /\\
     (~((?!) P) <=> (!x:A. ~(P x)) \\/ ?x y. P x /\\ P y /\\ ~(y = x))")))
  and pth_exu = (Sequent ([], parse_term
   "((?!) P) <=> (?x:A. P x) /\\ !x y. ~(P x) \\/ ~(P y) \\/ (y = x)"))
  and p_tm = parse_term "p:bool" and q_tm = parse_term "q:bool" in
  let rec nNF_DCONV cf baseconvs tm =
    match tm with
      Comb(Comb(Const(2,_),l),r) ->
          let th_lp,th_ln = nNF_DCONV cf baseconvs l
          and th_rp,th_rn = nNF_DCONV cf baseconvs r in
          mK_COMB(aP_TERM and_tm th_lp,th_rp),
          tRANS (iNST [l,p_tm; r,q_tm] pth_not_and)
                (mK_COMB(aP_TERM or_tm th_ln,th_rn))
    | Comb(Comb(Const(6,_),l),r) ->
          let th_lp,th_ln = nNF_DCONV cf baseconvs l
          and th_rp,th_rn = nNF_DCONV cf baseconvs r in
          mK_COMB(aP_TERM or_tm th_lp,th_rp),
          tRANS (iNST [l,p_tm; r,q_tm] pth_not_or)
                (mK_COMB(aP_TERM and_tm th_ln,th_rn))
    | Comb(Comb(Const(3,_),l),r) ->
          let th_lp,th_ln = nNF_DCONV cf baseconvs l
          and th_rp,th_rn = nNF_DCONV cf baseconvs r in
          tRANS (iNST [l,p_tm; r,q_tm] pth_imp)
                (mK_COMB(aP_TERM or_tm th_ln,th_rp)),
          tRANS (iNST [l,p_tm; r,q_tm] pth_not_imp)
                (mK_COMB(aP_TERM and_tm th_lp,th_rn))
    | Comb(Comb(Const(0,Tyapp("fun",Tyapp("bool",_)::_)),l),r) ->
          let th_lp,th_ln = nNF_DCONV cf baseconvs l
          and th_rp,th_rn = nNF_DCONV cf baseconvs r in
          if cf then
            tRANS (iNST [l,p_tm; r,q_tm] pth_eq')
                  (mK_COMB(aP_TERM and_tm (mK_COMB(aP_TERM or_tm th_lp,th_rn)),
                           mK_COMB(aP_TERM or_tm th_ln,th_rp))),
            tRANS (iNST [l,p_tm; r,q_tm] pth_not_eq')
                  (mK_COMB(aP_TERM and_tm (mK_COMB(aP_TERM or_tm th_lp,th_rp)),
                           mK_COMB(aP_TERM or_tm th_ln,th_rn)))
          else
            tRANS (iNST [l,p_tm; r,q_tm] pth_eq)
                  (mK_COMB(aP_TERM or_tm (mK_COMB(aP_TERM and_tm th_lp,th_rp)),
                           mK_COMB(aP_TERM and_tm th_ln,th_rn))),
            tRANS (iNST [l,p_tm; r,q_tm] pth_not_eq)
                  (mK_COMB(aP_TERM or_tm (mK_COMB(aP_TERM and_tm th_lp,th_rn)),
                           mK_COMB(aP_TERM and_tm th_ln,th_rp)))
    | Comb(Const(4,Tyapp("fun",Tyapp("fun",ty::_)::_)) as q,
           (Abs(x,t) as bod)) ->
          let th_p,th_n = nNF_DCONV true baseconvs t in
          aP_TERM q (aBS x th_p),
          let th1 = iNST [bod,mk_var("P",mk_fun_ty ty bool_ty)]
                         (iNST_TYPE [ty,aty] pth_not_forall)
          and th2 = tRANS (aP_TERM not_tm (bETA(mk_comb(bod,x)))) th_n in
          tRANS th1 (mK_EXISTS x th2)
    | Comb(Const(5,Tyapp("fun",Tyapp("fun",ty::_)::_)) as q,
           (Abs(x,t) as bod)) ->
          let th_p,th_n = nNF_DCONV cf baseconvs t in
          aP_TERM q (aBS x th_p),
          let th1 = iNST [bod,mk_var("P",mk_fun_ty ty bool_ty)]
                         (iNST_TYPE [ty,aty] pth_not_exists)
          and th2 = tRANS (aP_TERM not_tm (bETA(mk_comb(bod,x)))) th_n in
          tRANS th1 (mK_FORALL x th2)
    | Comb(Const(9,Tyapp("fun",Tyapp("fun",ty::_)::_)),
           (Abs(x,t) as bod)) ->
          let y = variant (x::frees t) x
          and th_p,th_n = nNF_DCONV cf baseconvs t in
          let eq = mk_eq(y,x) in
          let eth_p,eth_n = baseconvs eq
          and bth = bETA (mk_comb(bod,x))
          and bth' = bETA_CONV(mk_comb(bod,y)) in
          let th_p' = iNST [y,x] th_p and th_n' = iNST [y,x] th_n in
          let th1 = iNST [bod,mk_var("P",mk_fun_ty ty bool_ty)]
                         (iNST_TYPE [ty,aty] pth_exu)
          and th1' = iNST [bod,mk_var("P",mk_fun_ty ty bool_ty)]
                          (iNST_TYPE [ty,aty] pth_not_exu)
          and th2 =
            mK_COMB(aP_TERM and_tm
                        (mK_EXISTS x (tRANS bth th_p)),
                    mK_FORALL x (mK_FORALL y
                     (mK_COMB(aP_TERM or_tm (tRANS (aP_TERM not_tm bth) th_n),
                              mK_COMB(aP_TERM or_tm
                                    (tRANS (aP_TERM not_tm bth') th_n'),
                                      eth_p)))))
          and th2' =
            mK_COMB(aP_TERM or_tm
                        (mK_FORALL x (tRANS (aP_TERM not_tm bth) th_n)),
                    mK_EXISTS x (mK_EXISTS y
                     (mK_COMB(aP_TERM and_tm (tRANS bth th_p),
                              mK_COMB(aP_TERM and_tm (tRANS bth' th_p'),
                                      eth_n))))) in
          tRANS th1 th2,tRANS th1' th2'
    | Comb(Const(8,_),t) ->
          let th1,th2 = nNF_DCONV cf baseconvs t in
          th2,tRANS (iNST [t,p_tm] pth_not_not) th1
    | _ -> try baseconvs tm
           with Failure _ -> rEFL tm,rEFL(mk_neg tm) in
  let rec nNF_CONV cf (base1,base2 as baseconvs) tm =
    match tm with
      Comb(Comb(Const(2,_),l),r) ->
          let th_lp = nNF_CONV cf baseconvs l
          and th_rp = nNF_CONV cf baseconvs r in
          mK_COMB(aP_TERM and_tm th_lp,th_rp)
    | Comb(Comb(Const(6,_),l),r) ->
          let th_lp = nNF_CONV cf baseconvs l
          and th_rp = nNF_CONV cf baseconvs r in
          mK_COMB(aP_TERM or_tm th_lp,th_rp)
    | Comb(Comb(Const(3,_),l),r) ->
          let th_ln = nNF_CONV' cf baseconvs l
          and th_rp = nNF_CONV cf baseconvs r in
          tRANS (iNST [l,p_tm; r,q_tm] pth_imp)
                (mK_COMB(aP_TERM or_tm th_ln,th_rp))
    | Comb(Comb(Const(0,Tyapp("fun",Tyapp("bool",_)::_)),l),r) ->
          let th_lp,th_ln = nNF_DCONV cf base2 l
          and th_rp,th_rn = nNF_DCONV cf base2 r in
          if cf then
            tRANS (iNST [l,p_tm; r,q_tm] pth_eq')
                  (mK_COMB(aP_TERM and_tm (mK_COMB(aP_TERM or_tm th_lp,th_rn)),
                           mK_COMB(aP_TERM or_tm th_ln,th_rp)))
          else
            tRANS (iNST [l,p_tm; r,q_tm] pth_eq)
                  (mK_COMB(aP_TERM or_tm (mK_COMB(aP_TERM and_tm th_lp,th_rp)),
                           mK_COMB(aP_TERM and_tm th_ln,th_rn)))
    | Comb(Const(4,Tyapp("fun",Tyapp("fun",ty::_)::_)) as q,
           (Abs(x,t))) ->
          let th_p = nNF_CONV true baseconvs t in
          aP_TERM q (aBS x th_p)
    | Comb(Const(5,Tyapp("fun",Tyapp("fun",ty::_)::_)) as q,
           (Abs(x,t))) ->
          let th_p = nNF_CONV cf baseconvs t in
          aP_TERM q (aBS x th_p)
    | Comb(Const(9,Tyapp("fun",Tyapp("fun",ty::_)::_)),
           (Abs(x,t) as bod)) ->
          let y = variant (x::frees t) x
          and th_p,th_n = nNF_DCONV cf base2 t in
          let eq = mk_eq(y,x) in
          let eth_p,eth_n = base2 eq
          and bth = bETA (mk_comb(bod,x))
          and bth' = bETA_CONV(mk_comb(bod,y)) in
          let th_n' = iNST [y,x] th_n in
          let th1 = iNST [bod,mk_var("P",mk_fun_ty ty bool_ty)]
                         (iNST_TYPE [ty,aty] pth_exu)
          and th2 =
            mK_COMB(aP_TERM and_tm
                        (mK_EXISTS x (tRANS bth th_p)),
                    mK_FORALL x (mK_FORALL y
                     (mK_COMB(aP_TERM or_tm (tRANS (aP_TERM not_tm bth) th_n),
                              mK_COMB(aP_TERM or_tm
                                    (tRANS (aP_TERM not_tm bth') th_n'),
                                      eth_p))))) in
          tRANS th1 th2
    | Comb(Const(8,_),t) -> nNF_CONV' cf baseconvs t
    | _ -> try base1 tm with Failure _ -> rEFL tm
  and nNF_CONV' cf (base1,base2 as baseconvs) tm =
    match tm with
      Comb(Comb(Const(2,_),l),r) ->
          let th_ln = nNF_CONV' cf baseconvs l
          and th_rn = nNF_CONV' cf baseconvs r in
          tRANS (iNST [l,p_tm; r,q_tm] pth_not_and)
                (mK_COMB(aP_TERM or_tm th_ln,th_rn))
    | Comb(Comb(Const(6,_),l),r) ->
          let th_ln = nNF_CONV' cf baseconvs l
          and th_rn = nNF_CONV' cf baseconvs r in
          tRANS (iNST [l,p_tm; r,q_tm] pth_not_or)
                (mK_COMB(aP_TERM and_tm th_ln,th_rn))
    | Comb(Comb(Const(3,_),l),r) ->
          let th_lp = nNF_CONV cf baseconvs l
          and th_rn = nNF_CONV' cf baseconvs r in
          tRANS (iNST [l,p_tm; r,q_tm] pth_not_imp)
                (mK_COMB(aP_TERM and_tm th_lp,th_rn))
    | Comb(Comb(Const(0,Tyapp("fun",Tyapp("bool",_)::_)),l),r) ->
          let th_lp,th_ln = nNF_DCONV cf base2 l
          and th_rp,th_rn = nNF_DCONV cf base2 r in
          if cf then
            tRANS (iNST [l,p_tm; r,q_tm] pth_not_eq')
                  (mK_COMB(aP_TERM and_tm (mK_COMB(aP_TERM or_tm th_lp,th_rp)),
                           mK_COMB(aP_TERM or_tm th_ln,th_rn)))
          else
            tRANS (iNST [l,p_tm; r,q_tm] pth_not_eq)
                  (mK_COMB(aP_TERM or_tm (mK_COMB(aP_TERM and_tm th_lp,th_rn)),
                           mK_COMB(aP_TERM and_tm th_ln,th_rp)))
    | Comb(Const(4,Tyapp("fun",Tyapp("fun",ty::_)::_)),
           (Abs(x,t) as bod)) ->
          let th_n = nNF_CONV' cf baseconvs t in
          let th1 = iNST [bod,mk_var("P",mk_fun_ty ty bool_ty)]
                         (iNST_TYPE [ty,aty] pth_not_forall)
          and th2 = tRANS (aP_TERM not_tm (bETA(mk_comb(bod,x)))) th_n in
          tRANS th1 (mK_EXISTS x th2)
    | Comb(Const(5 ,Tyapp("fun",Tyapp("fun",ty::_)::_)),
           (Abs(x,t) as bod)) ->
          let th_n = nNF_CONV' true baseconvs t in
          let th1 = iNST [bod,mk_var("P",mk_fun_ty ty bool_ty)]
                         (iNST_TYPE [ty,aty] pth_not_exists)
          and th2 = tRANS (aP_TERM not_tm (bETA(mk_comb(bod,x)))) th_n in
          tRANS th1 (mK_FORALL x th2)
    | Comb(Const(9,Tyapp("fun",Tyapp("fun",ty::_)::_)),
           (Abs(x,t) as bod)) ->
          let y = variant (x::frees t) x
          and th_p,th_n = nNF_DCONV cf base2 t in
          let eq = mk_eq(y,x) in
          let eth_p,eth_n = base2 eq
          and bth = bETA (mk_comb(bod,x))
          and bth' = bETA_CONV(mk_comb(bod,y)) in
          let th_p' = iNST [y,x] th_p in
          let th1' = iNST [bod,mk_var("P",mk_fun_ty ty bool_ty)]
                          (iNST_TYPE [ty,aty] pth_not_exu)
          and th2' =
            mK_COMB(aP_TERM or_tm
                        (mK_FORALL x (tRANS (aP_TERM not_tm bth) th_n)),
                    mK_EXISTS x (mK_EXISTS y
                     (mK_COMB(aP_TERM and_tm (tRANS bth th_p),
                              mK_COMB(aP_TERM and_tm (tRANS bth' th_p'),
                                      eth_n))))) in
          tRANS th1' th2'
    | Comb(Const(8,_),t) ->
          let th1 = nNF_CONV cf baseconvs t in
          tRANS (iNST [t,p_tm] pth_not_not) th1
    | _ -> let tm' = mk_neg tm in try base1 tm' with Failure _ -> rEFL tm' in
  nNF_CONV;;

let nNF_CONV =
  (gEN_NNF_CONV false (aLL_CONV,fun t -> rEFL t,rEFL(mk_neg t)) :conv);;

let nNFC_CONV =
  (gEN_NNF_CONV true (aLL_CONV,fun t -> rEFL t,rEFL(mk_neg t)) :conv);;

let sKOLEM_CONV =
  tHENC
  (gEN_REWRITE_CONV tOP_DEPTH_CONV
   [eXISTS_OR_THM; lEFT_EXISTS_AND_THM; rIGHT_EXISTS_AND_THM;
    fORALL_AND_THM; lEFT_FORALL_OR_THM; rIGHT_FORALL_OR_THM;
    fORALL_SIMP; eXISTS_SIMP])
  (gEN_REWRITE_CONV rEDEPTH_CONV
   [rIGHT_AND_EXISTS_THM;
    lEFT_AND_EXISTS_THM;
    oR_EXISTS_THM;
    rIGHT_OR_EXISTS_THM;
    lEFT_OR_EXISTS_THM;
    sKOLEM_THM]);;


let pRENEX_CONV =
  gEN_REWRITE_CONV rEDEPTH_CONV
   [aND_FORALL_THM; lEFT_AND_FORALL_THM; rIGHT_AND_FORALL_THM;
    lEFT_OR_FORALL_THM; rIGHT_OR_FORALL_THM;
    oR_EXISTS_THM; lEFT_OR_EXISTS_THM; rIGHT_OR_EXISTS_THM;
    lEFT_AND_EXISTS_THM; rIGHT_AND_EXISTS_THM];;

let wEAK_DNF_CONV,dNF_CONV =
  let pth1 = Sequent([], parse_term "a /\\ (b \\/ c) <=> a /\\ b \\/ a /\\ c")
  and pth2 = Sequent([], parse_term "(a \\/ b) /\\ c <=> a /\\ c \\/ b /\\ c")
  and a_tm = parse_term "a:bool" and b_tm = parse_term "b:bool" and c_tm = parse_term "c:bool" in
  let rec distribute tm =
    match tm with
      Comb(Comb(Const(2,_),a),Comb(Comb(Const(6,_),b),c)) ->
          let th = iNST [a,a_tm; b,b_tm; c,c_tm] pth1 in
          tRANS th (bINOP_CONV distribute (rand(concl th)))
    | Comb(Comb(Const(2,_),Comb(Comb(Const(6,_),a),b)),c) ->
          let th = iNST [a,a_tm; b,b_tm; c,c_tm] pth2 in
          tRANS th (bINOP_CONV distribute (rand(concl th)))
    | _ -> rEFL tm in
  let strengthen =
    tHENC (dEPTH_BINOP_CONV (parse_term "(\\/)") cONJ_CANON_CONV) dISJ_CANON_CONV in
  let rec weakdnf tm =
    match tm with
      Comb(Const(4,_),Abs(_,_))
    | Comb(Const(5,_),Abs(_,_)) -> bINDER_CONV weakdnf tm
    | Comb(Comb(Const(6,_),_),_) -> bINOP_CONV weakdnf tm
    | Comb(Comb(Const(2,_) as op,l),r) ->
          let th = mK_COMB(aP_TERM op (weakdnf l),weakdnf r) in
          tRANS th (distribute(rand(concl th)))
    | _ -> rEFL tm
  and substrongdnf tm =
    match tm with
      Comb(Const(4,_),Abs(_,_))
    | Comb(Const(5,_),Abs(_,_)) -> bINDER_CONV strongdnf tm
    | Comb(Comb(Const(6,_),_),_) -> bINOP_CONV substrongdnf tm
    | Comb(Comb(Const(2,_) as op,l),r) ->
          let th = mK_COMB(aP_TERM op (substrongdnf l),substrongdnf r) in
          tRANS th (distribute(rand(concl th)))
    | _ -> rEFL tm
  and strongdnf tm =
    let th = substrongdnf tm in
    tRANS th (strengthen(rand(concl th))) in
  weakdnf,strongdnf;;

let wEAK_CNF_CONV,cNF_CONV =
  let pth1 = Sequent([], parse_term "a \\/ (b /\\ c) <=> (a \\/ b) /\\ (a \\/ c)")
  and pth2 = Sequent([], parse_term "(a /\\ b) \\/ c <=> (a \\/ c) /\\ (b \\/ c)")
  and a_tm = parse_term "a:bool" and b_tm = parse_term "b:bool" and c_tm = parse_term "c:bool" in
  let rec distribute tm =
    match tm with
      Comb(Comb(Const(6,_),a),Comb(Comb(Const(2,_),b),c)) ->
          let th = iNST [a,a_tm; b,b_tm; c,c_tm] pth1 in
          tRANS th (bINOP_CONV distribute (rand(concl th)))
    | Comb(Comb(Const(6,_),Comb(Comb(Const(2,_),a),b)),c) ->
          let th = iNST [a,a_tm; b,b_tm; c,c_tm] pth2 in
          tRANS th (bINOP_CONV distribute (rand(concl th)))
    | _ -> rEFL tm in
  let strengthen =
    tHENC (dEPTH_BINOP_CONV (parse_term "(/\\)") dISJ_CANON_CONV) cONJ_CANON_CONV in
  let rec weakcnf tm =
    match tm with
      Comb(Const(4,_),Abs(_,_))
    | Comb(Const(5,_),Abs(_,_)) -> bINDER_CONV weakcnf tm
    | Comb(Comb(Const(2,_),_),_) -> bINOP_CONV weakcnf tm
    | Comb(Comb(Const(6,_) as op,l),r) ->
          let th = mK_COMB(aP_TERM op (weakcnf l),weakcnf r) in
          tRANS th (distribute(rand(concl th)))
    | _ -> rEFL tm
  and substrongcnf tm =
    match tm with
      Comb(Const(4,_),Abs(_,_))
    | Comb(Const(5,_),Abs(_,_)) -> bINDER_CONV strongcnf tm
    | Comb(Comb(Const(2,_),_),_) -> bINOP_CONV substrongcnf tm
    | Comb(Comb(Const(6,_) as op,l),r) ->
          let th = mK_COMB(aP_TERM op (substrongcnf l),substrongcnf r) in
          tRANS th (distribute(rand(concl th)))
    | _ -> rEFL tm
  and strongcnf tm =
    let th = substrongcnf tm in
    tRANS th (strengthen(rand(concl th))) in
  weakcnf,strongcnf;;

let rEFUTE_THEN =
  let f_tm = parse_term "F"
  and conv = Simp.rEWR_CONV (Sequent ([], parse_term "p <=> ~p ==> F")) in
  fun ttac (asl,w as gl) ->
    if w = f_tm then aLL_TAC gl
    else if is_neg w then dISCH_THEN ttac gl
    else (cONV_TAC conv ++++ dISCH_THEN ttac) gl;;
