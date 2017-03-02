









open Lib;;
open Fusion;;
open Basics;;
open Printer;;
open Hl_parser;;
open Equal;;
open Bool;;
open Drule;;





let null_inst = ([],[],[] :instantiation);;

let null_meta = (([]:term list),null_inst);;





type goal = (string * thm) list * term;;

let equals_goal ((a,w):goal) ((a',w'):goal) =
  forall2 (fun (s,th) (s',th') -> s = s' & equals_thm th th') a a' & w = w';;









type justification = instantiation -> thm list -> thm;;






type goalstate = (term list * instantiation) * goal list * justification;;





type goalstack = goalstate list;;







type refinement = goalstate -> goalstate;;











type tactic = goal -> goalstate;;

type thm_tactic = thm -> tactic;;

type thm_tactical = thm_tactic -> thm_tactic;;





let (inst_goal:instantiation->goal->goal) =
  fun p (thms,w) ->
    map (f_f iii (iNSTANTIATE_ALL p)) thms,instantiate p w;;





let (compose_insts :instantiation->instantiation->instantiation) =
  fun (pats1,tmin1,tyin1) ((pats2,tmin2,tyin2) as i2) ->
    let tmin = map (f_f (instantiate i2) (inst tyin2)) tmin1
    and tyin = map (f_f (type_subst tyin2) iii) tyin1 in
    let tmin' = filter (fun (_,x) -> not (can (rev_assoc x) tmin)) tmin2
    and tyin' = filter (fun (_,a) -> not (can (rev_assoc a) tyin)) tyin2 in
    pats1@pats2,tmin@tmin',tyin@tyin';;









let (tHEN),(tHENL) =
  let propagate_empty i [] = [] in
  let propagate_thm th i [] = iNSTANTIATE_ALL i th in
  let compose_justs n just1 just2 i ths =
    let ths1,ths2 = chop_list n ths in
    (just1 i ths1)::(just2 i ths2) in
  let rec seqapply l1 l2 = match (l1,l2) with
     ([],[]) -> null_meta,[],propagate_empty
   | ((tac:tactic)::tacs),((goal:goal)::goals) ->
            let ((mvs1,insts1),gls1,just1) = tac goal in
            let goals' = map (inst_goal insts1) goals in
            let ((mvs2,insts2),gls2,just2) = seqapply tacs goals' in
            ((union mvs1 mvs2,compose_insts insts1 insts2),
             gls1@gls2,compose_justs (length gls1) just1 just2)
   | _,_ -> failwith "seqapply: Length mismatch" in
  let justsequence just1 just2 insts2 i ths =
    just1 (compose_insts insts2 i) (just2 i ths) in
  let tacsequence ((mvs1,insts1),gls1,just1) tacl =
    let ((mvs2,insts2),gls2,just2) = seqapply tacl gls1 in
    let jst = justsequence just1 just2 insts2 in
    let just = if gls2 = [] then propagate_thm (jst null_inst []) else jst in
    ((union mvs1 mvs2,compose_insts insts1 insts2),gls2,just) in
  let (then_: tactic -> tactic -> tactic) =
    fun tac1 tac2 g ->
      let _,gls,_ as gstate = tac1 g in
      tacsequence gstate (replicate tac2 (length gls))
  and (thenl_: tactic -> tactic list -> tactic) =
    fun tac1 tac2l g ->
      let _,gls,_ as gstate = tac1 g in
      if gls = [] then tacsequence gstate []
      else tacsequence gstate tac2l in
  then_,thenl_;;

let ((oRELSE): tactic -> tactic -> tactic) =
  fun tac1 tac2 g ->
    try tac1 g with Failure _ -> tac2 g;;

let (fAIL_TAC: string -> tactic) =
  fun tok g -> failwith tok;;

let (nO_TAC: tactic) =
  fAIL_TAC "NO_TAC";;

let (aLL_TAC:tactic) =
  fun g -> null_meta,[g],fun _ [th] -> th;;

let rec rEPEAT tac g =
  (oRELSE (tHEN tac (rEPEAT tac)) aLL_TAC) g;;

let eVERY tacl =
  itlist (fun t1 t2 -> tHEN t1 t2) tacl aLL_TAC;;

let mAP_EVERY tacf lst =
  eVERY (map tacf lst);;

let (lABEL_TAC: string -> thm_tactic) =
  fun s thm (asl,w) ->
    null_meta,[(s,thm)::asl,w],
    fun i [th] -> pROVE_HYP (iNSTANTIATE_ALL i thm) th;;

let aSSUME_TAC = lABEL_TAC "";;





let (pOP_ASSUM: thm_tactic -> tactic) =
  fun ttac ->
   function (((_,th)::asl),w) -> ttac th (asl,w)
    | _ -> failwith "POP_ASSUM: No assumption to pop";;

let (aSSUM_LIST: (thm list -> tactic) -> tactic) =
    fun aslfun (asl,w) -> aslfun (map snd asl) (asl,w);;

let (pOP_ASSUM_LIST: (thm list -> tactic) -> tactic) =
  fun asltac (asl,w) -> asltac (map snd asl) ([],w);;

let (eVERY_ASSUM: thm_tactic -> tactic) =
  fun ttac -> aSSUM_LIST (mAP_EVERY ttac);;

let (fIRST_ASSUM: thm_tactic -> tactic) =
  fun ttac (asl,w as g) -> tryfind (fun (_,th) -> ttac th g) asl;;

let (uNDISCH_THEN:term->thm_tactic->tactic) =
  fun tm ttac (asl,w) ->
    let thp,asl' = remove (fun (_,th) -> aconv (concl th) tm) asl in
    ttac (snd thp) (asl',w);;

let fIRST_X_ASSUM ttac =
    fIRST_ASSUM(fun th -> uNDISCH_THEN (concl th) ttac);;

let (rULE_ASSUM_TAC :(thm->thm)->tactic) =
  fun rule (asl,w) -> (tHEN (pOP_ASSUM_LIST(kkk aLL_TAC))
                       (mAP_EVERY (fun (s,th) -> lABEL_TAC s (rule th))
                                 (rev asl))) (asl,w);;







let (aCCEPT_TAC: thm_tactic) =
  let propagate_thm th i [] = iNSTANTIATE_ALL i th in
  fun th (asl,w) ->
    if aconv (concl th) w then
      null_meta,[],propagate_thm th
    else failwith "ACCEPT_TAC";;







let (cONV_TAC: conv -> tactic) =
  let t_tm = parse_term "T" in
  fun conv ((asl,w) as g) ->
    let th = conv w in
    let tm = concl th in
    if aconv tm w then aCCEPT_TAC th g else
    let l,r = dest_eq tm in
    if not(aconv l w) then failwith "CONV_TAC: bad equation" else
    if r = t_tm then aCCEPT_TAC(eQT_ELIM th) g else
    let th' = sYM th in
    null_meta,[asl,r],fun i [th] -> eQ_MP (iNSTANTIATE_ALL i th') th;;


let (dISCH_TAC: tactic) =
  let f_tm = parse_term "F" in
  fun (asl,w) ->
    try let ant,c = dest_imp w in
        let th1 = aSSUME ant in
        null_meta,[("",th1)::asl,c],
        fun i [th] -> dISCH (instantiate i ant) th
    with Failure _ -> try
        let ant = dest_neg w in
        let th1 = aSSUME ant in
        null_meta,[("",th1)::asl,f_tm],
        fun i [th] -> nOT_INTRO(dISCH (instantiate i ant) th)
    with Failure _ -> failwith "DISCH_TAC";;

let (uNDISCH_TAC: term -> tactic) =
 fun tm (asl,w) ->
   try let sthm,asl' = remove (fun (_,asm) -> aconv (concl asm) tm) asl in
       let thm = snd sthm in
       null_meta,[asl',mk_imp(tm,w)],
       fun i [th] -> mP th (iNSTANTIATE_ALL i thm)
   with Failure _ -> failwith "UNDISCH_TAC";;

let (sPEC_TAC: term * term -> tactic) =
  fun (t,x) (asl,w) ->
    try null_meta,[asl, mk_forall(x,subst[x,t] w)],
        fun i [th] -> sPEC (instantiate i t) th
    with Failure _ -> failwith "SPEC_TAC";;

let (x_GEN_TAC: term -> tactic),
    (x_CHOOSE_TAC: term -> thm_tactic),
    (eXISTS_TAC: term -> tactic) =
  let tactic_type_compatibility_check pfx e g =
    let et = type_of e and gt = type_of g in
    if et = gt then ()
    else failwith(pfx ^ ": expected type :"^string_of_type et^" but got :"^
                  string_of_type gt) in
  let x_GEN_TAC x' =
    if not(is_var x') then failwith "X_GEN_TAC: not a variable" else
    fun (asl,w) ->
        let x,bod = try dest_forall w
          with Failure _ -> failwith "X_GEN_TAC: Not universally quantified" in
        let _ = tactic_type_compatibility_check "X_GEN_TAC" x x' in
        let avoids = itlist (fun x -> union (thm_frees (snd x))) asl (frees w) in
        if mem x' avoids then failwith "X_GEN_TAC: invalid variable" else
        let afn = cONV_RULE(gEN_ALPHA_CONV x) in
        null_meta,[asl,vsubst[x',x] bod],
        fun i [th] -> afn (gEN x' th)
  and x_CHOOSE_TAC x' xth =
        let xtm = concl xth in
        let x,bod = try dest_exists xtm
         with Failure _ -> failwith "X_CHOOSE_TAC: not existential" in
        let _ = tactic_type_compatibility_check "X_CHOOSE_TAC" x x' in
        let pat = vsubst[x',x] bod in
        let xth' = aSSUME pat in
        fun (asl,w) ->
          let avoids = itlist (fun x -> union (frees ( concl ( snd x)))) asl
                              (union (frees w) (thm_frees xth)) in
          if mem x' avoids then failwith "X_CHOOSE_TAC: invalid variable" else
          null_meta,[("",xth')::asl,w],
          fun i [th] -> cHOOSE(x',iNSTANTIATE_ALL i xth) th
  and eXISTS_TAC t (asl,w) =
    let v,bod = try dest_exists w with Failure _ ->
                failwith "EXISTS_TAC: Goal not existentially quantified" in
    let _ = tactic_type_compatibility_check "EXISTS_TAC" v t in
    null_meta,[asl,vsubst[t,v] bod],
    fun i [th] -> eXISTS (instantiate i w,instantiate i t) th in
  x_GEN_TAC,x_CHOOSE_TAC,eXISTS_TAC;;

(*let (GEN_TAC: tactic) =
  fun (asl,w) ->
    try let x = fst(dest_forall w) in
        let avoids = itlist (union o thm_frees o snd) asl (frees w) in
        let x' = mk_primed_var avoids x in
        X_GEN_TAC x' (asl,w)
    with Failure _ -> failwith "GEN_TAC";;
*)

let (cHOOSE_TAC: thm_tactic) =
  fun xth ->
    try let x = fst(dest_exists(concl xth)) in
        fun (asl,w) ->
          let avoids = itlist (fun x -> union ( thm_frees ( snd x))) asl
                              (union (frees w) (thm_frees xth)) in
          let x' = mk_primed_var avoids x in
          x_CHOOSE_TAC x' xth (asl,w)
      with Failure _ -> failwith "CHOOSE_TAC";;


let (cONTR_TAC: thm_tactic) =
  let propagate_thm th i [] = iNSTANTIATE_ALL i th in
  fun cth (asl,w) ->
    try let th = cONTR w cth in
        null_meta,[],propagate_thm th
    with Failure _ -> failwith "CONTR_TAC";;

let (dISCH_THEN: thm_tactic -> tactic) =
  fun ttac -> tHEN dISCH_TAC (pOP_ASSUM ttac);;

let (by:tactic->refinement) =
  fun tac ((mvs,inst),gls,just) ->
    if gls = [] then failwith "No goal set" else
    let g = hd gls
    and ogls = tl gls in
    let ((newmvs,newinst),subgls,subjust) = tac g in
    let n = length subgls in
    let mvs' = union newmvs mvs
    and inst' = compose_insts inst newinst
    and gls' = subgls @ map (inst_goal newinst) ogls in
    let just' i ths =
      let i' = compose_insts inst' i in
      let cths,oths = chop_list n ths in
      let sths = (subjust i cths) :: oths in
      just i' sths in
    (mvs',inst'),gls',just';;

let (mk_goalstate:goal->goalstate) =
  fun (asl,w) ->
    if type_of w = bool_ty then
      null_meta,[asl,w],
      (fun inst [th] -> iNSTANTIATE_ALL inst th)
    else failwith "mk_goalstate: Non-boolean goal";;

let (tAC_PROOF : goal * tactic -> thm) =
  fun (g,tac) ->
    let gstate = mk_goalstate g in
    let _,sgs,just = by tac gstate in
    if sgs = [] then just null_inst []
    else failwith "TAC_PROOF: Unsolved goals";;

let prove(t,tac) =
  let th = tAC_PROOF(([],t),tac) in
  let t' = concl th in
  if t' = t then th else
  try eQ_MP (aLPHA t' t) th
  with Failure _ -> failwith "prove: justification generated wrong theorem";;
