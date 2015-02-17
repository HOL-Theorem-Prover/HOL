open Bool;;
open Fusion;;
open Lib;;
open Hl_parser;;
open Equal;;
open Basics;;
(*open Nets;;*)

let mK_FORALL =
  let atm = mk_const("!",[]) in
  fun v th -> aP_TERM (inst [type_of v,aty] atm) (aBS v th);;

let mK_EXISTS =
  let atm = mk_const("?",[]) in
  fun v th -> aP_TERM (inst [type_of v,aty] atm) (aBS v th);;

type instantiation =
  (int * term) list * (term * term) list * (hol_type * hol_type) list;;


let (instantiate :instantiation->term->term) =
  let betas n tm =
    let args,lam = funpow n (fun (l,t) -> (rand t)::l,rator t) ([],tm) in
    rev_itlist (fun a l -> let v,b = dest_abs l in vsubst[a,v] b) args lam in
  let rec ho_betas bcs pat tm =
    if is_var pat or is_const pat then fail() else
    try let bv,bod = dest_abs tm in
        mk_abs(bv,ho_betas bcs (body pat) bod)
    with Failure _ ->
        let hop,args = strip_comb pat in
        try let n = rev_assoc hop bcs in
            if length args = n then betas n tm else fail()
        with Failure _ ->
            let lpat,rpat = dest_comb pat in
            let ltm,rtm = dest_comb tm in
            try let lth = ho_betas bcs lpat ltm in
                try let rth = ho_betas bcs rpat rtm in
                    mk_comb(lth,rth)
                with Failure _ ->
                    mk_comb(lth,rtm)
            with Failure _ ->
                let rth = ho_betas bcs rpat rtm in
                mk_comb(ltm,rth) in
  fun (bcs,tmin,tyin) tm ->
    let itm = if tyin = [] then tm else inst tyin tm in
    if tmin = [] then itm else
    let ttm = vsubst tmin itm in
    if bcs = [] then ttm else
    try ho_betas bcs itm ttm with Failure _ -> ttm;;

let (iNSTANTIATE : instantiation->thm->thm) =
  let rec bETAS_CONV n tm =
    if n = 1 then tRY_CONV bETA_CONV tm else
    (tHENC (rATOR_CONV (bETAS_CONV (n-1))) (tRY_CONV bETA_CONV)) tm in
  let rec hO_BETAS bcs pat tm =
    if is_var pat or is_const pat then fail() else
    try let bv,bod = dest_abs tm in
        aBS bv (hO_BETAS bcs (body pat) bod)
    with Failure _ ->
        let hop,args = strip_comb pat in
        try let n = rev_assoc hop bcs in
            if length args = n then bETAS_CONV n tm else fail()
        with Failure _ ->
            let lpat,rpat = dest_comb pat in
            let ltm,rtm = dest_comb tm in
            try let lth = hO_BETAS bcs lpat ltm in
                try let rth = hO_BETAS bcs rpat rtm in
                    mK_COMB(lth,rth)
                with Failure _ ->
                    aP_THM lth rtm
            with Failure _ ->
                let rth = hO_BETAS bcs rpat rtm in
                aP_TERM ltm rth in
  fun (bcs,tmin,tyin) th ->
    let ith = if tyin = [] then th else iNST_TYPE tyin th in
    if tmin = [] then ith else
    let tth = iNST tmin ith in
    if hyp tth = hyp th then
      if bcs = [] then tth else
      try let eth = hO_BETAS bcs (concl ith) (concl tth) in
          eQ_MP eth tth
      with Failure _ -> tth
    else failwith "INSTANTIATE: term or type var free in assumptions";;

let (iNSTANTIATE_ALL : instantiation->thm->thm) =
  fun ((_,tmin,tyin) as i) th ->
    if tmin = [] & tyin = [] then th else
    let hyps = hyp th in
    if hyps = [] then iNSTANTIATE i th else
    let tyrel,tyiirel =
      if tyin = [] then [],hyps else
      let tvs = itlist (o union (o tyvars snd)) tyin [] in
      partition (fun tm -> let tvs' = type_vars_in_term tm in
                           not(intersect tvs tvs' = [])) hyps in
    let tmrel,tmirrel =
      if tmin = [] then [],tyiirel else
      let vs = itlist (o union (o frees snd)) tmin [] in
      partition (fun tm -> let vs' = frees tm in
                           not (intersect vs vs' = [])) tyiirel in
    let rhyps = union tyrel tmrel in
    let th1 = rev_itlist dISCH rhyps th in
    let th2 = iNSTANTIATE i th1 in
    funpow (length rhyps) uNDISCH th2;;










let (term_match:term list -> term -> term -> instantiation) =
  let safe_inserta ((y,x) as n) l =
    try let z = rev_assoc x l in
        if aconv y z then l else failwith "safe_inserta"
    with Failure "find" -> n::l in

  let safe_insert ((y,x) as n) l =
    try let z = rev_assoc x l in
        if Pervasives.compare y z = 0 then l else failwith "safe_insert"
    with Failure "find" -> n::l in

  let mk_dummy =
    let name = fst(dest_var(genvar aty)) in
    fun ty -> mk_var(name,ty) in

  let rec term_pmatch lconsts env vtm ctm ((insts,homs) as sofar) =
    match (vtm,ctm) with
      Var(_,_),_ ->
       (try let ctm' = rev_assoc vtm env in
            if Pervasives.compare ctm' ctm = 0 then sofar
            else failwith "term_pmatch"
        with Failure "find" ->
            if mem vtm lconsts then
              if Pervasives.compare ctm vtm = 0 then sofar
              else failwith "term_pmatch: can't instantiate local constant"
            else safe_inserta (ctm,vtm) insts,homs)
    | Const(vname,vty),Const(cname,cty) ->
        if Pervasives.compare vname cname = 0 then
          if Pervasives.compare vty cty = 0 then sofar
          else safe_insert (mk_dummy cty,mk_dummy vty) insts,homs
        else failwith "term_pmatch"
    | Abs(vv,vbod),Abs(cv,cbod) ->
        let sofar' = safe_insert
          (mk_dummy(snd(dest_var cv)),mk_dummy(snd(dest_var vv))) insts,homs in
        term_pmatch lconsts ((cv,vv)::env) vbod cbod sofar'
    | _ ->
      let vhop = repeat rator vtm in
      if is_var vhop & not (mem vhop lconsts) &
                       not (can (rev_assoc vhop) env) then
        let vty = type_of vtm and cty = type_of ctm in
        let insts' =
          if Pervasives.compare vty cty = 0 then insts
          else safe_insert (mk_dummy cty,mk_dummy vty) insts in
        (insts',(env,ctm,vtm)::homs)
      else
        let lv,rv = dest_comb vtm
        and lc,rc = dest_comb ctm in
        let sofar' = term_pmatch lconsts env lv lc sofar in
        term_pmatch lconsts env rv rc sofar' in

  let get_type_insts insts =
    itlist (fun (t,x) -> type_match (snd(dest_var x)) (type_of t)) insts in

  let separate_insts insts =
      let realinsts,patterns = partition (o is_var snd) insts in
      let betacounts =
        if patterns = [] then [] else
        itlist
          (fun (_,p) sof ->
            let hop,args = strip_comb p in
            try safe_insert (length args,hop) sof with Failure _ ->
            (warn true "Inconsistent patterning in higher order match"; sof))
          patterns [] in
      let tyins = get_type_insts realinsts [] in
      betacounts,
      mapfilter (fun (t,x) ->
        let x' = let xn,xty = dest_var x in
                 mk_var(xn,type_subst tyins xty) in
        if Pervasives.compare t x' = 0 then fail() else (t,x')) realinsts,
      tyins in

  let rec term_homatch lconsts tyins (insts,homs) =
    if homs = [] then insts else
    let (env,ctm,vtm) = hd homs in
    if is_var vtm then
      if Pervasives.compare ctm vtm = 0
       then term_homatch lconsts tyins (insts,tl homs) else
      let newtyins = safe_insert (type_of ctm,snd(dest_var vtm)) tyins
      and newinsts = (ctm,vtm)::insts in
      term_homatch lconsts newtyins (newinsts,tl homs) else
    let vhop,vargs = strip_comb vtm in
    let afvs = freesl vargs in
    let inst_fn = inst tyins in
    try let tmins = map
          (fun a -> (try rev_assoc a env with Failure _ -> try
                         rev_assoc a insts with Failure _ ->
                         if mem a lconsts then a else fail()),
                    inst_fn a) afvs in
        let pats0 = map inst_fn vargs in
        let pats = map (vsubst tmins) pats0 in
        let vhop' = inst_fn vhop in
        let ni =
          let chop,cargs = strip_comb ctm in
          if Pervasives.compare cargs pats = 0 then
            if Pervasives.compare chop vhop = 0
            then insts else safe_inserta (chop,vhop) insts else
          let ginsts = map
            (fun p -> (if is_var p then p else genvar(type_of p)),p) pats in
          let ctm' = subst ginsts ctm
          and gvs = map fst ginsts in
          let abstm = list_mk_abs(gvs,ctm') in
          let vinsts = safe_inserta (abstm,vhop) insts in
          let icpair = ctm',list_mk_comb(vhop',gvs) in
          icpair::vinsts in
        term_homatch lconsts tyins (ni,tl homs)
    with Failure _ ->
        let lc,rc = dest_comb ctm
        and lv,rv = dest_comb vtm in
        let pinsts_homs' =
          term_pmatch lconsts env rv rc (insts,(env,lc,lv)::(tl homs)) in
        let tyins' = get_type_insts (fst pinsts_homs') [] in
        term_homatch lconsts tyins' pinsts_homs' in

  fun lconsts vtm ctm ->
    let pinsts_homs = term_pmatch lconsts [] vtm ctm ([],[]) in
    let tyins = get_type_insts (fst pinsts_homs) [] in
    let insts = term_homatch lconsts tyins pinsts_homs in
    separate_insts insts;;






let deep_alpha =
  let tryalpha v tm =
    try alpha v tm
    with Failure _ -> try
        let v' = variant (frees tm) v in
        alpha v' tm
    with Failure _ -> tm in
  let rec deep_alpha env tm =
    if env = [] then tm else
    try let v,bod = dest_abs tm in
        let vn,vty = dest_var v in
        try let (vn',_),newenv = remove (fun (_,x) -> x = vn) env in
            let v' = mk_var(vn',vty) in
            let tm' = tryalpha v' tm in
            let iv,ib = dest_abs tm' in
            mk_abs(iv,deep_alpha newenv ib)
        with Failure _ -> mk_abs(v,deep_alpha env bod)
    with Failure _ -> try
        let l,r = dest_comb tm in
        mk_comb(deep_alpha env l,deep_alpha env r)
    with Failure _ -> tm in
  deep_alpha;;






let pART_MATCH =
  let rec match_bvs t1 t2 acc =
    try let v1,b1 = dest_abs t1
        and v2,b2 = dest_abs t2 in
        let n1 = fst(dest_var v1) and n2 = fst(dest_var v2) in
        let newacc = if n1 = n2 then acc else insert (n1,n2) acc in
        match_bvs b1 b2 newacc
    with Failure _ -> try
        let l1,r1 = dest_comb t1
        and l2,r2 = dest_comb t2 in
        match_bvs l1 l2 (match_bvs r1 r2 acc)
    with Failure _ -> acc in
  let pART_MATCH partfn th =
    let sth = sPEC_ALL th in
    let bod = concl sth in
    let pbod = partfn bod in
    let lconsts = intersect (frees (concl th)) (freesl(hyp th)) in
    fun tm ->
      let bvms = match_bvs tm pbod [] in
      let abod = deep_alpha bvms bod in
      let ath = eQ_MP (aLPHA bod abod) sth in
      let insts = term_match lconsts (partfn abod) tm in
      let fth = iNSTANTIATE insts ath in
      if hyp fth <> hyp ath then failwith "PART_MATCH: instantiated hyps" else
      let tm' = partfn (concl fth) in
      if Pervasives.compare tm' tm = 0 then fth else
      try sUBS[aLPHA tm' tm] fth
      with Failure _ -> failwith "PART_MATCH: Sanity check failure"
  in pART_MATCH;;





let mATCH_MP ith =
  let sth =
    try let tm = concl ith in
        let avs,bod = strip_forall tm in
        let ant,con = dest_imp bod in
        let svs,pvs = partition (ccc vfree_in ant) avs in
        if pvs = [] then ith else
        let th1 = sPECL avs (aSSUME tm) in
        let th2 = gENL svs (dISCH ant (gENL pvs (uNDISCH th1))) in
        mP (dISCH tm th2) ith
    with Failure _ -> failwith "MATCH_MP: Not an implication" in
  let match_fun = pART_MATCH (o fst dest_imp) sth in
  fun th -> try mP (match_fun (concl th)) th
            with Failure _ -> failwith "MATCH_MP: No match";;

