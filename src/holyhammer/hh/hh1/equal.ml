









open Lib;;
open Fusion;;
open Preterm;;
open Basics;;
(*open Nets;;*)






type conv = term->thm;;





let lhand = o rand rator;;

let lhs = o fst dest_eq;;

let rhs = o snd dest_eq;;





let mk_primed_var =
  let rec svariant avoid s =
    if mem s avoid || (can get_const_type s && not(is_hidden s)) then
      svariant avoid (s^"'")
    else s in
  fun avoid v ->
    let s,ty = dest_var v in
    let s' = svariant (mapfilter (o fst dest_var) avoid) s in
    mk_var(s',ty);;





let bETA_CONV tm =
  try bETA tm with Failure _ ->
  try let f,arg = dest_comb tm in
      let v = bndvar f in
      iNST [arg,v] (bETA (mk_comb(f,v)))
  with Failure _ -> failwith "BETA_CONV: Not a beta-redex";;





let aP_TERM tm th =
  try mK_COMB(rEFL tm,th)
  with Failure _ -> failwith "AP_TERM";;

let aP_THM th tm =
  try mK_COMB(th,rEFL tm)
  with Failure _ -> failwith "AP_THM";;

let sYM th =
  let tm = concl th in
  let l,r = dest_eq tm in
  let lth = rEFL l in
  eQ_MP (mK_COMB(aP_TERM (rator (rator tm)) th,lth)) lth;;

let aLPHA tm1 tm2 =
  try tRANS (rEFL tm1) (rEFL tm2)
  with Failure _ -> failwith "ALPHA";;

let aLPHA_CONV v tm =
  let res = alpha v tm in
  aLPHA tm res;;

let gEN_ALPHA_CONV v tm =
  if is_abs tm then aLPHA_CONV v tm else
  let b,abs = dest_comb tm in
  aP_TERM b (aLPHA_CONV v abs);;

let mK_BINOP op (lth,rth) =
  mK_COMB(aP_TERM op lth,rth);;





let (nO_CONV:conv) = fun tm -> failwith "NO_CONV";;

let (aLL_CONV:conv) = rEFL;;





let ((tHENC):conv -> conv -> conv) =
  fun conv1 conv2 t ->
    let th1 = conv1 t in
    let th2 = conv2 (rand(concl th1)) in
    tRANS th1 th2;;

let ((oRELSEC):conv -> conv -> conv) =
  fun conv1 conv2 t ->
    try conv1 t with Failure _ -> conv2 t;;

let (fIRST_CONV:conv list -> conv) = end_itlist (fun c1 c2 -> oRELSEC c1 c2);;

let (eVERY_CONV:conv list -> conv) =
  fun l -> itlist (fun c1 c2 -> tHENC c1 c2) l aLL_CONV;;

let rEPEATC =
  let rec rEPEATC conv t =
    (oRELSEC (tHENC conv (rEPEATC conv)) aLL_CONV) t in
  (rEPEATC:conv->conv);;

let (cHANGED_CONV:conv->conv) =
  fun conv tm ->
    let th = conv tm in
    let l,r = dest_eq (concl th) in
    if aconv l r then failwith "CHANGED_CONV" else th;;

let tRY_CONV conv = oRELSEC conv aLL_CONV;;





let (rATOR_CONV:conv->conv) =
  fun conv tm ->
    let l,r = dest_comb tm in aP_THM (conv l) r;;

let (rAND_CONV:conv->conv) =
  fun conv tm ->
    let l,r = dest_comb tm in aP_TERM l (conv r);;

let lAND_CONV = o rATOR_CONV rAND_CONV;;

let (cOMB2_CONV: conv->conv->conv) =
  fun lconv rconv tm -> let l,r = dest_comb tm in mK_COMB(lconv l,rconv r);;

let cOMB_CONV = www cOMB2_CONV;;

let (aBS_CONV:conv->conv) =
  fun conv tm ->
    let v,bod = dest_abs tm in
    let th = conv bod in
    try aBS v th with Failure _ ->
    let gv = genvar(type_of v) in
    let gbod = vsubst[gv,v] bod in
    let gth = aBS gv (conv gbod) in
    let gtm = concl gth in
    let l,r = dest_eq gtm in
    let v' = variant (frees gtm) v in
    let l' = alpha v' l and r' = alpha v' r in
    eQ_MP (aLPHA gtm (mk_eq(l',r'))) gth;;

let bINDER_CONV conv tm =
  if is_abs tm then aBS_CONV conv tm
  else rAND_CONV(aBS_CONV conv) tm;;

let sUB_CONV conv tm =
  match tm with
    Comb(_,_) -> cOMB_CONV conv tm
  | Abs(_,_) -> aBS_CONV conv tm
  | _ -> rEFL tm;;

let bINOP_CONV conv tm =
  let lop,r = dest_comb tm in
  let op,l = dest_comb lop in
  mK_COMB(aP_TERM op (conv l),conv r);;






let (oNCE_DEPTH_CONV: conv->conv),
    (dEPTH_CONV: conv->conv),
    (rEDEPTH_CONV: conv->conv),
    (tOP_DEPTH_CONV: conv->conv),
    (tOP_SWEEP_CONV: conv->conv) =
  let tHENQC conv1 conv2 tm =
    try let th1 = conv1 tm in
        try let th2 = conv2(rand(concl th1)) in tRANS th1 th2
        with Failure _ -> th1
    with Failure _ -> conv2 tm
  and tHENCQC conv1 conv2 tm =
    let th1 = conv1 tm in
    try let th2 = conv2(rand(concl th1)) in tRANS th1 th2
    with Failure _ -> th1
  and cOMB_QCONV conv tm =
    let l,r = dest_comb tm in
    try let th1 = conv l in
        try let th2 = conv r in mK_COMB(th1,th2)
        with Failure _ -> aP_THM th1 r
    with Failure _ -> aP_TERM l (conv r) in
  let rec rEPEATQC conv tm = tHENCQC conv (rEPEATQC conv) tm in
  let sUB_QCONV conv tm =
    if is_abs tm then aBS_CONV conv tm
    else cOMB_QCONV conv tm in
  let rec oNCE_DEPTH_QCONV conv tm =
      (oRELSEC conv (sUB_QCONV (oNCE_DEPTH_QCONV conv))) tm
  and dEPTH_QCONV conv tm =
    tHENQC (sUB_QCONV (dEPTH_QCONV conv))
           (rEPEATQC conv) tm
  and rEDEPTH_QCONV conv tm =
    tHENQC (sUB_QCONV (rEDEPTH_QCONV conv))
           (tHENCQC conv (rEDEPTH_QCONV conv)) tm
  and tOP_DEPTH_QCONV conv tm =
    tHENQC (rEPEATQC conv)
           (tHENCQC (sUB_QCONV (tOP_DEPTH_QCONV conv))
                    (tHENCQC conv (tOP_DEPTH_QCONV conv))) tm
  and tOP_SWEEP_QCONV conv tm =
    tHENQC (rEPEATQC conv)
           (sUB_QCONV (tOP_SWEEP_QCONV conv)) tm in
  (fun c -> tRY_CONV (oNCE_DEPTH_QCONV c)),
  (fun c -> tRY_CONV (dEPTH_QCONV c)),
  (fun c -> tRY_CONV (rEDEPTH_QCONV c)),
  (fun c -> tRY_CONV (tOP_DEPTH_QCONV c)),
  (fun c -> tRY_CONV (tOP_SWEEP_QCONV c));;





let rec dEPTH_BINOP_CONV op conv tm =
  match tm with
    Comb(Comb(op',l),r) when op' = op ->
      let l,r = dest_binop op tm in
      let lth = dEPTH_BINOP_CONV op conv l
      and rth = dEPTH_BINOP_CONV op conv r in
      mK_COMB(aP_TERM op' lth,rth)
  | _ -> conv tm;;





let pATH_CONV =
  let rec path_conv s cnv =
    match s with
      [] -> cnv
    | "l"::t -> rATOR_CONV (path_conv t cnv)
    | "r"::t -> rAND_CONV (path_conv t cnv)
    | _::t -> aBS_CONV (path_conv t cnv) in
  fun s cnv -> path_conv (explode s) cnv;;





let pAT_CONV =
  let rec pCONV xs pat conv =
    if mem pat xs then conv
    else if not(exists (fun x -> free_in x pat) xs) then aLL_CONV
    else if is_comb pat then
      cOMB2_CONV (pCONV xs (rator pat) conv) (pCONV xs (rand pat) conv)
    else
      aBS_CONV (pCONV xs (body pat) conv) in
  fun pat -> let xs,pbod = strip_abs pat in pCONV xs pbod;;





let sYM_CONV tm =
  try let th1 = sYM(aSSUME tm) in
      let tm' = concl th1 in
      let th2 = sYM(aSSUME tm') in
      dEDUCT_ANTISYM_RULE th2 th1
  with Failure _ -> failwith "SYM_CONV";;





let cONV_RULE (conv:conv) th =
  eQ_MP (conv(concl th)) th;;





let sUBS_CONV ths tm =
  try if ths = [] then rEFL tm else
      let lefts = map (o lhand concl) ths in
      let gvs = map (o genvar type_of) lefts in
      let pat = subst (zip gvs lefts) tm in
      let abs = list_mk_abs(gvs,pat) in
      let th = rev_itlist
        (fun y x -> cONV_RULE (tHENC (rAND_CONV bETA_CONV) (lAND_CONV bETA_CONV))
                              (mK_COMB(x,y))) ths (rEFL abs) in
      if rand(concl th) = tm then rEFL tm else th
  with Failure _ -> failwith "SUBS_CONV";;





let bETA_RULE = cONV_RULE(rEDEPTH_CONV bETA_CONV);;

let gSYM = cONV_RULE(oNCE_DEPTH_CONV sYM_CONV);;

let sUBS ths = cONV_RULE (sUBS_CONV ths);;





