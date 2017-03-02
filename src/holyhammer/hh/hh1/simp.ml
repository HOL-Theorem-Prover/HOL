open Lib;;
open Fusion;;
open Basics;;
open Hl_parser;;
(*open Nets;;*)
open Equal;;
open Drule;;
open Tactics;;
open Bool;;

type term_label = Vnet
                 | Lcnet of (string * int)
                 | Cnet of (string * int)
                 | Lnet of int;;

type 'a net = Netnode of (term_label * 'a net) list * 'a list;;

let empty_net = Netnode([],[]);;

let enter =
  let label_to_store lconsts tm =
    let op,args = strip_comb tm in
    if is_const op then Cnet(fst(dest_const op),length args),args
    else if is_abs op then
      let bv,bod = dest_abs op in
      let bod' = if mem bv lconsts then vsubst [genvar(type_of bv),bv] bod
                 else bod in
      Lnet(length args),bod'::args
    else if mem op lconsts then Lcnet(fst(dest_var op),length args),args
    else Vnet,[] in
  let canon_eq x y =
    try Pervasives.compare x y = 0 with Invalid_argument _ -> false
  and canon_lt x y =
    try Pervasives.compare x y < 0 with Invalid_argument _ -> false in
  let rec sinsert x l =
    if l = [] then [x] else
    let h = hd l in
    if canon_eq h x then failwith "sinsert" else
    if canon_lt x h then x::l else
    h::(sinsert x (tl l)) in
  let set_insert x l = try sinsert x l with Failure "sinsert" -> l in
  let rec net_update lconsts (elem,tms,Netnode(edges,tips)) =
    match tms with
      [] -> Netnode(edges,set_insert elem tips)
    | (tm::rtms) ->
          let label,ntms = label_to_store lconsts tm in
          let child,others =
            try (f_f snd iii) (remove (fun (x,y) -> x = label) edges)
            with Failure _ -> (empty_net,edges) in
          let new_child = net_update lconsts (elem,ntms@rtms,child) in
          Netnode ((label,new_child)::others,tips) in
  fun lconsts (tm,elem) net -> net_update lconsts (elem,[tm],net);;

let lookup =
  let label_for_lookup tm =
    let op,args = strip_comb tm in
    if is_const op then Cnet(fst(dest_const op),length args),args
    else if is_abs op then Lnet(length args),(body op)::args
    else Lcnet(fst(dest_var op),length args),args in
  let rec follow (tms,Netnode(edges,tips)) =
    match tms with
      [] -> tips
    | (tm::rtms) ->
          let label,ntms = label_for_lookup tm in
          let collection =
            try let child = assoc label edges in
                follow(ntms @ rtms, child)
            with Failure _ -> [] in
          if label = Vnet then collection else
          try collection @ follow(rtms,assoc Vnet edges)
          with Failure _ -> collection in
  fun tm net -> follow([tm],net);;

type gconv = int * conv;;
let rEWR_CONV = pART_MATCH lhs;;
let iMP_REWR_CONV = pART_MATCH (o lhs (o snd dest_imp));;
let oRDERED_REWR_CONV ord th =
  let basic_conv = rEWR_CONV th in
  fun tm ->
    let thm = basic_conv tm in
    let l,r = dest_eq(concl thm) in
    if ord l r then thm
    else failwith "ORDERED_REWR_CONV: wrong orientation";;
let oRDERED_IMP_REWR_CONV ord th =
  let basic_conv = iMP_REWR_CONV th in
  fun tm ->
    let thm = basic_conv tm in
    let l,r = dest_eq(rand(concl thm)) in
    if ord l r then thm
    else failwith "ORDERED_IMP_REWR_CONV: wrong orientation";;


let term_order =
  let rec lexify ord l1 l2 =
    if l1 = [] then false
    else if l2 = [] then true else
    let h1 = hd l1 and h2 = hd l2 in
    ord h1 h2 or (h1 = h2 & lexify ord (tl l1) (tl l2)) in
  let rec dyn_order top tm1 tm2 =
    let f1,args1 = strip_comb tm1
    and f2,args2 = strip_comb tm2 in
    if f1 = f2 then
      lexify (dyn_order f1) args1 args2
    else
      if f2 = top then false
      else if f1 = top then true
      else f1 > f2 in
  dyn_order (parse_term "T");;
let net_of_thm rep th =
  let tm = concl th in
  let lconsts = freesl (hyp th) in
  let matchable = o can (term_match lconsts) in
  match tm with
    Comb(Comb(Const(0,_),(Abs(x,Comb(Var(s,ty) as v,x')) as l)),v')
         when x' = x & v' = v & not(x = v) ->
        let conv tm =
          match tm with
            Abs(y,Comb(t,y')) when y = y' & not(free_in y t) ->
              iNSTANTIATE(term_match [] v t) th
          | _ -> failwith "REWR_CONV (eTA_AX special case)" in
        enter lconsts (l,(1,conv))
  | Comb(Comb(Const(0,_),l),r) ->
      if rep & free_in l r then
        let th' = eQT_INTRO th in
        enter lconsts (l,(1,rEWR_CONV th'))
      else if rep & matchable l r & matchable r l then
        enter lconsts (l,(1,oRDERED_REWR_CONV term_order th))
      else enter lconsts (l,(1,rEWR_CONV th))
  | Comb(Comb(_,t),Comb(Comb(Const(0,_),l),r)) ->
        if rep & free_in l r then
          let th' = dISCH t (eQT_INTRO(uNDISCH th)) in
          enter lconsts (l,(3,iMP_REWR_CONV th'))
        else if rep & matchable l r & matchable r l then
          enter lconsts (l,(3,oRDERED_IMP_REWR_CONV term_order th))
        else enter lconsts(l,(3,iMP_REWR_CONV th));;
let net_of_conv tm conv sofar =
  enter [] (tm,(2,conv)) sofar;;
let mk_rewrites =
  let iMP_CONJ_CONV = rEWR_CONV(Sequent ([], parse_term "p ==> q ==> r <=> p /\\ q ==> r"))
  and iMP_EXISTS_RULE =
    let cnv = rEWR_CONV(Sequent ([], parse_term "(!x. P x ==> Q) <=> (?x. P x) ==> Q")) in
    fun v th -> cONV_RULE cnv (gEN v th) in
  let collect_condition oldhyps th =
    let conds = subtract (hyp th) oldhyps in
    if conds = [] then th else
    let jth = itlist dISCH conds th in
    let kth = cONV_RULE (rEPEATC iMP_CONJ_CONV) jth in
    let cond,eqn = dest_imp(concl kth) in
    let fvs = subtract (subtract (frees cond) (frees eqn)) (freesl oldhyps) in
    itlist iMP_EXISTS_RULE fvs kth in
  let rec split_rewrites oldhyps cf th sofar =
    let tm = concl th in
    if is_forall tm then
      split_rewrites oldhyps cf (sPEC_ALL th) sofar
    else if is_conj tm then
      split_rewrites oldhyps cf (cONJUNCT1 th)
        (split_rewrites oldhyps cf (cONJUNCT2 th) sofar)
    else if is_imp tm & cf then
      split_rewrites oldhyps cf (uNDISCH th) sofar
    else if is_eq tm then
      (if cf then collect_condition oldhyps th else th)::sofar
    else if is_neg tm then
      let ths = split_rewrites oldhyps cf (eQF_INTRO th) sofar in
      if is_eq (rand tm)
      then split_rewrites oldhyps cf (eQF_INTRO (gSYM th)) ths
      else ths
    else
      split_rewrites oldhyps cf (eQT_INTRO th) sofar in
  fun cf th sofar -> split_rewrites (hyp th) cf th sofar;;
let rEWRITES_CONV net tm =
  let pconvs = lookup tm net in
  try tryfind (fun (_,cnv) -> cnv tm) pconvs
  with Failure _ -> failwith "REWRITES_CONV";;
let set_basic_rewrites,extend_basic_rewrites,basic_rewrites,
    set_basic_convs,extend_basic_convs,basic_convs,basic_net =
  let rewrites = ref ([]:thm list)
  and conversions = ref ([]:(string*(term*conv))list)
  and conv_net = ref (empty_net: gconv net) in
  let rehash_convnet() =
    conv_net := itlist (net_of_thm true) (!rewrites)
        (itlist (fun (_,(pat,cnv)) -> net_of_conv pat cnv) (!conversions)
                empty_net) in
  let set_basic_rewrites thl =
    let canon_thl = itlist (mk_rewrites false) thl [] in
    (rewrites := canon_thl; rehash_convnet())
  and extend_basic_rewrites thl =
    let canon_thl = itlist (mk_rewrites false) thl [] in
    (rewrites := canon_thl @ !rewrites; rehash_convnet())
  and basic_rewrites() = !rewrites
  and set_basic_convs cnvs =
    (conversions := cnvs; rehash_convnet())
  and extend_basic_convs (name,patcong) =
    (conversions :=
      (name,patcong)::filter(fun (name',_) -> name <> name') (!conversions);
     rehash_convnet())
  and basic_convs() = !conversions
  and basic_net() = !conv_net in
  set_basic_rewrites,extend_basic_rewrites,basic_rewrites,
  set_basic_convs,extend_basic_convs,basic_convs,basic_net;;
let gENERAL_REWRITE_CONV rep (cnvl:conv->conv) (builtin_net:gconv net) thl =
  let thl_canon = itlist (mk_rewrites false) thl [] in
  let final_net = itlist (net_of_thm rep) thl_canon builtin_net in
  cnvl (rEWRITES_CONV final_net);;
let gEN_REWRITE_CONV (cnvl:conv->conv) thl =
  gENERAL_REWRITE_CONV false cnvl empty_net thl;;

let gEN_REWRITE_RULE cnvl thl = cONV_RULE(gEN_REWRITE_CONV cnvl thl);;

let pURE_REWRITE_CONV thl =
  gENERAL_REWRITE_CONV true tOP_DEPTH_CONV empty_net thl;;
let oNCE_REWRITE_CONV thl =
  gENERAL_REWRITE_CONV false oNCE_DEPTH_CONV (basic_net()) thl;;
let pURE_REWRITE_RULE thl = cONV_RULE(pURE_REWRITE_CONV thl);;
let pURE_REWRITE_TAC thl = cONV_TAC(pURE_REWRITE_CONV thl);;
let (++++++) x y = oRELSE x y;;
let (++++) x y = tHEN x y;;
