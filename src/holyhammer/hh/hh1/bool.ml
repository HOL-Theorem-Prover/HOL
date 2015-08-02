open Printer;;
open Preterm;;
open Hl_parser;;
open Fusion;;
open Lib;;
open Equal;;
open Basics;;

parse_as_prefix "~";;

parse_as_binder "\\";;
parse_as_binder "!";;
parse_as_binder "?";;
parse_as_binder "?!";;

parse_as_infix ("==>",(4,"right"));;
parse_as_infix ("\\/",(6,"right"));;
parse_as_infix ("/\\",(8,"right"));;

parse_as_infix("<=>",(2,"right"));;
override_interface ("<=>",parse_term "(=):bool->bool->bool");;
parse_as_infix("=",(12,"right"));;

let dest_iff tm =
  match tm with
    Comb(Comb(Const(0,Tyapp("fun",[Tyapp("bool",[]);_])),l),r) -> (l,r)
  | _ -> failwith "dest_iff";;

let pINST tyin tmin =
  let iterm_fn = iNST (map (f_f iii (inst tyin)) tmin)
  and itype_fn = iNST_TYPE tyin in
  fun th -> try iterm_fn (itype_fn th)
            with Failure _ -> failwith "PINST";;





let pROVE_HYP ath bth =
  if exists (aconv (concl ath)) (hyp bth)
  then eQ_MP (dEDUCT_ANTISYM_RULE ath bth) ath
  else bth;;





let t_DEF = new_basic_definition
 (parse_term "T = ((\\p:bool. p) = (\\p:bool. p))");;

let tRUTH = eQ_MP (sYM t_DEF) (rEFL (parse_term "\\p:bool. p"));;

let eQT_ELIM th =
  try eQ_MP (sYM th) tRUTH
  with Failure _ -> failwith "EQT_ELIM";;

let eQT_INTRO =
  let t = parse_term "t:bool" in
  let pth =
    let th1 = dEDUCT_ANTISYM_RULE (aSSUME t) tRUTH in
    let th2 = eQT_ELIM(aSSUME(concl th1)) in
    dEDUCT_ANTISYM_RULE th2 th1 in
  fun th -> eQ_MP (iNST[concl th,t] pth) th;;





let aND_DEF = new_basic_definition
 (parse_term "(/\\) = \\p q. (\\f:bool->bool->bool. f p q) = (\\f. f T T)");;

let mk_conj = mk_binary "/\\";;
let list_mk_conj = end_itlist (curry mk_conj);;

let cONJ =
  let f = parse_term "f:bool->bool->bool"
  and p = parse_term "p:bool"
  and q = parse_term "q:bool" in
  let pth =
    let pth = aSSUME p
    and qth = aSSUME q in
    let th1 = mK_COMB(aP_TERM f (eQT_INTRO pth),eQT_INTRO qth) in
    let th2 = aBS f th1 in
    let th3 = bETA_RULE (aP_THM (aP_THM aND_DEF p) q) in
    eQ_MP (sYM th3) th2 in
  fun th1 th2 ->
    let th = iNST [concl th1,p; concl th2,q] pth in
    pROVE_HYP th2 (pROVE_HYP th1 th);;

let cONJUNCT1 =
  let p = parse_term "P:bool" and q = parse_term "Q:bool" in
  let pth =
    let th1 = cONV_RULE (rAND_CONV bETA_CONV) (aP_THM aND_DEF (parse_term "P:bool")) in
    let th2 = cONV_RULE (rAND_CONV bETA_CONV) (aP_THM th1 (parse_term "Q:bool")) in
    let th3 = eQ_MP th2 (aSSUME (parse_term "P /\\ Q")) in
    eQT_ELIM(bETA_RULE (aP_THM th3 (parse_term "\\(p:bool) (q:bool). p"))) in
  fun th ->
    try let l,r = dest_conj(concl th) in
        pROVE_HYP th (iNST [l,p; r,q] pth)
    with Failure _ -> failwith "CONJUNCT1";;

let cONJUNCT2 =
  let p = parse_term "P:bool" and q = parse_term "Q:bool" in
  let pth =
    let th1 = cONV_RULE (rAND_CONV bETA_CONV) (aP_THM aND_DEF (parse_term "P:bool")) in
    let th2 = cONV_RULE (rAND_CONV bETA_CONV) (aP_THM th1 (parse_term "Q:bool")) in
    let th3 = eQ_MP th2 (aSSUME (parse_term "P /\\ Q")) in
    eQT_ELIM(bETA_RULE (aP_THM th3 (parse_term "\\(p:bool) (q:bool). q"))) in
  fun th ->
    try let l,r = dest_conj(concl th) in
        pROVE_HYP th (iNST [l,p; r,q] pth)
    with Failure _ -> failwith "CONJUNCT2";;

let cONJ_PAIR th =
  try cONJUNCT1 th,cONJUNCT2 th
  with Failure _ -> failwith "CONJ_PAIR: not a conjunction";;

let cONJUNCTS = striplist cONJ_PAIR;;





let iMP_DEF = new_basic_definition
  (parse_term "(==>) = \\p q. p /\\ q <=> p");;

let mk_imp = mk_binary "==>";;

let mP =
  let p = parse_term "p:bool"
  and q = parse_term "q:bool" in
  let pth =
    let th1 = bETA_RULE (aP_THM (aP_THM iMP_DEF p) q) in
    let th2 = eQ_MP th1 (aSSUME (parse_term "p ==> q")) in
    cONJUNCT2 (eQ_MP (sYM th2) (aSSUME p)) in
  fun ith th ->
    let ant,con = dest_imp (concl ith) in
    if aconv ant (concl th) then
      pROVE_HYP th (pROVE_HYP ith (iNST [ant,p; con,q] pth))
    else failwith "MP: theorems do not agree";;

let dISCH =
  let p = parse_term "p:bool"
  and q = parse_term "q:bool" in
  let pth = sYM(bETA_RULE (aP_THM (aP_THM iMP_DEF p) q)) in
  fun a th ->
    let th1 = cONJ (aSSUME a) th in
    let th2 = cONJUNCT1 (aSSUME (concl th1)) in
    let th3 = dEDUCT_ANTISYM_RULE th1 th2 in
    let th4 = iNST [a,p; concl th,q] pth in
    eQ_MP th4 th3;;

let rec dISCH_ALL th =
  try dISCH_ALL (dISCH (hd (hyp th)) th)
  with Failure _ -> th;;

let uNDISCH th =
  try mP th (aSSUME(rand(rator(concl th))))
  with Failure _ -> failwith "UNDISCH";;

let rec uNDISCH_ALL th =
  if is_imp (concl th) then uNDISCH_ALL (uNDISCH th)
  else th;;

let iMP_ANTISYM_RULE th1 th2 =
  dEDUCT_ANTISYM_RULE (uNDISCH th2) (uNDISCH th1);;

let eQ_IMP_RULE =
  let peq = parse_term "p <=> q" in
  let p,q = dest_iff peq in
  let pth1 = dISCH peq (dISCH p (eQ_MP (aSSUME peq) (aSSUME p)))
  and pth2 = dISCH peq (dISCH q (eQ_MP (sYM(aSSUME peq)) (aSSUME q))) in
  fun th -> let l,r = dest_iff(concl th) in
            mP (iNST [l,p; r,q] pth1) th,mP (iNST [l,p; r,q] pth2) th;;





let fORALL_DEF = new_basic_definition (parse_term "(!) = \\P:A->bool. P = \\x. T");;

let mk_forall = mk_binder "!";;

let sPEC =
  let p = parse_term "P:A->bool"
  and x = parse_term "x:A" in
  let pth =
    let th1 = eQ_MP(aP_THM fORALL_DEF p) (aSSUME (parse_term "(!)(P:A->bool)")) in
    let th2 = aP_THM (cONV_RULE bETA_CONV th1) x in
    let th3 = cONV_RULE (rAND_CONV bETA_CONV) th2 in
    dISCH_ALL (eQT_ELIM th3) in
  fun tm th ->
    try let abs = rand(concl th) in
        cONV_RULE bETA_CONV
         (mP (pINST [snd(dest_var(bndvar abs)),aty] [abs,p; tm,x] pth) th)
    with Failure _ -> failwith "SPEC";;

let sPECL tms th =
  try rev_itlist sPEC tms th
  with Failure _ -> failwith "SPECL";;

let sPEC_VAR th =
  let bv = variant (thm_frees th) (bndvar(rand(concl th))) in
  bv,sPEC bv th;;

let rec sPEC_ALL th =
  if is_forall(concl th) then sPEC_ALL(snd(sPEC_VAR th)) else th;;

let gEN =
  let pth = sYM(cONV_RULE (rAND_CONV bETA_CONV)
                          (aP_THM fORALL_DEF (parse_term "P:A->bool"))) in
  fun x ->
    let qth = iNST_TYPE[snd(dest_var x),aty] pth in
    let ptm = rand(rand(concl qth)) in
    fun th ->
        let th' = aBS x (eQT_INTRO th) in
        let phi = lhand(concl th') in
        let rth = iNST[phi,ptm] qth in
        eQ_MP rth th';;

let gENL = itlist gEN;;

let gEN_ALL th =
  let asl,c = dest_thm th in
  let vars = subtract (frees c) (freesl asl) in
  gENL vars th;;

let eXISTS_DEF = new_basic_definition
 (parse_term "(?) = \\P:A->bool. !q. (!x. P x ==> q) ==> q");;

let mk_exists =  mk_binder "?";;

let eXISTS =
  let p = parse_term "P:A->bool" and x = parse_term "x:A" in
  let pth =
    let th1 = cONV_RULE (rAND_CONV bETA_CONV) (aP_THM eXISTS_DEF p) in
    let th2 = sPEC x (aSSUME (parse_term "!x:A. P x ==> Q")) in
    let th3 = dISCH (parse_term "!x:A. P x ==> Q") (mP th2 (aSSUME (parse_term "(P:A->bool) x"))) in
    eQ_MP (sYM th1) (gEN (parse_term "Q:bool") th3) in
  fun (etm,stm) th ->
    try let qf,abs = dest_comb etm in
        let bth = bETA_CONV(mk_comb(abs,stm)) in
        let cth = pINST [type_of stm,aty] [abs,p; stm,x] pth in
        pROVE_HYP (eQ_MP (sYM bth) th) cth
    with Failure _ -> failwith "EXISTS";;

let cHOOSE =
  let p = parse_term "P:A->bool" and q = parse_term "Q:bool" in
  let pth =
    let th1 = cONV_RULE (rAND_CONV bETA_CONV) (aP_THM eXISTS_DEF p) in
    let th2 = sPEC (parse_term "Q:bool") (uNDISCH(fst(eQ_IMP_RULE th1))) in
    dISCH_ALL (dISCH (parse_term "(?) (P:A->bool)") (uNDISCH th2)) in
  fun (v,th1) th2 ->
    try let abs = rand(concl th1) in
        let bv,bod = dest_abs abs in
        let cmb = mk_comb(abs,v) in
        let pat = vsubst[v,bv] bod in
        let th3 = cONV_RULE bETA_CONV (aSSUME cmb) in
        let th4 = gEN v (dISCH cmb (mP (dISCH pat th2) th3)) in
        let th5 = pINST [snd(dest_var v),aty] [abs,p; concl th2,q] pth in
        mP (mP th5 th4) th1
    with Failure _ -> failwith "CHOOSE";;

let oR_DEF = new_basic_definition (parse_term "(\\/) = \\p q. !r. (p ==> r) ==> (q ==> r) ==> r");;

let mk_disj = mk_binary "\\/";;
let list_mk_disj = end_itlist (curry mk_disj);;

let f_DEF = new_basic_definition (parse_term "F = !p:bool. p");;
let nOT_DEF = new_basic_definition (parse_term "(~) = \\p. p ==> F");;

let mk_neg =
  let neg_tm = parse_term "(~)" in
  fun tm -> try mk_comb(neg_tm,tm)
            with Failure _ -> failwith "mk_neg";;

let nOT_ELIM =
  let p = parse_term "P:bool" in
  let pth = cONV_RULE(rAND_CONV bETA_CONV) (aP_THM nOT_DEF p) in
  fun th ->
    try eQ_MP (iNST [rand(concl th),p] pth) th
    with Failure _ -> failwith "NOT_ELIM";;

let nOT_INTRO =
  let p = parse_term "P:bool" in
  let pth = sYM(cONV_RULE(rAND_CONV bETA_CONV) (aP_THM nOT_DEF p)) in
  fun th ->
    try eQ_MP (iNST [rand(rator(concl th)),p] pth) th
    with Failure _ -> failwith "NOT_INTRO";;

let eQF_INTRO =
  let p = parse_term "P:bool" in
  let pth =
    let th1 = nOT_ELIM (aSSUME (parse_term "~ P"))
    and th2 = dISCH (parse_term "F") (sPEC p (eQ_MP f_DEF (aSSUME (parse_term "F")))) in
    dISCH_ALL (iMP_ANTISYM_RULE th1 th2) in
  fun th ->
    try mP (iNST [rand(concl th),p] pth) th
    with Failure _ -> failwith "EQF_INTRO";;

let eXISTS_UNIQUE_DEF = new_basic_definition
 (parse_term "(?!) = \\P:A->bool. ((?) P) /\\ (!x y. P x /\\ P y ==> x = y)");;

let cONTR =
  let p = parse_term "P:bool" and f_tm = parse_term "F" in
  let pth = sPEC p (eQ_MP f_DEF (aSSUME (parse_term "F"))) in
  fun tm th ->
    if concl th <> f_tm then failwith "CONTR"
    else pROVE_HYP th (iNST [tm,p] pth);;

let eXISTS_UNIQUE_THM = Sequent ([], parse_term "!P. (?!x:A. P x) <=> (?x. P x) /\\ (!x x'. P x /\\ P x' ==> (x = x'))");;
let fUN_EQ_THM = Sequent([],parse_term "!(f:A->B) g. f = g <=> (!x. f x = g x)");;
let bOOL_CASES_AX = Sequent([],parse_term "!t. (t <=> T) \\/ (t <=> F)");;
