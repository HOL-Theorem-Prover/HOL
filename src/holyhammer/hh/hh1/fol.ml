module Im = Map.Make(struct type t = int let compare = compare end);;

open Lib;;

type fol_term = Fvar of int
              | Fnapp of int * fol_term list;;
type fol_lit = int * fol_term list;;

let mk_negated (p,a) = -p,a;;

let offinc = 10000;;

let rec fol_ground = function
    Fvar _ -> false
  | Fnapp (_, l) -> Lib.forall fol_ground l;;

let rec fol_subst_bump offset theta tm =
  match tm with
    Fvar v -> if v < offinc then
        let v' = v + offset in
        (try Im.find v' theta with Not_found -> (Fvar(v')))
      else
        (try Im.find v theta with Not_found -> tm)
  | Fnapp(f,args) ->
    let args' = qmap (fol_subst_bump offset theta) args in
    if args' == args then tm else Fnapp(f,args');;

let fol_inst_bump offset theta ((p,args) as at:fol_lit) =
  let args' = qmap (fol_subst_bump offset theta) args in
  if args' == args then at else p,args';;

let rec istriv env x t =
  match t with
    Fvar y -> y = x or
  (try let t' = Im.find y env in istriv env x t'
   with Not_found -> false)
  | Fnapp(f,args) -> exists (istriv env x) args & failwith "cyclic";;

let rec fol_unify offset tm1 tm2 ((subst, nv) as sofar) =
  match tm1,tm2 with
    Fnapp(f,fargs),Fnapp(g,gargs) ->
      if f <> g then failwith "" else
        itlist2 (fol_unify offset) fargs gargs sofar
  | _,Fvar(x) ->
    (let x' = x + offset in
     try let tm2' = Im.find x' subst in
         fol_unify 0 tm1 tm2' sofar
     with Not_found ->
       if istriv subst x' tm1 then sofar
       else (Im.add x' tm1 subst, x' :: nv))
  | Fvar(x),_ ->
     (try let tm1' = Im.find x subst in
         fol_unify offset tm1' tm2 sofar
     with Not_found ->
       let tm2' = fol_subst_bump offset Im.empty tm2 in
       if istriv subst x tm2' then sofar
       else (Im.add x tm2' subst, nv));;

let fol_unify_lit offset (h1, l1) (h2, l2) subst =
  if h1 <> h2 then failwith "" else
  List.fold_left (fun sf (t1, t2) -> fol_unify offset t1 t2 sf) (subst, []) (zip l1 l2)
;;

let rec fol_subst theta tm =
  match tm with
    Fvar v -> (try Im.find v theta with Not_found -> tm)
  | Fnapp(f,args) ->
    let args' = qmap (fol_subst theta) args in
    if args' == args then tm else Fnapp(f,args');;

let fol_inst theta ((p,args) as at:fol_lit) =
  let args' = qmap (fol_subst theta) args in
  if args' == args then at else p,args';;

let reset_vars,fol_of_var,hol_of_var =
  let vstore = ref []
  and gstore = ref []
  and vcounter = ref 0 in
  let inc_vcounter() =
    let n = !vcounter in
    let m = n + 1 in
    if m >= offinc then failwith "inc_vcounter: too many variables" else
      (vcounter := m; n) in
  let reset_vars() = vstore := []; gstore := []; vcounter := 0 in
  let fol_of_var v =
    let currentvars = !vstore in
    try assoc v currentvars with Failure _ ->
      let n = inc_vcounter() in
      vstore := (v,n)::currentvars; n in
  let hol_of_var v =
    try rev_assoc v (!vstore)
    with Failure _ -> rev_assoc v (!gstore) in
  let hol_of_bumped_var v =
    try hol_of_var v with Failure _ ->
      let v' = v mod offinc in
      let hv' = hol_of_var v' in
      let gv = Basics.genvar(Fusion.type_of hv') in
      gstore := (gv,v)::(!gstore); gv in
  reset_vars,fol_of_var,hol_of_bumped_var;;

let reset_consts,fol_of_const,hol_of_const =
  let false_tm = Hl_parser.parse_term "F" in
  let cstore = ref ([]:(Fusion.term * int)list)
  and ccounter = ref 2 in
  let reset_consts() = cstore := [false_tm,1]; ccounter := 2 in
  let fol_of_const c =
    let currentconsts = !cstore in
    try assoc c currentconsts with Failure _ ->
      let n = !ccounter in
      ccounter := n + 1; cstore := (c,n)::currentconsts; n in
  let hol_of_const c = rev_assoc c (!cstore) in
  reset_consts,fol_of_const,hol_of_const;;



let rec fol_of_term cs_are_vars env consts tm =
  if Fusion.is_var tm & (if cs_are_vars then mem tm consts else not (mem tm consts)) then
      Fvar(fol_of_var tm)
  else
    let f,args = Basics.strip_comb tm in
    if mem f env then failwith "fol_of_term: higher order" else
      let ff = fol_of_const f in
      Fnapp(ff,map (fol_of_term cs_are_vars env consts) args)
;;

let fol_of_atom cs_are_vars env vars tm =
  let f,args = Basics.strip_comb tm in
  if mem f env then failwith "fol_of_atom: higher order" else
    let ff = fol_of_const f in
    ff,map (fol_of_term cs_are_vars env vars) args;;

let fol_of_literal cs_are_vars env vars tm =
  try let tm' = Basics.dest_neg tm in
      let p,a = fol_of_atom cs_are_vars env vars tm' in
      -p,a
  with Failure _ -> fol_of_atom cs_are_vars env vars tm;;

let rec hol_of_term tm =
  match tm with
    Fvar v -> hol_of_var v
  | Fnapp(f,args) -> Basics.list_mk_comb(hol_of_const f,map hol_of_term args);;

let hol_of_atom (p,args) =
  Basics.list_mk_comb(hol_of_const p,map hol_of_term args);;

let hol_of_literal (p,args) =
  if p < 0 then Bool.mk_neg(hol_of_atom(-p,args))
  else hol_of_atom (p,args);;

let rec fol_eq insts tm1 tm2 =
  tm1 == tm2 or
  match tm1,tm2 with
    Fnapp(f,fargs),Fnapp(g,gargs) ->
      f = g & forall2 (fol_eq insts) fargs gargs
  | _,Fvar(x) ->
    (try let tm2' = Im.find x insts in
         fol_eq insts tm1 tm2'
     with Not_found ->
       try istriv insts x tm1 with Failure _ -> false)
  | Fvar(x),_ ->
    (try let tm1' = Im.find x insts in
         fol_eq insts tm1' tm2
     with Not_found ->
       try istriv insts x tm2 with Failure _ -> false);;

let fol_atom_eq insts (p1,args1) (p2,args2) =
  p1 = p2 & forall2 (fol_eq insts) args1 args2;;

open Equal;;
open Simp;;
open Basics;;
open Bool;;
open Fusion;;
open Hl_parser;;
open Drule;;

let create_equality_axioms =
  let eq_thms = cONJUNCTS (Sequent ([], parse_term "(x:A = x) /\\
        (~(x:A = y) \\/ ~(x = z) \\/ (y = z))")) in
  let imp_elim_CONV = rEWR_CONV
    (Sequent ([], parse_term "(a ==> b) <=> ~a \\/ b")) in
  let eq_elim_RULE =
    mATCH_MP(Sequent ([], parse_term "(a <=> b) ==> b \\/ ~a")) in
  let veq_tm = rator(rator(concl(hd eq_thms))) in
  let create_equivalence_axioms (eq,_) =
    let tyins = type_match (type_of veq_tm) (type_of eq) [] in
    map (iNST_TYPE tyins) eq_thms in
  let rec tm_consts tm acc =
    let fn,args = strip_comb tm in
    if args = [] then acc
    else itlist tm_consts args (insert (fn,length args) acc) in
  let rec fm_consts tm ((preds,funs) as acc) =
    try fm_consts(snd(dest_forall tm)) acc with Failure _ ->
    try fm_consts(snd(dest_exists tm)) acc with Failure _ ->
    try let l,r = dest_conj tm in fm_consts l (fm_consts r acc)
    with Failure _ -> try
        let l,r = dest_disj tm in fm_consts l (fm_consts r acc)
    with Failure _ -> try
        let l,r = dest_imp tm in fm_consts l (fm_consts r acc)
    with Failure _ -> try
         fm_consts (dest_neg tm) acc with Failure _ ->
    try let l,r = dest_eq tm in
        if type_of l = bool_ty
        then fm_consts r (fm_consts l acc)
        else failwith "atomic equality"
    with Failure _ ->
    let pred,args = strip_comb tm in
    if args = [] then acc else
    insert (pred,length args) preds,itlist tm_consts args funs in
  let create_congruence_axiom pflag (tm,len) =
    let atys,rty = splitlist (fun ty -> let op,l = dest_type ty in
                                        if op = "fun" then hd l,hd(tl l)
                                          else fail())
                               (type_of tm) in
      let ctys = fst(chop_list len atys) in
      let largs = map genvar ctys
      and rargs = map genvar ctys in
      let th1 = rev_itlist (ccc (curry mK_COMB)) (map (o aSSUME mk_eq)
          (zip largs rargs)) (rEFL tm) in
      let th2 = if pflag then eq_elim_RULE th1 else th1 in
      itlist (fun e th -> cONV_RULE imp_elim_CONV (dISCH e th)) (hyp th2) th2 in
    fun tms -> let preds,funs = itlist fm_consts tms ([],[]) in
               let eqs0,noneqs = partition
                  (fun (t,_) -> is_const t & fst(dest_const t) = "=") preds in
               if eqs0 = [] then [] else
               let pcongs = map (create_congruence_axiom true) noneqs
               and fcongs = map (create_congruence_axiom false) funs in
               let preds1,_ =
                 itlist fm_consts (map concl (pcongs @ fcongs)) ([],[]) in
               let eqs1 = filter
                 (fun (t,_) -> is_const t & fst(dest_const t) = "=") preds1 in
               let eqs = union eqs0 eqs1 in
               let equivs =
                 itlist (o (union' equals_thm) create_equivalence_axioms)
                        eqs [] in
               equivs@pcongs@fcongs;;

let rec fol_subst_partial insts tm =
  match tm with
    Fvar(v) -> (try let t = Im.find v insts in
                    fol_subst_partial insts t
                with Not_found -> tm)
  | Fnapp(f,args) -> Fnapp(f,map (fol_subst_partial insts) args);;

let print_var i = Printf.printf "V%i" i;;
(*  try print_string (String.uppercase (fst (Fusion.dest_var (hol_of_var i)))) with _ -> print_char 'V'; print_int i;;*)

let rec print_foft = function
    Fvar i -> print_var i
  | Fnapp (i, l) -> (*Printf.printf "c%i" i;*)
(try print_string (String.lowercase (fst (Fusion.dest_const (hol_of_const i))))
                   with Failure _ -> print_string (String.lowercase (fst (Fusion.dest_var (hol_of_const i)))));
    match l with
      [] -> ()
    | [h] -> print_char '('; print_foft h; print_char ')'
    | h :: t -> print_char '('; print_foft h; List.iter (fun x -> print_char ','; print_foft x) t; print_char ')'
;;

let print_fofl (i, l) =
  if i < 0 then print_char '-';
  if fst (Fusion.dest_const (hol_of_const (abs i))) = "#" then print_string "#" else (*Printf.printf "p%i" (abs i);*)
  print_string (fst (Fusion.dest_const (hol_of_const (abs i))));
  match l with
    [] -> ()
  | [h] -> print_char '('; print_foft h; print_char ')'
  | h :: t -> print_char '('; print_foft h; List.iter (fun x -> print_char ','; print_foft x) t; print_char ')'
;;

let rec oiter oc fn sep = function
    [] -> ()
  | [e] -> fn oc e
  | h :: t -> fn oc h; output_string oc sep; oiter oc fn sep t;;

let print_fof_clause l =
  print_char '['; oiter stdout (fun _ i -> print_fofl i) ", " l; print_string "].";;

let print_fol_subst s =
  print_char '{'; Im.iter (fun v t -> print_var v; print_string ":="; print_foft t; print_char ' ') s; print_char '}'
;;

