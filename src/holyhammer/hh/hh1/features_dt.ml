(* This module defines Discrimination-Tree based features.
   The implementation bases on the HOL Light Nets module. *)

open Lib;;
open Basics;;
open Fusion;;

type term_label = Vnet                          (* variable (instantiable)   *)
                 | Lcnet of (string * int)      (* local constant            *)
                 | Cnet of (int * int)       (* constant                  *)
                 | Lnet of int;;                (* lambda term (abstraction) *)
module Tlm = Map.Make(struct type t = term_label let compare = compare end);;

type 'a net = Netnode of ('a net) Tlm.t * 'a list;;

let empty_net2 = Netnode (Tlm.empty,[]);;

let num = ref 0;;
let next () = num := !num + 1; !num;;

let enter2 =
  let label_to_store tm =
    let op,args = strip_comb tm in
    match op with
      Const (n, _) -> Cnet(n,List.length args),args
    | Abs (bv, bod) -> Lnet(List.length args),bod::args
    | _ -> Vnet,[] in
  let rec sinsert x l = if l = [] then [x] else raise Exit in
  let rec net_update (elem,tms,Netnode(edges,tips)) =
    match tms with
      [] -> Netnode(edges,sinsert elem tips)
    | (tm::rtms) ->
          let label,ntms = label_to_store tm in
          let child,others =
            try let ch = Tlm.find label edges
                in (ch, Tlm.remove label edges)
            with Not_found -> (empty_net2, edges) in
          let new_child = net_update (elem,ntms@rtms,child) in
          let others = Tlm.add label new_child others in
          Netnode (others,tips) in
  fun tm net -> net_update (tm,[tm],net);;

(* ------------------------------------------------------------------------- *)
(* Look up a term in a net and return possible matches.                      *)
(* ------------------------------------------------------------------------- *)

let lookup2 hash =
  let label_for_lookup tm =
    let op,args = strip_comb tm in
    match op with
      Const (n, _) -> Cnet(n,List.length args),args
    | Abs (bv, bod) -> Lnet(List.length args),bod::args
    | Var (vn, _) -> Lcnet(vn,List.length args),args
    | _ -> failwith "should_not_happen" in
  let rec follow (tms,Netnode(edges,tips)) =
    match tms with
      [] -> List.iter (fun x -> Hashtbl.replace hash x ()) tips
    | (tm::rtms) ->
          let label,ntms = label_for_lookup tm in
          try
            let child = Tlm.find label edges in
            follow(ntms @ rtms, child)
          with Not_found -> ();
          if label <> Vnet then begin
            try follow(rtms,Tlm.find Vnet edges) with Not_found -> ()
          end
  in
  fun tm net -> follow([tm],net);;

let rec linearizer = function
    Var _ -> raise Exit
  | Const (s, t) -> Var ("X", t)
  | Abs (t1, t2) -> (try Abs (t1, linearizer t2) with Exit -> Var ("X", mk_fun_ty (type_of t1) (type_of t2)))
  | Comb (t1, t2) -> (try Comb (t1, linearizer t2) with Exit ->
                     try (let lt1 = linearizer t1 in if is_var lt1 then raise Exit; Comb (lt1, t2))
                     with Exit -> Var ("X", snd (dest_fun_ty (type_of t1))))
;;

let rec linearizel = function
    Var _ -> raise Exit
  | Const (s, t) -> Var ("X", t)
  | Abs (t1, t2) -> (try Abs (t1, linearizel t2) with Exit -> Var ("X", mk_fun_ty (type_of t1) (type_of t2)))
  | (Comb (t1, t2) as t) ->
      let (hop, args) = strip_comb t in
        (try list_mk_comb (hop, linearizell args) with Exit ->
           try (let lt1 = linearizel hop in if is_var lt1 then raise Exit; list_mk_comb (lt1, args))
                     with Exit -> Var ("X", type_of t))
and linearizell = function
  [] -> raise Exit
| h :: t -> try (linearizel h) :: t with Exit -> h :: linearizell t
;;

let rec linearize_each = function
    Abs (t1, t2) -> List.map (fun x -> Abs (t1, x)) (linearize_each t2)
  | Const (s, t) -> [mk_var ("X", t)]
  | (Comb (l, r) as t) -> let ll = linearize_each l and rr = linearize_each r in
      let lll =
        List.map (fun x -> if is_var x then mk_var ("X", type_of t) else mk_comb (x, r)) ll
      in List.map (fun x -> mk_comb (l, x)) rr @ lll
  | Var _ -> []
;;

let rec enter_all_linearize left net t =
  try
    let n1 = enter2 t net in
    try
      let t2 = if left then linearizel t else linearizer t in
      enter_all_linearize left n1 t2
    with Exit ->
      n1
  with Exit ->
    (* Optimize: net *)
    try
      let t2 = if left then linearizel t else linearizer t in
      enter_all_linearize left net t2
    with Exit -> net
;;

(*let enter_each net t =
  let l = linearize_each2 t in
  let net = try enter2 t net with Exit -> net in
  List.fold_left (fun sf t -> try enter2 t sf with Exit -> sf) net l
;;*)

(* Only for FOF *)
let rec fold_subterms fn net tm =
  if is_neg tm then fold_subterms fn net (dest_neg tm) else
  if is_exists tm then fold_subterms fn net (snd (dest_exists tm)) else
  if is_forall tm then fold_subterms fn net (snd (dest_forall tm)) else
  if is_conj tm then List.fold_left (fold_subterms fn) net (conjuncts tm) else
  if is_imp tm then let l,r = dest_imp tm in fold_subterms fn (fold_subterms fn net r) l else
  if is_disj tm then List.fold_left (fold_subterms fn) net (disjuncts tm) else
  let net = fn net tm in
  match strip_comb tm with
    _, [] -> net
  | op, args -> List.fold_left (fun sf a -> fold_subterms fn sf a) net args
;;

(*let sublin net tm =
  let fn net tm = enter_all_linearize true net tm in
  let fn net tm = enter_all_linearize false net tm in
  let fn net tm = enter_each net tm in
  let fn net tm = try enter2 tm net with Exit -> net in
  fold_subterms fn net tm
;;*)

let make_net right left single pairs tms =
  let enterl net tms = List.fold_left (fun sf t -> try enter2 t sf with Exit -> sf) net tms in
  let fn net tm =
    let net = try enter2 tm net with Exit -> net in
    let net = if right then enter_all_linearize false net tm else net in
    let net = if left then enter_all_linearize true net tm else net in
    let net = if single then let l = linearize_each tm in enterl net l else net in
    let net = if pairs then
      let l =
        let ts = linearize_each tm in
        setify (List.concat (List.map linearize_each ts))
      in enterl net l else net
    in
    net
  in
  let sublin net tm = fold_subterms fn net tm in
  List.fold_left (fun net t -> sublin net t) (empty_net2) tms
;;

let find_terms =
  let rec accum tl tm =
    let tl' = tm :: tl in
    if is_abs tm then
       accum tl' (body tm)
    else if is_comb tm then
       accum (accum tl' (rator tm)) (rand tm)
    else tl' in
  accum [];;

let features net tm =
  let subs = setify2 (find_terms tm) in
  let hash = Hashtbl.create 100 in
  List.iter (fun t -> lookup2 hash t net) subs;
  Hashtbl.fold (fun k _ sf -> k :: sf) hash []
;;

let rec patterns hash sf = function
    Const (c, _) ->
      let cn = Hashtbl.find Fusion.hash_const_name c in
      Hashtbl.replace hash (sf ^ cn) (); Hashtbl.replace hash cn ()
  | Abs (x, t) ->
      patterns hash (sf ^ "\\-") t
  | (Comb (l, r) as tm) ->
    if is_neg tm then patterns hash sf (dest_neg tm) else
    if is_exists tm then patterns hash sf (snd (dest_exists tm)) else
    if is_forall tm then patterns hash sf (snd (dest_forall tm)) else
    if is_conj tm then List.iter (patterns hash sf) (conjuncts tm) else
    if is_disj tm then List.iter (patterns hash sf) (disjuncts tm) else
    if is_imp tm then let l,r = dest_imp tm in patterns hash sf l; patterns hash sf r else
    let (hop, args) = strip_comb tm in
    let hopa = if is_var hop then "V" else if is_abs hop then "\\" else (fst (dest_const hop)) in
    List.iter (patterns hash (hopa ^ "-")) args;
    List.iter (patterns hash (sf ^ hopa ^ "-")) args
  | Var (x, t) ->
    Hashtbl.replace hash (sf ^ "V") (); Hashtbl.replace hash "V" ()
;;

let patterns tm =
  let hash = Hashtbl.create 100 in
  patterns hash "" tm;
  Hashtbl.fold (fun k _ sf -> k :: sf) hash []
;;

let rec patterns2 hash sf = function
    Const (c, _) ->
      let cn = Hashtbl.find Fusion.hash_const_name c in
      Hashtbl.replace hash (sf ^ cn) (); Hashtbl.replace hash cn ()
  | Abs (x, t) ->
      patterns2 hash "\\-" t
  | (Comb (l, r) as tm) ->
    if is_neg tm then patterns2 hash sf (dest_neg tm) else
    if is_exists tm then patterns2 hash sf (snd (dest_exists tm)) else
    if is_forall tm then patterns2 hash sf (snd (dest_forall tm)) else
    if is_conj tm then List.iter (patterns2 hash sf) (conjuncts tm) else
    if is_disj tm then List.iter (patterns2 hash sf) (disjuncts tm) else
    if is_imp tm then let l,r = dest_imp tm in patterns2 hash sf l; patterns2 hash sf r else
    let (hop, args) = strip_comb tm in
    let hopa = if is_var hop then "V" else if is_abs hop then "\\" else (fst (dest_const hop)) in
    List.iter (patterns2 hash (hopa ^ "-")) args
(*    List.iter (patterns2 hash (sf ^ hopa ^ "-")) args*)
  | Var (x, t) ->
    Hashtbl.replace hash (sf ^ "V") (); Hashtbl.replace hash "V" ()
;;

let patterns tm =
  let hash = Hashtbl.create 100 in
  patterns2 hash "" tm;
  Hashtbl.fold (fun k _ sf -> k :: sf) hash []
;;
