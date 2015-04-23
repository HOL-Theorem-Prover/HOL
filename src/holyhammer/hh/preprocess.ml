(*--------------------------------------------------------------------------- *)
(* This files contains the data-preprocessing done after the reading phase    *)
(* namely: splitting conjunctions and more later.                             *)
(*--------------------------------------------------------------------------- *)

open Hh_parse

(*--------------------------------------------------------------------------- 
  Prefixing objects (necessary for matching between different libraries).
  --------------------------------------------------------------------------- *)
(* Warning: only prefix quoted names *)
let remove_prime s =
  let n = String.length s in
  Str.last_chars (Str.first_chars s (n - 1)) (n- 2) 

let give_prefix prefix name =
  if name.[0] = '\'' && name.[String.length name - 1] = '\''
    then "\'" ^ prefix ^ remove_prime name ^ "\'"
    else name

let rec bv_of t = match t with
  | Abs (n,ty,tm) -> n :: (bv_of ty @ bv_of tm)
  | Comb (x,y)    -> bv_of x @ bv_of y
  | Id x          -> []

let prefix_entry prefix (s,r,t) =
  let bvl = bv_of t in 
  let is_free fv = not (List.mem fv bvl) in
  let rec f tm = match tm with 
    | Abs (v,ty,tm') -> Abs (v, f ty, f tm')
    | Comb (x,y)     -> Comb (f x, f y)
    | Id x           -> if is_free x then Id (give_prefix prefix x) else Id x
  in
    (give_prefix prefix s,r,f t)	

let prefix_deph prefix h =
  let h_res = Hashtbl.create 20000 in
  let f thm (thy,depl) = 
    let new_thm = give_prefix prefix thm in
    let new_depl = List.map (give_prefix prefix) depl in
      Hashtbl.add h_res new_thm (thy,new_depl)
  in
    Hashtbl.iter f h;
    h_res


(*--------------------------------------------------------------------------- 
  Splitting conjunctions under the quantifiers. (not necessary for hol4)
  --------------------------------------------------------------------------- *)

(* Hashtable used by hollight, hol4 and mizar. 
   Warning: need to be cleaned before usage *)
let splith = Hashtbl.create 20000

let find_split thm = try Hashtbl.find splith thm 
                     with Not_found -> failwith ("find_split: " ^ thm)

(* name tools *)
let app_info s info =
  let add_prime s = "\'" ^ s ^ "\'" in
  let remove_prime s =
    let n = String.length s in
    Str.last_chars (Str.first_chars s (n - 1)) (n- 2) 
  in
  if s.[0] = '\'' && s.[String.length s - 1] = '\''
    then add_prime (remove_prime s ^ info)
    else s ^ info

(* accessors and constructors for the AST *)
let rec all_id t = match t with 
  | Comb (x,y) -> all_id x @ all_id y
  | Abs (n,ty,tm) -> n :: (all_id ty @ all_id tm)
  | Id x          -> [x]

let mk_forall ((n,ty),t) = Comb (Id "!",Abs (n, ty, t))

let mk_clever_forall ((n,ty),t) = 
  if List.mem n (all_id t) then mk_forall ((n,ty),t) else t

let rec list_mk_clever_forall (vl,t) = match vl with
  | [] -> t
  | a :: m -> mk_clever_forall (a,list_mk_clever_forall (m,t))

(* splitting each entry into multiple entries *)
let rec split_term vl t = match t with
  | Comb (Id "!", Abs (n, ty, tm)) -> split_term ((n,ty) :: vl) tm
  | Comb (Comb (Id "&", x), y) -> split_term vl x @ split_term vl y
  | _ -> [list_mk_clever_forall (List.rev vl,t)]

let split_entry (name,role,term) =
  let conjl = split_term [] term in
  let i = ref 0 in
  let name_conj x = 
    let entry = (app_info name ("s" ^ string_of_int !i), role, x) in
    incr i; entry
  in
  let entryl = if List.length conjl = 1 
               then [(name,role,term)] 
               else List.map name_conj conjl
  in
  (* save how the term was splitted to be able to recompute the dependencies *)
  Hashtbl.add splith name (List.map (fun (n,r,t) -> n) entryl); 
  entryl

let split_thy (thy,entryl) = (thy,List.concat (List.map split_entry entryl))

(* splitting dependencies: need to be done after splitting terms *)
let split_deph deph =
  let h1 = Hashtbl.create 20000 in
  let h2 = Hashtbl.create 20000 in 
  let split_depl h thm (thy,l) =
    Hashtbl.add h thm (thy, List.concat (List.map find_split l))  
  in
  let split_thm h thm (thy,depl) =  
    let conjl = find_split thm in
      List.iter (fun x -> Hashtbl.add h x (thy,depl)) conjl
  in
  Hashtbl.iter (split_depl h1) deph;
  Hashtbl.iter (split_thm h2) h1; 
    h2

let split_lib (deph,tmll) = 
  Hashtbl.clear splith;
  let new_tmll = List.map split_thy tmll in (* keep it before split_deph *) 
    (split_deph deph,new_tmll)
    


