open Hh_parse

(* Tools *)
let rec is_type t = match t with
  | Id "$t" -> true
  | Comb (Comb (Id ">", Id "$t"), x) -> is_type x
  | _ -> false

let is_thm (_,role,_) = role = "ax" || role = "def"
let is_tyc (_,role,_) = role = "ty"
let is_ty (_,_,t) = is_type t

let flatten_tmll l = List.concat (List.map snd l)

let get_tyl_cl_thml l = 
  let (tycl,thml) = List.partition is_tyc l in
  let (tyl,cl) = List.partition is_ty tycl in
  let f (x,_,y) = (x,y) in
  let (tyl,cl,thml) = (List.map f tyl, List.map f cl, List.map f thml) in
   (tyl,cl,thml)

let foreach_filter f tmll = List.map (fun (str,l) -> (str,List.filter f l)) tmll
let foreach_map f tmll = List.map (fun (str,l) -> (str,List.map f l)) tmll
let drop_tt tmll = foreach_map (fun (_,x,y,z) -> (x,y,z)) tmll

let hash_of_alist l = 
  let hash = Hashtbl.create 20000 in
    List.iter (fun (a,b) -> Hashtbl.add hash a b) l;
    hash

(* Splitting disjunctions *)
let splith = Hashtbl.create 20000

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

let rec split_fc vl t = match t with
  | Comb (Id "!", Abs (n, ty, tm)) -> split_fc ((n,ty) :: vl) tm
  | Comb (Comb (Id "&", x), y) -> split_fc vl x @ split_fc vl y
  | _ -> [list_mk_clever_forall (List.rev vl,t)]

let find_split thm = try Hashtbl.find splith thm 
                     with Not_found -> failwith ("find_split: " ^ thm)

let split_fc_thy (thy,tml) =
  let splits (s,r,t) =
    let tml = split_fc [] t in
    let i = ref 0 in
    let f x = (x, (i := !i + 1; s ^ "_s" ^ string_of_int !i)) in
    let tnl = if List.length tml = 1 then [(t,s)] 
             else (i := 0; List.map f tml)
    in
      Hashtbl.add splith s (List.map snd tnl); 
      List.map (fun (t1,s1) -> (s1,r,t1)) tnl
  in
    (thy,List.concat (List.map splits tml))

let modify_dep deph =
  let h1 = Hashtbl.create 20000 in
  let h2 = Hashtbl.create 20000 in 
  let split_dep h thm (thy,l) =
    Hashtbl.add h thm (thy, List.concat (List.map find_split l))  
  in
  let split_thm h thm (thy,l) =  
    let sl = find_split thm in
      List.iter (fun x -> Hashtbl.add h x (thy,l)) sl  
  in
  Hashtbl.iter (split_dep h1) deph;
  Hashtbl.iter (split_thm h2) h1; 
    h2

let split_fc_all (deph,tmll) = 
  Hashtbl.clear splith;
  let tmll_r = List.map split_fc_thy tmll in
    (modify_dep deph,tmll_r)

let miz_split_fc tmll = (Hashtbl.clear splith; List.map split_fc_thy tmll)

(* Initialization *)
let print_info (dir,tyl,cl,thml,thmlo) =
  print_string ("Loading objects from " ^ dir ^ "\n");
  print_string ("- types: " ^ string_of_int (List.length tyl) ^ "\n");
  print_string ("- constants: " ^ string_of_int (List.length cl) ^ "\n");
  print_string ("- theorems: " ^ string_of_int (List.length thml) ^ "\n");
  print_string ("- theories: "^ string_of_int (List.length thmlo) ^ "\n\n")

let print_info_miz (dir,thml,thmlo) =
  print_string ("Loading objects from " ^ dir ^ "\n");
  print_string ("- theorems: " ^ string_of_int (List.length thml) ^ "\n");
  print_string ("- theories: "^ string_of_int (List.length thmlo) ^ "\n\n")

let init_dir dir =
  let (deph,tmll) = Read.alt_read_dir dir in
  let tmll = drop_tt tmll in
  let (deph,tmll) = split_fc_all (deph,tmll) in
  let (tyl,cl,thml) = get_tyl_cl_thml (flatten_tmll tmll) in
  let tmll = foreach_filter (is_thm) tmll in
  let thmlo = foreach_map (fun (x,y,z) -> x) tmll in 
  let roleh = hash_of_alist (List.map (fun (x,y,z) -> (x,y)) (flatten_tmll tmll)) in
    print_info (dir,tyl,cl,thml,thmlo);
    ((tyl,cl,thml),(deph,roleh,thmlo))

