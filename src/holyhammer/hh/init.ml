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

(* Initialization *)
let print_info (dir,tyl,cl,thml,thmlo) =
  print_string ("Loading objects from " ^ dir ^ "\n");
  print_string ("- types: " ^ string_of_int (List.length tyl) ^ "\n");
  print_string ("- constants: " ^ string_of_int (List.length cl) ^ "\n");
  print_string ("- theorems: " ^ string_of_int (List.length thml) ^ "\n");
  print_string ("- theories: "^ string_of_int (List.length thmlo) ^ "\n\n")

let init_dir dir =
  let (deph,tmll) = Read.alt_read_dir dir in
  let tmll = drop_tt tmll in
  let (tyl,cl,thml) = get_tyl_cl_thml (flatten_tmll tmll) in
  let tmll = foreach_filter (is_thm) tmll in
  let thmlo = foreach_map (fun (x,y,z) -> x) tmll in 
  let roleh = hash_of_alist (List.map (fun (x,y,z) -> (x,y)) (flatten_tmll tmll)) in
    print_info (dir,tyl,cl,thml,thmlo);
    ((tyl,cl,thml),(deph,roleh,thmlo))

