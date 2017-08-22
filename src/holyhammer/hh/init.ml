(*-------------------------------------------------------------------------- *)
(* Organize the libraries by theorems, types and constants. Give also        *)
(* additional information about the theorems such as their dependencies and  *)
(* originated theories (deph), their role (roleh) and the order (thmlo) in   *)
(* which the theorems were proved inside their theory.                       *)                   
(*-------------------------------------------------------------------------- *)

open Hh_parse
open Preprocess

(* object partition *)
let rec is_type t = match t with
  | Id "$t" -> true
  | Comb (Comb (Id ">", Id "$t"), x) -> is_type x
  | _ -> false

let is_thm (_,role,_) = role = "ax" || role = "def"
let is_tyc (_,role,_) = role = "ty"
let is_ty (_,_,t) = is_type t

let get_tyl_cl_thml l = 
  let (tycl,thml) = List.partition is_tyc l in
  let (tyl,cl) = List.partition is_ty tycl in
  let f (x,_,y) = (x,y) in
  let (tyl,cl,thml) = (List.map f tyl, List.map f cl, List.map f thml) in
  (tyl,cl,thml)

(* Transforming the lists of terms by theory *)
let flatten_tmll l = List.concat (List.map snd l)
let foreach_filter f tmll = List.map (fun (thy,l) -> (thy,List.filter f l)) tmll
let foreach_map f tmll = List.map (fun (thy,l) -> (thy,List.map f l)) tmll
let drop_tt tmll = foreach_map (fun (_,s,r,t) -> (s,r,t)) tmll

(* Creating a hash from a associative list *)
let hash_of_alist l = 
  let hash = Hashtbl.create (List.length l) in
  List.iter (fun (a,b) -> Hashtbl.add hash a b) l;
  hash

(* Initialization *)
let print_info (dir,tyl,cl,thml,thmlo) =
  print_string ("Loading objects from " ^ dir ^ "\n");
  print_string ("- types: " ^ string_of_int (List.length tyl) ^ "\n");
  print_string ("- constants: " ^ string_of_int (List.length cl) ^ "\n");
  print_string ("- theorems: " ^ string_of_int (List.length thml) ^ "\n");
  print_string ("- theories: "^ string_of_int (List.length thmlo) ^ "\n\n")

let really_big_theorems = ref [] (* only used for information *)

let init_dir dir =
  let (deph,tmll) = Read.read_dir dir in
  let tmll = drop_tt tmll in (* remove the TPTP "tt" prefix *)
  (* let (deph,tmll) = split_lib (deph,tmll) in *) (* splits under quantifiers removed *)
  let (tyl,cl,thml) = get_tyl_cl_thml (flatten_tmll tmll) in
  really_big_theorems := 
  List.map fst (List.filter (fun (_,t) -> size_of t >= 2000) thml);
  let big_thml = !really_big_theorems in
  let tmll = foreach_filter (fun (s,r,t) -> is_thm (s,r,t) && not (List.mem s big_thml)) tmll in
  let short_thml = List.filter (fun (s,_) -> not (List.mem s big_thml)) thml in
  let deph = remove_deph big_thml deph in
  let thmlo = foreach_map (fun (s,r,t) -> s) tmll in 
  let roleh = hash_of_alist (List.map (fun (s,r,t) -> (s,r)) (flatten_tmll tmll)) in
  print_info (dir,tyl,cl,thml,thmlo);
  ((tyl,cl,short_thml),(deph,roleh,thmlo))

let init_dir_features dir =
  let ((tyl,cl,thml),(deph,roleh,thmlo)) = init_dir dir in
  let (feah,fea_thyl) = Read.read_features_dir dir in
  ((tyl,cl,thml),(deph,roleh,thmlo),(feah,fea_thyl))

(* Gives an additional prefix to all the objects in the directory 
   (useful for matching different libraries)
*)
let init_dir_prefix prefix dir =
  let (deph,tmll) = Read.read_dir dir in
  let tmll = drop_tt tmll in (* remove the TPTP "tt" prefix *)
  (* prefix *)
  let tmll = foreach_map (prefix_entry prefix) tmll in
  let deph = prefix_deph prefix deph in
  (* split *)
  let (deph,tmll) = split_lib (deph,tmll) in
  (* *)
  let (tyl,cl,thml) = get_tyl_cl_thml (flatten_tmll tmll) in
  let tmll = foreach_filter (is_thm) tmll in
  let thmlo = foreach_map (fun (s,r,t) -> s) tmll in 
  let roleh = hash_of_alist (List.map (fun (s,r,t) -> (s,r)) (flatten_tmll tmll)) in
  print_info (dir,tyl,cl,thml,thmlo);
  ((tyl,cl,thml),(deph,roleh,thmlo))

