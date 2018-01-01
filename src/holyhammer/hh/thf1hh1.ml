open Hh_parse
(* Global references *)                                
let const_tyvarl = ref [];;
let init_type = ("$i", 0) :: !Fusion.the_type_constants;;
Fusion.new_constant ("$equals",List.assoc "=" (Fusion.constants ()));;
let init_const = Fusion.constants();;
let (term_hash : (string,Fusion.term) Hashtbl.t ref) = ref (Hashtbl.create 20000)
let term_of n = Hashtbl.find (!term_hash) n

(* HH tools *)
let rec hh_to_string hhterm = match hhterm with
    Abs (a,x,y) -> "Abs " ^ a ^ ":" ^ hh_to_string x ^ "," ^ hh_to_string y
  | Comb (x,y)  -> "(" ^ hh_to_string x ^ " " ^ hh_to_string y ^ ")"
	| Id a        -> a				

let rec strip_comb acc = function
  | Comb (x, y) -> strip_comb (y :: acc) x
  | t -> (t, acc)

let rec isNtType sf = function
    Id "$t" -> Some sf
  | Comb (Comb (Id ">", Id "$t"), x) -> isNtType (sf + 1) x
  | _ -> if sf = 0 then None else failwith "isNtType"

let hash_of_alist l = 
  let hash = Hashtbl.create 20000 in
    List.iter (fun (a,b) -> Hashtbl.add hash a b) l;
    hash

let alist_of_hash hash = 
    Hashtbl.fold (fun k v l -> (k,v) :: l) hash  []

(* Parse type *)
let quantl = ref [];;
let rec ptypea tvl hht = match hht with
    Comb (Id "!", Abs (n,Id "$t", tm)) -> 
			quantl := (Fusion.mk_vartype n) :: (!quantl); ptypea (n :: tvl) tm
  | Comb (Comb (Id ">", x), y) -> Fusion.mk_type ("fun", [ptypea tvl x; ptypea tvl y])
  | Id "$o" -> Fusion.bool_ty
  | Id x -> if List.mem x tvl then Fusion.mk_vartype x else Fusion.mk_type (x, [])
  | Comb _ as t -> begin
		   match strip_comb [] t with
                     (Id x,tyl) -> Fusion.mk_type (x, List.map (ptypea tvl) tyl)
                     | _          -> failwith ("ptypea: " ^ hh_to_string hht)
                  end
 | _ -> failwith ("ptypea: " ^ hh_to_string hht)

let ptypeb tvl t = quantl := []; let res = ptypea tvl t in (List.rev !quantl,res)
let ptype tvl t = snd (ptypeb tvl t)


let pnot = Hl_parser.parse_term "~"
let pt = Hl_parser.parse_term "T"
let pf = Hl_parser.parse_term "F"

let rec pterm tvl vl t = match t with
  | Abs (n, ty, tm) ->
      let ty = ptype tvl ty in Fusion.mk_abs (Fusion.mk_var (n, ty), pterm tvl ((n, ty) :: vl) tm)
  | Comb (Id "!", Abs (n, ty, tm)) ->
      if ty = Id "$t" then pterm (n :: tvl) vl tm else
      let ty = ptype tvl ty in Bool.mk_forall (Fusion.mk_var (n, ty), pterm tvl ((n, ty) :: vl) tm)
  | Comb (Id "?", Abs (n, ty, tm)) ->
      let ty = ptype tvl ty in Bool.mk_exists (Fusion.mk_var (n, ty), pterm tvl ((n, ty) :: vl) tm)
  | Comb (Id "~", x) -> Fusion.mk_comb (pnot, pterm tvl vl x)
  | Comb (Comb (Id "=", x), y) -> Fusion.mk_eq (pterm tvl vl x, pterm tvl vl y)
  | Comb (Comb (Id "=>", x), y) -> Bool.mk_imp (pterm tvl vl x, pterm tvl vl y)
  | Comb (Comb (Id "&", x), y) -> Bool.mk_conj (pterm tvl vl x, pterm tvl vl y)
  | Comb (Comb (Id "|", x), y) -> Basics.mk_binary "\\/" (pterm tvl vl x, pterm tvl vl y)
  | (Comb _ as t) -> pterm_comb tvl vl t
  | Id "$true" -> pt
  | Id "$false" -> pf
  | Id x -> try let ty = List.assoc x vl in Fusion.mk_var (x, ty) with Not_found -> Fusion.mk_const (x, [])
  | _ -> pterm_comb tvl vl t
and pterm_comb tvl vl t = match strip_comb [] t with
    (Id x, rl) -> begin 
        try let ty = List.assoc x vl in 
          Basics.list_mk_comb (Fusion.mk_var (x,ty), List.map (pterm tvl vl) rl)
	with Not_found -> 
          let itvl = try List.assoc x !const_tyvarl with _ -> failwith ("undeclared constant: " ^ x) in
          let (tyl,tml) = Lib.chop_list (List.length itvl) rl in
          let tyl = List.map (ptype tvl) tyl in
          let tml = List.map (pterm tvl vl) tml in
          let c = Fusion.mk_const (x,List.combine tyl itvl) in
            Basics.list_mk_comb (c,tml)
		 end
  | (lt, rl) -> Basics.list_mk_comb (pterm tvl vl lt,List.map (pterm tvl vl) rl)

let pterm t = try pterm [] [] t 
  with | Failure s -> failwith ("pterm: " ^ s ^ " in: " ^ hh_to_string t) 
       | _         -> failwith ("pterm: " ^ hh_to_string t) 


(* Parse and initialize types and constants *)
let rm_used_id l1 l2 = 
  List.filter (fun (id,_) -> not (List.mem id (List.map fst l2))) l1

let parse_type (ty_name,ty) = match isNtType 0 ty with
  | None -> failwith ("parse_type: " ^ ty_name ^ ": " ^ hh_to_string ty)
  | Some n -> (ty_name,n)

let parse_init_tyc (tyl,cl) =
  let tys = List.map parse_type tyl in
  let lty = init_type @ rm_used_id tys init_type in
    Fusion.the_type_constants := lty;
    print_string ("- types: " ^ string_of_int (List.length lty) ^ " \n");
  let cs0 = List.map (fun (a, b) -> (a, ptypeb [] b)) cl in
  let cs1 = List.map (fun (a,(b,c)) -> (a,c)) cs0 in
  let cs2 = List.map (fun (a,(b,c)) -> (a,b)) cs0 in
  let lc = init_const @ rm_used_id cs1 init_const in
    Fusion.set_term_constants lc;
    print_string ("- constants: "  ^ string_of_int (List.length lc) ^ " \n");
    const_tyvarl := ("$equals",[Fusion.aty]) :: cs2 
;;

let parse_axdef thml = 
  let f (s,t) = (s,pterm t) in List.map f thml

(* Main function *)
let parse (tyl,cl,thml) = 
  print_string ("Parsing objects \n");
  parse_init_tyc (tyl,cl);
  let thml = parse_axdef thml in
  let tmh = hash_of_alist thml in
   print_string ("- theorems: "^ string_of_int (List.length thml) ^ "\n\n"); 
   (term_hash := tmh)
;;




         




