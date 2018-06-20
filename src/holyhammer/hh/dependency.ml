
(* These are structures specific to the relation between dependencies *)

(* string sets *)
module Ss = Set.Make(struct type t = string let compare = compare end);;

let rec mk_set l = match l with
    [] -> Ss.empty
  | a :: m -> Ss.add a (mk_set m)

let rec xunion setl = 
  match setl with 
    [] -> Ss.empty
  | set :: m ->  Ss.union set (xunion m)


(***** Global references (to be initialised before usage)  *****)
(* 
   dep_hash  : thm -> (thy,dep)
   role_hash : thm -> role
   thm_lo    : thy -> thml
   thy_hash  : thy -> thyl
   seq_hash  : thm -> int
*)


let (dep_hash : (string,(string * string list)) Hashtbl.t ref) = 
  ref (Hashtbl.create 20000)
let (role_hash : (string,string) Hashtbl.t ref) = 
  ref (Hashtbl.create 20000)
let thm_lo = ref []
let (thy_hash : (string,string list) Hashtbl.t ref) = ref (Hashtbl.create 1000)
let (thy_td_hash : (string,string list) Hashtbl.t ref) = ref (Hashtbl.create 1000)
let (thm_td_hash : (string,string list) Hashtbl.t ref) = ref (Hashtbl.create 20000)
let (seq_hash : (string,int) Hashtbl.t ref ) = ref (Hashtbl.create 20000)
let thy_lo = ref []

(* Accessors *)
let thy_of thm = try fst (Hashtbl.find (!dep_hash) thm)
                 with _ -> failwith ("Not found theorem: " ^ thm)
let dep_of thm = try snd (Hashtbl.find (!dep_hash) thm) 
                 with _ -> failwith  ("Not found theorem: " ^ thm)
let role_of thm = try Hashtbl.find (!role_hash) thm
                 with _ -> failwith ("Not found theorem: " ^ thm)

let thml_of thy = try List.assoc thy (!thm_lo)
                  with _ -> failwith ("Not found theory in thm_lo: " ^ thy)
let all_thys ()  = List.map fst (!thm_lo)
let dep_of_thy thy = try Hashtbl.find (!thy_hash) thy
                     with _ -> failwith ("Not found theory in thy_hash: " ^ thy)  
let thml_of_thyl thyl = List.concat (List.map thml_of thyl)

let all_thms () = thml_of_thyl (all_thys ())

let seq_of thm = try Hashtbl.find (!seq_hash) thm
                 with _ -> failwith ("Not found theorem: " ^ thm)

let rec rm_dupl l = match l with
  | [] -> []
  | a :: m -> if List.mem a m then rm_dupl m else a :: rm_dupl m

let rec td_of_check thmog thm =   
  if thm = thmog then failwith ("Theorem loop: " ^ thm) else
  try Hashtbl.find !thm_td_hash thm with Not_found ->  
  begin 
    let thml = dep_of thm in
    let res =  rm_dupl (List.concat (thml :: List.map (td_of_check thmog) thml)) in
      Hashtbl.add !thm_td_hash thm res; res
  end

let rec td_of thm =   
  try Hashtbl.find !thm_td_hash thm with Not_found ->  
  begin 
    let thml = dep_of thm in
    let res =  rm_dupl (List.concat (thml :: List.map (td_of_check thm) thml)) in
      Hashtbl.add !thm_td_hash thm res; res
  end

let rec td_of_thy_check thyog thy =
  if thy = thyog then failwith ("Theory loop: " ^ thy) else
  try Hashtbl.find !thy_td_hash thy with Not_found -> 
  begin
    let thyl = dep_of_thy thy in
    let res = rm_dupl (List.concat (thyl :: List.map (td_of_thy_check thyog) thyl)) in
      Hashtbl.add !thy_td_hash thy res; res
  end

let rec td_of_thy thy =
  try Hashtbl.find !thy_td_hash thy with Not_found -> 
  begin
    let thyl = dep_of_thy thy in
    let res = rm_dupl (List.concat (thyl :: List.map (td_of_thy_check thy) thyl)) in
      Hashtbl.add !thy_td_hash thy res; res
  end

let rm_trans_edge l1 = 
  let s2 = xunion (List.map (Lib.o mk_set td_of_thy) l1) in
    Ss.elements (Ss.diff (mk_set l1) s2)

let rm_trans_thy_hash () =
  let hmem = !thy_hash in
  let hres = Hashtbl.create 1000 in
  let f k v = Hashtbl.add hres k (rm_trans_edge v) in
    Hashtbl.iter f hmem; thy_hash := hres

(* Require dep_hash, thm_lo, optionally a thy_graph file *)
let init_thy_hash fname = 
  Hashtbl.clear !thy_hash;
  match fname with
  | Some s -> (print_string ("- loading theory graph from: " ^ s ^ "\n");
               thy_hash := Read.read_thy_graph s)
  | None   ->
    begin
    print_string ("- infering theory graph from dependencies\n");
    let add thy = 
      let nl = thml_of thy in
      let dnl = List.concat (List.map dep_of nl) in
      let thyset = mk_set (List.map thy_of dnl) in
        Hashtbl.add (!thy_hash) thy (Ss.elements (Ss.remove thy thyset))
    in
      List.iter add (all_thys ())
    end

let init_thm_td_hash () =
  print_string "- computing transitive dependencies of theorems\n";
  Hashtbl.clear (!thm_td_hash);
  List.iter (Lib.o ignore td_of) (all_thms ())

let init_thy_td_hash () =
  print_string "- computing transitive dependencies of theories\n";
  Hashtbl.clear (!thy_td_hash);
  List.iter (Lib.o ignore td_of_thy) (all_thys ())


(* Linear order *)
let rec prevl l e = match l with
    [] -> failwith "prevl: Not_found"
  | a :: m -> if a = e then [] else a :: prevl m e

(* gives a sequential number to a theories and theorems *)
let rec sort_thyl thyl = match thyl with 
  | [] -> []
  | thy :: m -> let l = td_of_thy thy in
                let (l1,l2) = List.partition (fun x -> List.mem x l) m in 
                   sort_thyl l1 @ [thy] @ sort_thyl l2
 
let init_seq_hash fname =
  let seq_n = ref 0 in
  let add_thm_seq_hash thm = 
    Hashtbl.add !seq_hash thm !seq_n;
    seq_n := !seq_n + 1
  in
  let add_thy_seq_hash thy =
    List.iter add_thm_seq_hash (thml_of thy)  
  in
    Hashtbl.clear !seq_hash;
    let thyl = match fname with 
       | Some s -> (print_string ("- loading theory order from: " ^ s ^ "\n"); 
                    Read.read_thy_lo s)
       | None   -> (print_string ("- infering order of theories \n");
                    sort_thyl (all_thys ()))              
    in
    thy_lo := thyl;
    List.iter add_thy_seq_hash thyl

(* Environnement:
fname1 is a string option for the theory graph 
fname2 is a string option for the theory linear order. 
*)
let init_dep_env fname1 fname2 (deph,roleh,thmlo) =
  print_string "Defining accessibility functions: \n";
  dep_hash := deph;
  role_hash := roleh;
  thm_lo := thmlo;
  init_thy_hash fname1;
  Hashtbl.clear (!thm_td_hash);
  (* init_thm_td_hash (); *)
  init_thy_td_hash ();
  rm_trans_thy_hash ();
  init_seq_hash fname2; (* initialize also thy_lo *)
  (Hashtbl.copy !dep_hash, 
   Hashtbl.copy !role_hash, 
   !thm_lo, 
   Hashtbl.copy !thy_hash, 
   Hashtbl.copy !thy_td_hash, 
   Hashtbl.copy !thm_td_hash, 
   Hashtbl.copy !seq_hash, 
   !thy_lo)

let set_dep_env (deph,roleh,thmlo,thyh,thytdh,thmtdh,seqh,thylo) =
   dep_hash := deph; role_hash := roleh; thm_lo := thmlo; 
   thy_hash := thyh; 
   thy_td_hash := thytdh;
   thm_td_hash := thmtdh;
   seq_hash := seqh;
   thy_lo  := thylo

(* Methods *)
let sort_thml thml = 
  let compare_thm thm1 thm2 = compare (seq_of thm1) (seq_of thm2) in
    List.sort compare_thm thml

let gen_dep thm = sort_thml (dep_of thm)
let gen_td thm = sort_thml (td_of thm)
let gen_loaded thm =
  let thy = thy_of thm in
  let pnl = prevl (thml_of thy) thm in
  let anl = thml_of_thyl (td_of_thy thy) in
    sort_thml (pnl @ anl)

let gen_lo thm =
  let thy = thy_of thm in
  let pnl = prevl (thml_of thy) thm in
  let anl = thml_of_thyl (prevl (!thy_lo) thy) in
    sort_thml (pnl @ anl)

let gen_all () = sort_thml (thml_of_thyl (all_thys()))

