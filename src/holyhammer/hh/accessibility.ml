(*-------------------------------------------------------------------------- *)
(* This files contains the necessary functions used in the accessibility     *)
(* experiments.                                                              *)
(*-------------------------------------------------------------------------- *)

open Read
open Hh_parse
open Thf1hh1
open Dependency
open Predict_knn
open Write

(* Output: writing fof problems *)

let eval_dir = "../eval/"
let tmp_file = "predictions/predict_hh_";;
let acc_predictor = KNN

let w_errors = ref [] 

let write_fof_exp file_name (cj_name, axioms) =
  try write_fof file_name (cj_name, axioms)
  with e -> w_errors := e :: !w_errors (* allowing errors (can't prove True) *)

let mkdir s = try Unix.mkdir s 0o777 with Unix.Unix_error (Unix.EEXIST,_,_) -> ()

let rec mkdir_rec s = 
  if s = "." || s = ".." || s = "" || s = "/" then ()
  else (mkdir_rec (Filename.dirname s); mkdir s)
  
(* 
Initialisation need to be performed before experiments on a library
Warning: 
- If a linear order is provided, 
  all theories that belong to this order are ignored
- thydep_file is a string option for the theory graph 
- thylo_file is a string option for the theory linear order. 
*)


let acc_predict n_preds (cj_name,l) =
  let cj = term_of cj_name in
  predict_interactive acc_predictor tmp_file n_preds cj l

let init_acc_env thy_dir thydep_file thylo_file =
  let ((tyl,cl,thml),(thmh,roleh,thmlo)) = Init.init_dir thy_dir in
  let _ = init_dep_env thydep_file thylo_file (thmh,roleh,thmlo) in
  Thf1hh1.parse (tyl,cl,thml) (* creating the term hash *)

(* Experiment 1 *)
let write_dep_thy pdir thy =
  let dir = pdir ^ "/" ^ thy in mkdir_rec dir;
  let f x = 
    let fname = dir ^ "/" ^ Filename.basename x in
    if role_of x = "def" then () 
    else write_fof_exp fname (x,gen_dep x)
  in
    print_string thy;
    List.iter f (thml_of thy);
    print_string "\n"

let write_dep p =
  let pdir = eval_dir ^ "/" ^ p ^ "_dep" in mkdir_rec pdir;
    print_string "Writing dependencies:\n";
    List.iter (write_dep_thy pdir) (all_thys ())

(* Experiment 2 *)
let write_td_thy n pdir thy =
  let dir = pdir ^ "/" ^ thy in mkdir_rec dir;
  let f x = 
    let fname = dir ^ "/" ^ Filename.basename x in
    if role_of x = "def" then () 
    else let l = gen_td x in
      if l = [] then write_fof_exp fname (x,[]) 
      else write_fof_exp fname (x, acc_predict n (x,l)) 
  in  
    List.iter f (thml_of thy)

let write_td n p =
  let pdir = eval_dir ^ "/" ^ p ^ "_td_" ^ (string_of_int n) in mkdir_rec pdir;
    print_string "Writing transitive dependencies:\n";
    List.iter (write_td_thy n pdir) (all_thys ())


(* Experiment 3 *)
let write_loaded_thy n pdir thy =
  let dir = pdir ^ "/" ^ thy in mkdir_rec dir;
  let f x = 
    let fname = dir ^ "/" ^ Filename.basename x in
    if role_of x = "def" then () 
    else write_fof_exp fname (x,acc_predict n (x, gen_loaded x)) 
  in  
    print_string thy; 
    List.iter f (thml_of thy);
    print_string "\n"

let write_loaded n p =
  let pdir = eval_dir ^ "/" ^ p ^ "_loaded_" ^ (string_of_int n) in mkdir_rec pdir;
    print_string "Writing loaded theorems:\n";
    List.iter (write_loaded_thy n pdir) (all_thys ())


(* Experiment 4 *)
let write_lo_thy n pdir thy =
  let dir = pdir ^ "/" ^ thy in mkdir_rec dir;
  let f x = 
    let fname = dir ^ "/" ^ Filename.basename x in
    if role_of x = "def" then () 
    else let l = gen_lo x in
       if l = [] then write_fof_exp fname (x,[])  
       else write_fof_exp fname (x, acc_predict n (x,l)) 
  in  
    print_string thy; 
    List.iter f (thml_of thy);
    print_string "\n"

let write_lo n p =
  let pdir = eval_dir ^ "/" ^ p ^ "_lo_" ^ (string_of_int n) in mkdir_rec pdir;
    print_string "Writing linear order:\n";
    List.iter (write_lo_thy n pdir) !thy_lo


(* Running
terminal command: rlwrap ./top -I hh1
open Accessibility;;
open Read;;
open Dependency;;

(* matching *)


(* hol4 *)
let thy_dir = dir_of_itp "h4";;
let thydep_file = Some (thydep_of_itp "h4");;
let thylo_file = None;;
let exp_name = "h4";;


init_acc_env thy_dir thydep_file thylo_file;;

let cjname = "'list/APPEND_NIL_'";;
let axl = gen_loaded cjname;;
acc_predict 10000 (cjname,axl);;

write_loaded 128 exp_name;;

(* hollight *)
let thy_dir = dir_of_itp "hl";;
let thydep_file = None;;
let thylo_file = None;;

init_acc_env thy_dir thydep_file thylo_file;;

write_dep "hl";;
write_td "hl";;
write_loaded "hl";;
write_lo "hl";; (* any order is chosen here *)
*)

(* Testing
open Dependency;;
let alist_of_hash hash = 
    Hashtbl.fold (fun k v l -> (k,v) :: l) hash  [] ;;
let h = Read.read_thy_graph (thy_graph "h4");;
let h = (!term_hash);;
let h = (!role_hash);;
let h = (!dep_hash);;
let list = (!thm_lo);;
let f hash = Hashtbl.fold  (fun k (v,r) l -> (k,v) :: l) hash  [] ;;
let g hash = Hashtbl.fold  (fun k (v,r) l -> (k,r) :: l) hash  [] ;;
let al = alist_of_hash h;;
*)
 

