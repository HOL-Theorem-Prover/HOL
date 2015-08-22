(*-------------------------------------------------------------------------- *)
(* Useful functions used troughout the developments                          *)
(*-------------------------------------------------------------------------- *)

(*--------------------------------------------------------------------------
  Debugging
  -------------------------------------------------------------------------- *)

let log_file file str =
  let oc = open_out_gen [Open_creat; Open_text; Open_append] 0o640 file in
  output_string oc str;
  close_out oc

let logfile = "matching_log"
let logs s = log_file logfile s

let time name f x =
    let t = Sys.time() in
    let fx = f x in
    logs (name ^ ": " ^ string_of_float (Sys.time() -. t) ^ "sec\n");
    fx

let time_here f x =
    let t = Sys.time() in
    let fx = f x in
    print_string (string_of_float (Sys.time() -. t) ^ "sec\n");
    fx

(*--------------------------------------------------------------------------
  IO
  -------------------------------------------------------------------------- *)
let erase_file file =
  let oc = open_out file in 
    output_string oc "";
  close_out oc

let readl file = 
let lines = ref [] in
let chan = open_in file in
try
  while true; do
    lines := input_line chan :: !lines
  done; !lines
with End_of_file ->
  close_in chan;
  List.rev !lines ;;

let writel file strl =
  let oc = open_out file in 
    List.iter (Printf.fprintf oc "%s\n") strl; 
  close_out oc

let append file str =
  let oc = open_out_gen [Open_creat; Open_text; Open_append] 0o640 file in
  output_string oc str;
  close_out oc

(*--------------------------------------------------------------------------
  List
  -------------------------------------------------------------------------- *)

let rec first_n n l =
  if n <= 0 || l = []
  then []
  else List.hd l :: first_n (n - 1) (List.tl l)

let rec mk_set l = match l with
    [] -> []
  | a :: m -> if List.mem a m then mk_set m else a :: mk_set m

let rec sum fl = if fl = [] then 0. else List.hd fl +. (sum (List.tl fl))

(*--------------------------------------------------------------------------
  Hash
  -------------------------------------------------------------------------- *)

let values_of_hash hash = Hashtbl.fold (fun k v l -> v :: l) hash  []
let keys_of_hash hash = Hashtbl.fold (fun k v l -> k :: l) hash []
let alist_of_hash hash = Hashtbl.fold (fun k v l -> (k,v) :: l) hash  []



