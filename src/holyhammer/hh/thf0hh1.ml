open Hh_parse;;

let rec isNtType sf = function
  | Id "$tType" -> Some sf
  | Hh_parse.Comb (Hh_parse.Comb (Hh_parse.Id ">", Id "$tType"), x) -> isNtType (sf + 1) x
  | Id "$t" -> Some sf
  | Hh_parse.Comb (Hh_parse.Comb (Hh_parse.Id ">", Id "$t"), x) -> isNtType (sf + 1) x
  | _ -> if sf = 0 then None else failwith "isNtType"
;;

let process (tys, cs, axs, conj) = function
    (_, "type", Comb (Comb (Id ":", Id x), y)) ->
      (match isNtType 0 y with
         Some n -> ((x, n) :: tys, cs, axs, conj)
       | None -> (tys, (x, y) :: cs, axs, conj)
      )
  | (x, "ty", y) ->
      (match isNtType 0 y with
         Some n -> ((x, n) :: tys, cs, axs, conj)
       | None -> (tys, (x, y) :: cs, axs, conj)
      )
  | (x, "axiom", y) -> (tys, cs, (x, y) :: axs, conj)
  | (x, "ax", y)    -> (tys, cs, (x, y) :: axs, conj)
  | (x, "hypothesis", y) -> (tys, cs, (x, y) :: axs, conj)
  | (x, "definition", y) -> (tys, cs, (x, y) :: axs, conj)
  | (x, "conjecture", y) -> (tys, cs, axs, (x, y) :: conj)
  | (_, x, _) -> failwith ("process: " ^ x)
;;

let rec strip_comb acc = function
  | Comb (x, y) -> strip_comb (y :: acc) x
  | t -> (t, acc)
;;

let rec ptype tvl = function
    Comb (Id "!", Abs (n, Id "$tType", tm)) -> ptype (n :: tvl) tm
  | Comb (Id "!", Abs (n, Id "$t", tm)) -> ptype (n :: tvl) tm
  | Comb (Comb (Id ">", x), y) -> Fusion.mk_type ("fun", [ptype tvl x; ptype tvl y])
  | Id "$o" -> Fusion.mk_type ("bool", [])
  | Id x -> (try Fusion.mk_vartype (Printf.sprintf "%03i" (List.length tvl - Lib.index x tvl)) with _ -> Fusion.mk_type (x, []))
  | (Comb _ as ty) ->
    (match strip_comb [] ty with
	    (Id x, tyl) -> Fusion.mk_type (x, List.map (ptype tvl) tyl)
		| _   -> failwith "ptype1")
  | _ -> failwith "ptype2"
;;

let pnot = Hl_parser.parse_term "~";;
let pt = Hl_parser.parse_term "T";;
let pf = Hl_parser.parse_term "F";;

let rec pterm env tvl = function
    Abs (n, ty, tm) ->
      let ty = ptype tvl ty in Fusion.mk_abs (Fusion.mk_var (n, ty), pterm ((n, ty) :: env) tvl tm)
  | Comb (Id "!", Abs (n, Id "$tType", tm)) -> pterm env (n :: tvl) tm
  | Comb (Id "!", Abs (n, ty, tm)) ->
      let ty = ptype tvl ty in Bool.mk_forall (Fusion.mk_var (n, ty), pterm ((n, ty) :: env) tvl tm)
  | Comb (Id "?", Abs (n, ty, tm)) ->
      let ty = ptype tvl ty in Bool.mk_exists (Fusion.mk_var (n, ty), pterm ((n, ty) :: env) tvl tm)
  | Comb (Id "~", x) -> Fusion.mk_comb (pnot, pterm env tvl x)
  | Comb (Comb (Id "=", x), y) -> Fusion.mk_eq (pterm env tvl x, pterm env tvl y)
  | Comb (Comb (Id "=>", x), y) -> Bool.mk_imp (pterm env tvl x, pterm env tvl y)
  | Comb (Comb (Id "&", x), y) -> Bool.mk_conj (pterm env tvl x, pterm env tvl y)
  | Comb (Comb (Id "|", x), y) -> Basics.mk_binary "\\/" (pterm env tvl x, pterm env tvl y)
  | (Comb _ as t) -> pterm_comb env tvl t
  | Id "$true" -> pt
  | Id "$false" -> pf
  | Id x ->
      try let ty = List.assoc x env in Fusion.mk_var (x, ty)
      with Not_found -> try Fusion.mk_const (x, []) with _ -> failwith ("pterm: mk_const: " ^ x)
and pterm_comb env tvl t =
  match strip_comb [] t with
    (Id s, rl) ->
      begin try let ty = List.assoc s env in Basics.list_mk_comb (Fusion.mk_var (s,ty),List.map (pterm env tvl) rl)
      with Not_found ->
        let tyv = Lib.setify (Fusion.tyvars (Fusion.get_const_type s)) in
        let tya, tma = Lib.chop_list (List.length tyv) rl in
        let tya = List.map (ptype tvl) tya
        and tma = List.map (pterm env tvl) tma in
        let c = Fusion.mk_const (s, List.combine tya tyv) in
        Basics.list_mk_comb (c, tma)
      end
  | (l, rl) -> Basics.list_mk_comb (pterm env tvl l,List.map (pterm env tvl) rl)
let rxp = Str.regexp "'";;
let apos = Str.global_replace rxp "\\'";;

let rxpfile = Str.regexp "axiom.*,file[(][']";;
let rxpu = Str.regexp "u_";;
let rxpo = Str.regexp "o_";;
let rxpi = Str.regexp "i_";;
let unrxp s = Str.global_replace rxpo "." (Str.global_replace rxpi "'" (Str.global_replace rxpu "_" s));;

let get_deps fname =
  let ic = open_in fname in
  let sf = ref [] in
  (try while true do
    let l = input_line ic in
    try ignore (Str.search_forward rxpfile l 0);
      let q1 = String.index l '\'' in
      let q2 = String.index_from l (q1 + 1) '\'' in
      sf := unrxp (String.sub l (q2 + 4) (String.length l - q2 - 7)) :: !sf
    with Not_found -> ()
  done with End_of_file -> ());
  !sf
;;

let run_prover time fname prover =
  let cmd = match prover with
    "v" -> "vampire --mode casc -t " ^ time ^ " --proof tptp --output_axiom_names on " ^ fname
  | "z" -> "z3 -tptp DISPLAY_UNSAT_CORE=true -T:" ^ time ^ " " ^ fname
  | "e" -> "eproof -s --tstp-format --cpu-limit=" ^ time ^ "  " ^ fname
  | "E" -> "runepar.pl " ^ time ^ " 0 " ^ fname ^ " 2 1"
  | x -> "eproof -s --tstp-format --cpu-limit=" ^ time ^ " " ^ ((*apos*) x) ^ " " ^ fname
  in
  let fnameo = fname ^ "o" in
  let cmd = cmd ^ " > " ^ fnameo ^ " 2> /dev/null" in
(*  print_endline cmd;*)
(*  Predict.unlink := fnameo :: !Predict.unlink;*)
  ignore (Sys.command cmd);
  if Sys.command ("grep -q 'SZS status Theorem' " ^ fnameo) = 0 then Some (get_deps fnameo) else None
(*  if Sys.command ("grep -q 'SZS status Timeout' " ^ fnameo) = 0 then -1 else 1*)
;;

let hh1_type_constants = ("$i", 0) :: !Fusion.the_type_constants;;
let hh1_term_constants = Fusion.constants ();;

let read_file file =
  let h2 = Read.read_prf [file] in
  let (tys, cs, axs, conj) = Hashtbl.fold (fun (_, a) (b, c) sf -> process sf (a, b, c)) h2 ([],[],[],[]) in
  Fusion.the_type_constants := hh1_type_constants @ tys;
  let cs = List.map (fun (a, b) -> (a, ptype [] b)) cs in
  Fusion.set_term_constants (hh1_term_constants @ cs);
  let axassoc = List.map (fun (a,b) -> (a, pterm [] [] b)) axs in
  let (cnames, conjs) = List.split conj in
  let cname = String.concat "" cnames in
  let conj = if conjs = [] then pt else Bool.list_mk_conj (List.map (pterm [] []) conjs) in
  (cname, conj, axassoc)
;;

