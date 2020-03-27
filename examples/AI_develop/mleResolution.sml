(* ========================================================================= *)
(* FILE          : mleResolution.sml                                         *)
(* DESCRIPTION   : Prover for propositional CNF                              *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mleResolution :> mleResolution =
struct

open HolKernel Abbrev boolLib aiLib smlParallel psMCTS psTermGen
  mlNeuralNetwork mlTreeNeuralNetwork mlTacticData mlReinforce

val ERR = mk_HOL_ERR "mleResolution"

(* -------------------------------------------------------------------------
   Comparison function
   ------------------------------------------------------------------------- *)

type lit = int * bool
type clause = lit list
val lit_compare = cpl_compare Int.compare bool_compare
val clause_compare = list_compare lit_compare 
type pb = clause list

(* -------------------------------------------------------------------------
   Subsumption
   ------------------------------------------------------------------------- *)

val subsume_calls = ref 0
fun subsume c1 c2 = 
  let 
    val _ = incr subsume_calls
    val d = dset lit_compare c2 
  in 
    all (fn x => dmem x d) c1 
  end 
fun subsumel c1l c2 = exists (fn x => subsume x c2) c1l

(* todo: do it properly *)
fun inter_reduce cl = case cl of
    [] => []
  | c :: m => if subsumel m c then inter_reduce m else c :: inter_reduce m

(* -------------------------------------------------------------------------
   Resolution: assumes the literals in clauses are sorted.
   ------------------------------------------------------------------------- *)

fun resolve_aux b (c1,c2) = case (c1:clause,c2:clause) of
    ([],_) => if b then c2 else raise ERR "resolve_aux" "no match"
  | (_,[]) => if b then c1 else raise ERR "resolve_aux" "no match"
  | ((a1,b1) :: m1, (a2,b2) :: m2) =>
    if a1 < a2 then (a1,b1) :: resolve_aux b (m1,c2)
    else if a2 < a1 then (a2,b2) :: resolve_aux b (c1,m2) 
    else 
      if b1 = b2 then (a1,b1) :: resolve_aux b (m1,m2)
      else if b then raise ERR "resolve_aux" "multiple matches"
           else resolve_aux true (m1,m2)

val resolve_calls = ref 0

fun resolve (c1:clause, c2:clause) = 
  (
  incr resolve_calls;
  (resolve_aux false (c1,c2) : clause)
  )

fun resolve_ctxt pb (c1,c2) = 
  let val c = resolve (c1,c2) in 
    if mem c pb orelse subsumel pb c 
    then raise ERR "resolve_ctxt" "" 
    else c
  end

fun exists_match pb l c = 
  exists (fn x => can (resolve_ctxt pb) (x,c)) l

fun filter_match pb c l = 
  filter (fn x => can (resolve_ctxt pb) (c,x)) l

(* -------------------------------------------------------------------------
   Brute force algorithm by iterative deepedning
   ------------------------------------------------------------------------- *)

fun resolve_cost pb ((c1,n1),(c2,n2)) =
  let val c = resolve (c1,c2) in
    if dmem c pb then raise ERR "resolve_cost" "" else (c, n1 + n2 + 1)
  end

fun resolve_brute (pb,l1,l2) =
  let val l = all_pairs l2 @ cartesian_product l1 l2 in
    mapfilter (resolve_cost pb) l
  end

fun brute_pb_aux aimf (i,n) (pb,l1,l2) =
  if aimf pb then ("solved", i, SOME (dkeys pb))
  else if null l2 then ("saturated", i, NONE)  
  else if i >= n then ("timeout", i, NONE)
  else
    let 
      val cl1 = dlist (dregroup clause_compare (resolve_brute (pb,l1,l2))) 
      val cl2 = map_snd list_imin cl1
    in
      brute_pb_aux aimf (i+1,n) (daddl cl2 pb, l2 @ l1, cl2)
    end

fun brute_pb aimf n (l: clause list) = 
  let val lcost = map_assoc (fn _ => 0) l in
    brute_pb_aux aimf (0,n) (dnew clause_compare lcost, [], lcost)
  end

fun abs_time pb =
  (resolve_calls := 0; ignore (brute_pb (dmem []) 20 pb); !resolve_calls)


(* -------------------------------------------------------------------------
   Evaluation
   ------------------------------------------------------------------------- *)

fun eval_lit assign (lit,b) = 
  if b then Vector.sub (assign,lit) else not (Vector.sub (assign,lit))

fun eval_clause assign c = exists (eval_lit assign) c

fun eval_pb assign pb = all (eval_clause assign) pb

fun all_assign nvar =
  map Vector.fromList 
  (cartesian_productl (List.tabulate (nvar,fn _ => [false,true])))

fun is_sat pb = 
  let val nvar = list_imax (map fst (List.concat pb)) in
    exists (C eval_pb pb) (all_assign (nvar + 1))
  end

(* -------------------------------------------------------------------------
   Generation of a random problem for 3-SAT
   ------------------------------------------------------------------------- *)

fun random_lit nvar = 
  (random_int (0, nvar - 1), random_elem [true,false])

fun random_clause nlit nvar = 
  let 
    fun loop n d = 
      if n <= 0 then d else
      let val (i,b) = random_lit nvar in
        if dmem i d then loop (n-1) d else loop (n-1) (dadd i b d)
      end
  in
    dlist (loop nlit (dempty Int.compare))
  end

fun random_pb nclause nlit nvar =
  let 
    fun loop d =
      if dlength d >= nclause 
      then d 
      else loop (dadd (random_clause nlit nvar) () d)
  in
    dkeys (loop (dempty clause_compare))
  end

(*
load "aiLib"; open aiLib;
load "mleResolution"; open mleResolution;
val ERR = mk_HOL_ERR "mleResolution";
val max_lit = 3;
val max_var = 5;
val max_clause = 25;

val atim = abs_time pb;
fun provable_pb n =
  if n <= 0 then [] else
  let val pb = random_pb max_clause max_lit max_var in
    if is_sat pb 
    then provable_pb n 
    else pb :: provable_pb (n-1)
  end

val pbl = provable_pb 100;
val pbatiml = map_assoc abs_time pbl;

fun sigmoid x = Math.tanh x / 2.0 + 0.5;
fun scale_real x = 2.0 * x - 1.0;

fun random_selection (pb,pbtim) = 
  let 
    val randoml = List.tabulate (length pb, fn _ => random_int (0,1))
    val vect = Vector.fromList (map (scale_real o Real.fromInt) randoml)
    val newpb = map fst (filter (fn x => snd x = 1) (combine (pb,randoml)))
  in
    if is_sat newpb 
    then ((pb,vect), 0.0)
    else ((pb,vect), sigmoid (int_div pbtim (abs_time newpb)))
  end;

val ex = (hd pbatiml);
selection or not selection

(*
fun random_selectionl (posl,negl) pbatim =
  if (length posl >= 5 andalso length negl >= 5) orelse 
     (length posl >= 100 orelse length negl >= 100)
  then 
    (first_n 5 posl, first_n 5 negl)
  else
  let val ex = random_selection pbatim in
    if snd ex > 0.5 
    then random_selectionl (ex :: posl, negl) pbatim
    else random_selectionl (posl, ex :: negl) pbatim
  end
*)

val (posl,negl) = random_selectionl ([],[]) (hd pbatiml);

val exl = List.concat 
  (map ((fn (a,b) => a @ b) o random_selectionl ([],[])) pbatiml);

load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;

val ((pb,sel),afreq) = hd exl;

val headvar = mk_var ("head_", ``:bool -> bool``);

val operl = 
  map_assoc (dim_std (1,25))
  (List.tabulate (5, mk_bvar) @ 
   [empty_list_var,``$~``,``$/\``,``$\/``]);
  @ (headvar, [25,25,25])


fun term_of_pb (pb,sel) = 
  let
    val pbtm = term_of_clausel pb
    val cattm = list_mk_comb (catvar,[pbtm,seltm])
    val headtm = mk_comb (headvar,cattm)
  end

fun prep_ex (pbsel,afreq) = (term_of_pbsel pbsel,[afreq])

val schedule =
  [{ncore = 4, verbose = true, learning_rate = 0.02,
    batch_size = 16, nepoch = 20}]

val tnnparam = map_assoc (dim_std (2,12)) operl

*)


(*
let
  val _ = resolve_calls := 0
  val pb = random_pb max_clause max_lit max_var
  val r = if is_sat pb then raise ERR "" "" else brute_pb (dmem []) 32 pb
  val depth = #2 r
  val pbend = valOf (#3 r)
in
  print_endline ("Depth: " ^ its depth);
  print_endline ("Generated clauses: " ^ its (length pbend));
  print_endline ("Resolve calls: " ^ its (!resolve_calls))
  print_endline ("Axioms");
  print_endline (string_of_pb pb);
  print_endline ("Derived clauses");
  print_endline (string_of_pb pbend)
end;
*)

(*
fun print_c
3^4 - 2 ^ 4;
3^7 - 2 ^ 7; 3^5
(* could be subsumes instead of subset *)
fun min_cut cut pb =
  let fun aimf d = all (fn x => dmem x d) cut in
    snd (valOf (#3 (brute_pb aimf 5 pb)))
  end;
fun improving_cut () = 
  let val pb = random_pb max_clause max_lit max_var in
    if is_sat pb then (print "s"; improving_cut ()) else
    let
      val _ = print_endline "p"
      val cut = random_pb (random_int (1,10)) max_lit max_var
      val rtot = (min_proof pb handle _ => 0)
      val r2 = (min_proof (pb @ cut) handle _ => 1000)
      val r1 = (min_cut cut pb handle _ => 1000)
    in
      if r1 + r2 < rtot then (pb,cut) else improving_cut ()
    end
  end;
*)

(*
Todo define what is a good cut: take random subset of the proof?
*)

(*
val max_lit = 3;
val max_var = 5;val ERR = mk_HOL_ERR "mleResolution"
val max_clause = 20;
val pbl = List.tabulate (100, fn _ => random_pb max_clause max_lit max_var);
val (pbl_sat, pbl_unsat) = partition is_sat pbl;
length pbl_unsat;
val pbl_result = map (brute_pb 32) pbl_unsat;
val pbl_solved = filter (fn x => #1 x = "solved") pbl_result;
length (filter (fn x => #1 x = "solved") pbl_result);
length (filter (fn x => #1 x = "saturated") pbl_result);
length (filter (fn x => #1 x = "timeout") pbl_result);
val diffl = map (valOf o #3) pbl_solved;
val diffd = count_dict (dempty Int.compare) diffl;
(dlist diffd);
*)

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = pb * pb * int list
val pb_compare = list_compare clause_compare

fun mk_startboard cl = (cl, [])

fun string_of_lit (i,b) = if b then its i else "~" ^ its i
fun string_of_clause c = 
  "(" ^ String.concatWith " " (map string_of_lit c) ^ ")"
fun string_of_pb cl = 
  if null cl 
  then "empty clause list"
  else String.concatWith "\n" (map string_of_clause cl)

fun string_of_board (cl1,cl2,nl) =
  string_of_pb cl1 ^ "\n\n" ^ string_of_pb cl2 ^ "\n\n" ^
  String.concatWith " " (map its nl)  

val board_compare = 
  triple_compare pb_compare pb_compare (list_compare Int.compare)

fun status_of (cl1,cl2,nl) =
  let val pb = cl2 @ cl1 in
    if is_sat pb then Lose else
    let val atim = abs_time pb in 
      if atim < last (first_n 10 nl)
      then Win
      else if null cl1 then Lose
      else Undecided
    end
  end

(* -------------------------------------------------------------------------
   Neural representation of the board
   ------------------------------------------------------------------------- *)

(*
val empty_list_var = mk_var ("empty_list_var", bool)
val pair_cat = mk_var ("pair_cat", ``:bool -> bool -> bool``)
val cat_move = mk_var ("cat_move", ``:bool -> bool -> 'a``); 

fun mk_bvar i = mk_var ("V" ^ its i, bool)
fun bvar_of_term tm = string_to_int (tl_string (fst (dest_var tm)))

fun mk_lit (i,b) = (if b then I else mk_neg) (mk_bvar i)
fun lit_of_term tm = 
  if is_neg tm 
  then (bvar_of_term (dest_neg tm), false) 
  else (bvar_of_term tm, true)

fun term_of_clause c = list_mk_disj (map mk_lit c)
fun clause_of_term ctm = map lit_of_term (strip_disj ctm)

fun term_of_clausel cl = 
  if null cl 
  then empty_list_var 
  else list_mk_conj (map term_of_clause cl)
fun clausel_of_term tm = 
  if term_eq empty_list_var tm 
  then []
  else map clause_of_term (strip_conj tm)

fun term_of_pb d = term_of_clausel (dkeys d)
fun pb_of_term tm = dset clause_compare (clausel_of_term tm)

fun term_of_board (cl,co,_) =
  let val clo = if co = NONE then [] else [valOf co] in
    list_mk_comb (pair_cat, [term_of_clausel cl, term_of_clausel clo])    
  end
fun board_of_term tm = 
  let val (cl1,cl2) = pair_of_list (snd (strip_comb tm)) in
    (
    clausel_of_term cl1, 
    (case clausel_of_term cl2 of 
        [] => NONE | [a] => SOME a | _ => raise ERR "board_of_term" "")
    )
  end

fun term_of_move board move = 
  list_mk_comb (cat_move, [term_of_board board, term_of_clause move])

val head_eval = mk_var ("head_eval", ``:bool -> 'a``)
val head_poli = mk_var ("head_poli", ``:'a -> 'a``)
fun tag_heval x = mk_comb (head_eval,x)
fun tag_hpoli x = mk_comb (head_poli,x)

val operl = List.tabulate (5, mk_bvar) @ 
  [empty_list_var, cat_move,
   pair_cat, ``$~``,``$/\``,``$\/``,head_eval,head_poli]
*)

(*
load "aiLib"; open aiLib;
load "mleResolution"; open mleResolution;
val board = [[(0,true),(1,false),(2,true)]];
val tm = term_of_board (board,NONE,0);
*)

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

datatype move = Select | Delete
val movel = [Select,Delete]

fun string_of_move move = 
  case move of Select => "Select" | Delete => "Delete"

fun move_compare (a,b) = 
  String.compare (string_of_move a, string_of_move b)

fun available_movel _ = movel

fun apply_move move (cl1,cl2,nl) = 
  if null cl1 then raise ERR "apply_move" "" else
  case move of
    Select => (tl cl1, hd cl1 :: cl2, nl)
  | Delete => (tl cl1, cl2, nl)
  
(* -------------------------------------------------------------------------
   Game
   ------------------------------------------------------------------------- *)

val game : (board,move) game =
  {
  status_of = status_of,
  apply_move = apply_move,
  movel = movel,
  available_movel = available_movel,  
  string_of_board = string_of_board,
  string_of_move = string_of_move,
  move_compare = move_compare,
  board_compare = board_compare
  }

(* -------------------------------------------------------------------------
   MCTS test with uniform player
   ------------------------------------------------------------------------- *)

fun mk_mctsparam nsim =
  {
  timer = NONE,
  nsim = SOME nsim,
  stopatwin_flag = true,
  decay = 1.0, explo_coeff = 2.0,
  noise_coeff = 0.25, 
  noise_root = false,
  noise_all = false, 
  noise_gen = random_real,
  noconfl = false, 
  avoidlose = false
  }

fun string_of_status status = case status of
    Win => "win"
  | Lose => "lose"
  | Undecided => "undecided"

fun mcts_test nsim target =
  let
    val mctsobj =
      {mctsparam = mk_mctsparam nsim,
       game = game,
       player = random_player game}
    val tree = starttree_of mctsobj target
    val (endtree,_) = mcts mctsobj tree
    val b = #status (dfind [] endtree) = Win
  in
    print_endline (string_of_status (#status (dfind [] endtree)));
    (b, endtree)
  end

(*
load "aiLib"; open aiLib;
load "psMCTS"; open psMCTS;
load "mleResolution"; open mleResolution;

val max_lit = 3;
val max_var = 5;
val max_clause = 25;

fun provable_pb n =
  if n <= 0 then [] else
  let val pb = random_pb max_clause max_lit max_var in
    if is_sat pb 
    then provable_pb n 
    else pb :: provable_pb (n-1)
  end;

val pbl = provable_pb 100;
val pbl1 = map_assoc abs_time pbl;
val targetl = map (fn (a,b) => (a,([]:pb),List.tabulate (10,fn _ => b))) pbl1;

fun update_target target =
  let val (win,endtree) = mcts_test 1000 target in
    if win then
      let
        val nodel = trace_win endtree []
        val (pb,_,nl) = #board (last nodel)
        val atim = abs_time pb
      in
        (pb, [], dict_sort Int.compare (atim :: nl))
      end
    else target
  end;

val targetl2 = map update_target targetl;
val targetl3 = map update_target targetl2;
val targetl4 = map update_target targetl3;
val targetl5 = map update_target targetl4;

val targetl10 = funpow 5 (map update_target) targetl5;
val targetl15 = funpow 5 (map update_target) targetl10;
val l1 = map_assoc list_imin (map #3 targetl15);
val l2 = map fst (dict_sort compare_imin l1);
*)

(*
(* -------------------------------------------------------------------------
   Parallelization
   ------------------------------------------------------------------------- *)

fun write_boardl file boardl =
  let val nl = map #3 boardl in
    export_terml (file ^ "_boardl") (map term_of_board boardl);
    writel (file ^ "_timel") (map its nl)
  end

fun read_boardl file =
  let 
    val boardl = map board_of_term (import_terml (file ^ "_boardl"))
    val nl = map string_to_int (readl (file ^ "_timel"))
    val (l1,l2) = split boardl
  in
    combine_triple (l1,l2,nl)
  end

val gameio = {write_boardl = write_boardl, read_boardl = read_boardl}

(* -------------------------------------------------------------------------
   Players
   ------------------------------------------------------------------------- *)

val schedule =
  [{ncore = 4, verbose = true, learning_rate = 0.02,
    batch_size = 16, nepoch = 20}]

val tnnparam = map_assoc (dim_std (2,12)) operl

fun tob board = 
  tag_heval (term_of_board board) ::
  map (tag_hpoli o term_of_move board) (available_movel board)

val dplayer = {tob = tob, tnnparam = tnnparam, schedule = schedule}

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

val version = 1

val rlparam =
  {expname = "mleResolution-" ^ its version, exwindow = 200000,
   ncore = 30, ntarget = 200, nsim = 32000, decay = 1.0}

val rlobj : (board,move) rlobj =
  {rlparam = rlparam, 
   game = game, 
   gameio = gameio, 
   dplayer = dplayer}

val extsearch = mk_extsearch "mleResolution.extsearch" rlobj
*)

(*
load "mleResolution"; open mleResolution;
load "mlReinforce"; open mlReinforce;
val pbl = (#level_targetl rlobj) 4;
val r = rl_start (rlobj,extsearch) 4;
*)

end (* struct *)
