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

fun subsume c1 c2 = 
  let val d = dset lit_compare c2 in 
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
  (incr resolve_calls; (resolve_aux false (c1,c2) : clause))

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

fun abs_time pb =
  if is_sat pb then 1000000000 else
  (resolve_calls := 0; ignore (brute_pb (dmem []) 20 pb); !resolve_calls)

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
    shuffle (dkeys (loop (dempty clause_compare)))
  end

fun provable_pb (max_clause,max_lit,max_var) n =
  if n <= 0 then [] else
  let val pb = random_pb max_clause max_lit max_var in
    if is_sat pb 
    then provable_pb (max_clause,max_lit,max_var) n 
    else pb :: provable_pb (max_clause,max_lit,max_var) (n-1)
  end

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = pb * pb * int
val pb_compare = list_compare clause_compare

fun string_of_lit (i,b) = if b then its i else "~" ^ its i
fun lit_of_string s = 
  if hd_string s = #"~" 
  then (string_to_int (tl_string s), false)
  else (string_to_int s, true)

fun string_of_clause c = 
  if null c then "emptyclause" else
  String.concatWith "_" (map string_of_lit c)
fun clause_of_string s =
  if s = "emptyclause" then [] else
  map lit_of_string (String.tokens (fn c => c = #"_") s)

fun string_of_pb cl = 
  if null cl then "emptypb" else 
  String.concatWith "," (map string_of_clause cl)
fun pb_of_string s = 
  if s = "emptypb" then [] else
  map clause_of_string (String.tokens (fn c => c = #",") s)

fun string_of_board (cl1,cl2,n) =
  string_of_pb cl1 ^ " " ^ string_of_pb cl2 ^ " " ^ its n
fun board_of_string s = 
  let val (a,b,c) = triple_of_list (String.tokens Char.isSpace s) in
    (pb_of_string a, pb_of_string b, string_to_int c)
  end

val board_compare = triple_compare pb_compare pb_compare Int.compare

fun find_index nl a = case nl of
    [] => 0
  | b :: m => if b <= a then 1 + find_index m a else 0

fun eval_board (_,_,n) = 10.0 * (1.0 / (1.0 + Math.ln (Real.fromInt n)))

fun status_of (board as (cl1,cl2,_)) =
  let val pb = cl2 @ cl1 in
    if is_sat pb then Lose 
    else if null cl1 then Win
    else Undecided
  end

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

datatype move = Select | Delete
val movel = [Select,Delete]

fun string_of_move move = 
  case move of Select => "Select" | Delete => "Delete"

fun move_compare (a,b) = 
  String.compare (string_of_move a, string_of_move b)

fun available_movel (cl1,cl2,_) = 
  if null cl1 then [] else movel

fun apply_move move (cl1,cl2,n) = 
  if null cl1 then raise ERR "apply_move" "" else
  case move of
    Select => (tl cl1, hd cl1 :: cl2, n)
  | Delete => (tl cl1, cl2, abs_time (tl cl1 @ cl2))
  
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
  timer = NONE, nsim = SOME nsim, stopatwin_flag = false,
  decay = 1.0, explo_coeff = 2.0,
  noise_coeff = 0.25, noise_root = false, noise_all = false, 
  noise_gen = random_real,
  noconfl = false, avoidlose = false, evalwin = true
  }

fun smart_player game board =
  (eval_board board, 
   map (fn x => (x,1.0)) (#available_movel game board))

fun mcts_test nsim target =
  let
    val mctsobj =
      {mctsparam = mk_mctsparam nsim,
       game = game,
       player = smart_player game}
    val tree = starttree_of mctsobj target
    val (endtree,_) = mcts mctsobj tree
    val b = is_win (#status (dfind [] endtree))
  in
    print_endline (string_of_status (#status (dfind [] endtree)));
    (b, endtree)
  end

(*
load "aiLib"; open aiLib;
load "psMCTS"; open psMCTS;
load "psBigSteps"; open psBigSteps;
load "mleResolution"; open mleResolution;


val mctsparam =
  {
  timer = NONE, nsim = SOME 10000, stopatwin_flag = false,
  decay = 1.0, explo_coeff = 2.0,
  noise_coeff = 0.25, noise_root = false, noise_all = false, 
  noise_gen = random_real,
  noconfl = false, avoidlose = false, evalwin = true
  };

fun smart_player (game : (board,move) game) (board as (cl1,cl2,nl)) =
  (eval_board board, 
   map (fn x => (x,1.0)) (#available_movel game board));

val bsobj = 
   {game = game,
    mctsparam = mctsparam,
    preplayer = fn _ => smart_player game, 
    temp_flag = false, 
    verbose = true};

val max_lit = 3; val max_var = 5; val max_clause = 25;
val pbl = provable_pb (max_clause,max_lit,max_var) 1;
val target = (hd pbl, ([]:pb), abs_time (hd pbl));

val object = run_bigsteps bsobj target;
val (_,_,nodel) = object;
val mini = #board (hd nodel);
print_endline (#string_of_board game target);
print_endline (#string_of_board game mini);

fun convert_sc n = 10.0 * (1.0 / (1.0 + Math.ln (Real.fromInt n)));
val l1 = map (abs_time o (fn (a,b,c) => a @ b) o #board) (rev nodel);
val l2 = map convert_sc l1;
*)

(* should not use eval for 0.0 *)

(* -------------------------------------------------------------------------
   Neural representation of the board
   ------------------------------------------------------------------------- *)

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

fun term_of_board (cl1,cl2,_) =
  list_mk_comb (pair_cat, [term_of_clausel cl1, term_of_clausel cl2])    

val head_eval = mk_var ("head_eval", ``:bool -> bool``)
val head_poli = mk_var ("head_poli", ``:bool -> bool``)
fun tag_heval x = mk_comb (head_eval,x)
fun tag_hpoli x = mk_comb (head_poli,x)

(*
load "aiLib"; open aiLib;
load "mleResolution"; open mleResolution;
val max_lit = 3; val max_var = 5; val max_clause = 25;
val pbl = provable_pb (max_clause,max_lit,max_var) 1;
val target = (hd pbl, ([]:pb), abs_time (hd pbl));
val tm = term_of_board target;
*)

(* -------------------------------------------------------------------------
   Parallelization
   ------------------------------------------------------------------------- *)

fun write_boardl file boardl =
  writel (file ^ "_boardl") (map string_of_board boardl)

fun read_boardl file = map board_of_string (readl (file ^ "_boardl"))

val gameio = {write_boardl = write_boardl, read_boardl = read_boardl}

(* -------------------------------------------------------------------------
   Players
   ------------------------------------------------------------------------- *)

val schedule =
  [{ncore = 4, verbose = true, learning_rate = 0.02,
    batch_size = 16, nepoch = 20}]

val operl = List.tabulate (5, mk_bvar) @ 
  [empty_list_var, cat_move,
   pair_cat, ``$~``,``$/\``,``$\/``,head_eval]

val tnnparam = map_assoc (dim_std (1,16)) operl @ [(head_poli,[16,2])]

fun pretob _ board = 
  let val tm = term_of_board board in [tag_heval tm, tag_hpoli tm] end

val dplayer = {pretob = pretob, tnnparam = tnnparam, schedule = schedule}

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

val version = 1

fun infobs boardl = 
  let 
    fun f x = String.translate 
      (fn x => if Char.isSpace x then "\n" else Char.toString x)
      (string_of_board x)
    val dir = HOLDIR ^ "/examples/AI_develop/log" ^ its version 
    val _ = mkDir_err dir
    val file = dir ^ "/" ^ its (hash_string (string_of_board (last boardl)))
  in
    (if exists_file file then () else
     append_endline file (f (last boardl) ^ "\n"));
    append_endline file (f (hd boardl))
  end

val rlparam =
  {expname = "mleResolution-" ^ its version, exwindow = 200000,
   ncore = 30, ntarget = 200, nsim = 3200, decay = 1.0}

val rlobj : (board,move) rlobj =
  {rlparam = rlparam,  game = game, gameio = gameio, dplayer = dplayer,
   infobs = infobs}

val extsearch = mk_extsearch "mleResolution.extsearch" rlobj


(*
load "aiLib"; open aiLib;
load "mlReinforce"; open mlReinforce;
load "mleResolution"; open mleResolution;

val max_lit = 3; val max_var = 5; val max_clause = 25;
val pbl = provable_pb (max_clause,max_lit,max_var) 100;
val targetl = map (fn x => (x,[]:pb,abs_time x)) pbl;
val targetd = dnew (#board_compare game) (map (fn x => (x,[])) targetl)
val r = rl_start (rlobj,extsearch) targetd;
*)

end (* struct *)
