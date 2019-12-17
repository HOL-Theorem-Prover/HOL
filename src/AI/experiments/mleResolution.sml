(* ========================================================================= *)
(* FILE          : mleResolution.sml                                         *)
(* DESCRIPTION   : Prover for propositional CNF                              *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mleResolution :> mleResolution =
struct

open HolKernel Abbrev boolLib aiLib smlParallel psMCTS psTermGen
  mlNeuralNetwork mlTreeNeuralNetwork mlTacticData mlReinforce mleLib mleSetLib

val ERR = mk_HOL_ERR "mleResolution"
type 'a set = ('a, unit) Redblackmap.dict

(* -------------------------------------------------------------------------
   Comparison function
   ------------------------------------------------------------------------- *)

val lit_compare = cpl_compare Int.compare bool_compare
fun dict_compare cmp (d1,d2) = list_compare cmp (dlist d1, dlist d2)
val clause_compare = dict_compare (cpl_compare Int.compare bool_compare)

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = 
  (
  (int, bool) Redblackmap.dict) set * 
  (int, bool) Redblackmap.dict) option * 
  int
  )

val board_compare =
  cpl_compare (set_compare (set_compare lit_compare)) Int.compare

fun string_of_board _ = "board"

fun status_of (l,n) =
  if exists null l then Win 
  else if n <= 0 then Lose
  else Undecided

(* -------------------------------------------------------------------------
   Term representations of the board
   ------------------------------------------------------------------------- *)

(* use priming instead *)
fun mk_lit (i,b) = 
  (if b then I else mk_neg) (mk_var ("V" ^ its i, bool))

fun term_of_board (d,n) =
  let 
    val vll1 = map dkeys (dkeys d) 
    val vll2 = map (map mk_lit) vll1
  in
    list_mk_disj (map list_mk_conj vll2)
  end
 
fun term_of_boardc _ b = term_of_board b

(*
load "aiLib"; open aiLib;
load "mleResolution"; open mleResolution;
val board = dset (set_compare lit_compare) 
  [dset lit_compare [(0,true),(1,false),(2,true)]];
val tm = term_of_board (board,0);

clause1_tag, literal1_tag
*)

(*
load "aiLib"; open aiLib;
val l = List.tabulate (100, fn x => random_elem [0,1]);
val n = sum_int l;
*)

(* -------------------------------------------------------------------------
   One resolution step
   ------------------------------------------------------------------------- *)

fun all_match (l,d) = case l of
    [] => []
  | (i,b) :: m =>
    if dfind i d = not b handle NotFound => false  
    then [i] 
    else [] @ all_match (m,d)

fun all_matchd (d1,d2) = all_match (dlist d1, d2)

fun is_singleton l = case l of [a] => true | _ => false

fun is_match (d1,d2) = is_singleton (all_matchd (d1,d2))
  
fun resolve_at_match (d1,d2) i =
  daddl (dlist (drem i d1)) (drem i d2)

fun resolve_all_match (d1,d2) = case all_matchd (d1,d2) of
    [i] => resolve_at_match (d1,d2) i
  | _ => raise ERR "resolve_all_match"

(*
val d1 = dnew Int.compare [(0,true),(1,false),(2,true)];
val d2 = dnew Int.compare [(0,false),(3,false),(4,true)];
val l = dlist (only_hd (resolve_all_match (d1,d2)));
*)

(* -------------------------------------------------------------------------
   Brute force algorithm
   ------------------------------------------------------------------------- *)

fun all_pairs cmp l = 
  let 
    val ll = cartesian_product l l
    fun test (a,b) = cmp (a,b) = LESS
  in
    filter test ll
  end

fun resolve_all d = 
  let 
    val ddl = all_pairs clause_compare (dkeys d) 
    val clauses = List.concat (map resolve_all_match ddl)
  in
    (
    dset clause_compare clauses,
    daddl (map_assoc (fn _ => ()) clauses) d
    )
  end

fun brute_pb_aux (i,n) hist pb =
  if exists (fn x => dlength x = 0) (dkeys pb) then ("solved", i, hist) else
  if i >= n then ("timeout",i, hist) else
  let val (clauses,newpb) = resolve_all pb in
    if dlength newpb <= dlength pb then ("saturated", i+1, hist) else
    brute_pb_aux (i+1,n) (clauses :: hist) newpb
  end

fun brute_pb n pb = brute_pb_aux (0,n) [] pb;

(* 
val pbl = List.tabulate (10000, fn _ => random_pb 5 5);
val rl = map (brute_pb 10) pbl;
val rl_solved = filter (fn x => #1 x = "solved") rl;
val rl_saturated = filter (fn x => #1 x = "saturated") rl;
val rl_timeout = filter (fn x => #1 x = "timeout") rl;
map length [rl_solved, rl_saturated, rl_timeout];

fun compare_length (_,a,_) (_,b,_) = Int.compare (a,b);
val d = dregroup Int.compare (map (fn x => (#2 x, ())) rl_solved);
val rl_solved_dis = dlist (dmap (fn (_,l) => length l) d);

fun view pb = map dlist (dkeys pb)
val pb = random_pb 5 5;
view pb;
val (a,b,c) = brute_pb 100 pb;
val l = map view c;
*)

(* -------------------------------------------------------------------------
   Generation
   ------------------------------------------------------------------------- *)

fun random_lit i = (i,random_elem [true,false])
fun random_clause maxlit = 
  let fun f i = if random_int (0,1) = 0 then [random_lit i] else [] in
    dnew Int.compare (List.concat (List.tabulate (maxlit, f)))
  end
fun random_pb nclause maxlit =
  let val dl = List.tabulate (nclause, fn _ => random_clause maxlit) in
    dset clause_compare dl
  end

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

type move = Select of int | Delete of int

fun string_of_move m = case m of
    Select c => "s" ^ its c
  | Delete c => "c" ^ its c

fun move_compare (a,b) = String.compare (string_of_move a, string_of_move b)

fun resolve_pair (c1,c2)= 
  resolve_all_match (List.nth (dl,c1), List.nth (dl,c2))

fun apply_move move (d,c1o,n) = case move of
  | Delete c => (drem (List.nth (dkeys d, c)) d, NONE, n-1)  
  | Select c2 => case c1o of
    | NONE => (d, SOME c2, n-1)
    | SOME c1 => (dadd (resolve_pair (c1,c2)) d, NONE, n-1)

fun is_select m = case m of Select _ => true | _ => false

fun available_move board move = case board of
    (_, NONE, _) => true
  | (_, SOME c1, _) => is_select move

(* -------------------------------------------------------------------------
   Game
   ------------------------------------------------------------------------- *)

val game : (board,move) game =
  {
  board_compare = board_compare,
  string_of_board = string_of_board,
  movel = movel,
  move_compare = Term.compare,
  string_of_move = string_of_move,
  status_of = status_of,
  available_move = available_move,
  apply_move = apply_move
  }

(* -------------------------------------------------------------------------
   MCTS test with uniform player
   ------------------------------------------------------------------------- *)

(*
load "mleResolution"; open mleResolution;
load "psMCTS"; open psMCTS;
load "aiLib"; open aiLib;
load "mlTacticData"; open mlTacticData;

val mcts_param =
  {
  nsim = 50000,
  stopatwin_flag = true,
  decay = #decay (#rl_param rlpreobj),
  explo_coeff = 2.0,
  noise_coeff = 0.25,
  noise_gen = 0.2
  };

val datasetsynt_dir = HOLDIR ^ "/src/AI/experiments/data_setsynt"
val tml1 = import_terml (datasetsynt_dir ^ "/h4setsynt");
val targetl1 = map mk_startboard (first_n 100 tml1);
val graphl = map (snd o fst) targetl1;
val graph_set = mk_fast_set (list_compare bool_compare) graphl;
length graph_set;

fun test i target =
  let
    val mcts_obj =
      {mcts_param = mcts_param,
       game = #game rlpreobj,
       player = uniform_player (#game rlpreobj)}
    val tree = starttree_of mcts_obj target
    val endtree = mcts mcts_obj tree
  in
    print_endline (its i);
    #status (dfind [] endtree) = Win
  end
;

val targetl2 = combine (targetl1, mapi test targetl1);
val targetl3 = filter snd targetl2;
length targetl3;
*)
end (* struct *)
