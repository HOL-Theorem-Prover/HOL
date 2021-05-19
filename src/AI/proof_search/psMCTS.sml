(* ========================================================================= *)
(* FILE          : psMCTS.sml                                                *)
(* DESCRIPTION   : MCTS algorithm                                            *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure psMCTS :> psMCTS =
struct

open HolKernel Abbrev boolLib aiLib

val ERR = mk_HOL_ERR "psMCTS"

(* -------------------------------------------------------------------------
   Status of the nodes and of the full search
   ------------------------------------------------------------------------- *)

datatype status = Undecided | Win | Lose
fun is_win x = case x of Win => true | _ => false
fun is_lose x = case x of Lose => true | _ => false
fun is_undecided x = case x of Undecided => true | _ => false
fun score_status status = case status of
    Undecided => raise ERR "score_status" ""
  | Win => 1.0
  | Lose => 0.0
fun string_of_status status = case status of
    Win => "win"
  | Lose => "lose"
  | Undecided => "undecided"
datatype search_status = Success | Saturated | Timeout

(* -------------------------------------------------------------------------
   Search tree
   ------------------------------------------------------------------------- *)

type 'a node =
  {board : 'a, stati : status, sum : real, vis : real}
datatype ('a,'b) tree =
   Leaf | Node of 'a node * ('b * real * ('a,'b) tree) vector
fun dest_node x = case x of Node y => y | _ => raise ERR "dest_node" ""
fun is_node x = case x of Node y => true | _ => false
fun is_leaf x = case x of Leaf => true | _ => false

(* -------------------------------------------------------------------------
   MCTS specification
   ------------------------------------------------------------------------- *)

type ('a,'b) game =
  {
  status_of : 'a -> status,
  apply_move : 'b -> 'a -> 'a,
  available_movel : 'a -> 'b list,
  string_of_board : 'a -> string,
  string_of_move : 'b -> string,
  board_compare : 'a * 'a -> order,
  move_compare : 'b * 'b -> order,
  movel : 'b list
  }

fun uniform_player game board =
  (0.0, map (fn x => (x,1.0)) (#available_movel game board))

fun random_player game board =
  (random_real (), map (fn x => (x,1.0)) (#available_movel game board))

type ('a,'b) player = 'a -> real * ('b * real) list

type mctsparam =
  {
  time : real option, nsim : int option,
  explo_coeff : real,
  noise : bool, noise_coeff : real, noise_gen : unit -> real
  }

type ('a,'b) mctsobj =
  {mctsparam : mctsparam, game : ('a,'b) game, player : ('a,'b) player}

(* --------------------------------------------------------------------------
   Policy noise
   ------------------------------------------------------------------------- *)

fun normalize_prepol prepol =
  let val (l1,l2) = split prepol in combine (l1, normalize_proba l2) end

fun add_noise param prepol =
  let
    val noisel1 = List.tabulate (length prepol, fn _ => (#noise_gen param) ())
    val noisel2 = normalize_proba noisel1
    fun f ((move,polv),noise) =
      let
        val coeff = #noise_coeff param
        val newpolv = (1.0 - coeff) * polv + coeff * noise
      in
        (move,newpolv)
      end
  in
    map f (combine (prepol,noisel2))
  end

(* -------------------------------------------------------------------------
   Creation of a node
   ------------------------------------------------------------------------- *)

fun create_node obj board =
  let
    val game = #game obj
    val param = #mctsparam obj
    val stati = (#status_of game) board
    val (value,pol1) = case stati of
        Win => (1.0,[])
      | Lose => (0.0,[])
      | Undecided => (#player obj) board
    val pol2 = normalize_prepol pol1
    val pol3 = if #noise param then add_noise param pol2 else pol2
  in
    (Node ({stati=stati,board=board,sum=value,vis=1.0},
            Vector.fromList (map (fn (a,b) => (a,b,Leaf)) pol3)), 
     value)
  end

fun starting_tree obj board = fst (create_node obj board)

(* -------------------------------------------------------------------------
   Score of a choice in a policy according to pUCT formula.
   ------------------------------------------------------------------------- *)

fun score_puct param sqvtot (move,polv,ctree) =
  let
    val (sum,vis) = case ctree of
      Leaf => (0.0,0.0)
    | Node (cnode,_) => (#sum cnode, #vis cnode)
  in
    (sum + (#explo_coeff param) * polv * sqvtot) / (vis + 1.0)
  end
 
(* -------------------------------------------------------------------------
   Selection of a node to extend by traversing the tree.
   ------------------------------------------------------------------------- *)

fun rebuild_tree reward buildl tree = case buildl of
    [] => tree
  | build :: m => rebuild_tree reward m (build reward tree)

fun select_child obj buildl (node,cv) =
  let
    val (stati,param) = (#stati node, #mctsparam obj)
  in
    if not (is_undecided stati)
    then rebuild_tree (score_status stati) buildl (Node (node,cv))
    else
    let    
      val _ = if Vector.length cv = 0 
        then raise ERR "no move available" "" else () 
      val sqrttot = Math.sqrt (#vis node)
      val ci = vector_maxi (score_puct param sqrttot) cv 
      val (cmove,cpol,ctree) = Vector.sub (cv,ci)
      fun update_node reward {stati,board,sum,vis} =
        {stati=stati, board=board, sum=sum+reward, vis=vis+1.0}
      fun build reward cfuture =
        Node (update_node reward node, 
              Vector.update (cv,ci,(cmove,cpol,cfuture)))
      val newbuildl = build :: buildl
    in
      case ctree of 
        Leaf => 
        let 
          val newboard = (#apply_move (#game obj)) cmove (#board node)
          val (newctree,reward) = create_node obj newboard
        in
          rebuild_tree reward newbuildl newctree  
        end 
      | Node x => select_child obj newbuildl x
    end
  end

(* -------------------------------------------------------------------------
   MCTS
   ------------------------------------------------------------------------- *)

fun mk_timer param =
  if isSome (#nsim param) then 
    let val threshold = valOf (#nsim param) in
      fn n => (Real.round n) >= threshold
    end
  else if isSome (#time param) then 
    let 
      val timer = Timer.startRealTimer () 
      val limit = Time.fromReal (valOf (#time param))
    in
      fn _ => Timer.checkRealTimer timer > limit
    end
  else (fn _ => false)

fun mcts obj starttree =
  let
    val timerf = mk_timer (#mctsparam obj)
    fun loop n tree =
      if timerf (#vis (fst (dest_node tree))) then tree else 
      loop (n+1) (select_child obj [] (dest_node tree))
  in
    loop 0 starttree
  end

(* -------------------------------------------------------------------------
   Statistics
   ------------------------------------------------------------------------- *)

fun score_visit (move,polv,ctree) = case ctree of
      Leaf => 0.0
    | Node (cnode,_) => (#vis cnode)

fun most_visited_path tree = case tree of
    Leaf => []
  | Node (node,cv) => 
    if Vector.length cv = 0 then [(node,NONE)] else
    let 
      val ci = vector_maxi score_visit cv 
      val (cmove,_,ctree) = Vector.sub (cv,ci)
    in
      (node, SOME cmove) :: most_visited_path ctree
    end

(* -------------------------------------------------------------------------
   Toy example: the goal of this task is to reach a positive number starting
   from zero by incrementing or decrementing.
   ------------------------------------------------------------------------- *)

type toy_board = (int * int * int)
datatype toy_move = Incr | Decr

fun toy_status_of (start,finish,timer) =
  if start >= finish then Win
  else if start < 0 orelse timer <= 0 then Lose
  else Undecided

val toy_movel = [Incr,Decr]
fun toy_available_movel board = [Incr,Decr]
fun toy_string_of_move x = case x of Incr => "Incr" | Decr => "Decr"

fun toy_apply_move move (start,finish,timer) = case move of
   Incr => (start+1,finish,timer-1)
 | Decr => (start-1,finish,timer-1)

val toy_game =
  {
  status_of = toy_status_of,
  apply_move = toy_apply_move,
  available_movel = toy_available_movel,
  string_of_board = (fn (a,b,c) => (its a ^ " " ^ its b ^ " " ^ its c)),
  string_of_move = toy_string_of_move,
  board_compare = (fn ((a,b,c),(d,e,f)) =>
    cpl_compare Int.compare Int.compare ((a,b),(d,e))),
  move_compare = (fn (a,b) =>
    String.compare (toy_string_of_move a, toy_string_of_move b)),
  movel = toy_movel
  }

(*
load "aiLib"; open aiLib;
load "psMCTS"; open psMCTS;

val mctsparam =
  {time = (NONE : real option), nsim = (SOME 1000000 : int option),
   explo_coeff = 2.0,
   noise = false, noise_coeff = 0.25, noise_gen = gamma_noise_gen 0.2};

val mctsobj : (toy_board,toy_move) mctsobj =
  {mctsparam = mctsparam, game = toy_game, player = random_player toy_game};

val tree = starting_tree mctsobj (500,1000,1000);
val (_,t) = add_time (mcts mctsobj) tree;
dlength tree;
Profile.results ();
val l = most_visited_path tree;
*)


end (* struct *)
