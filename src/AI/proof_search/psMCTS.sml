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
   Search tree
   ------------------------------------------------------------------------- *)

datatype status = Undecided | Win | Lose
type id = int list (* node identifier *)
val id_compare = list_compare Int.compare
type 'b pol = (('b * real) * id) list
type ('a,'b) node =
  {
  pol : 'b pol, 
  value : real,
  board : 'a, 
  sum : real, 
  vis : real, 
  status : status
  }
type ('a,'b) tree = (id, ('a,'b) node) Redblackmap.dict

(* -------------------------------------------------------------------------
   Game specification, player (value + policy) and additional search
   parameters
   ------------------------------------------------------------------------- *)

type ('a,'b) game =
  {
  board_compare : 'a * 'a -> order,
  string_of_board : 'a -> string,
  movel: 'b list,
  move_compare : 'b * 'b -> order,
  string_of_move : 'b -> string,
  status_of : 'a -> status,
  available_move : 'a -> 'b -> bool,
  apply_move : ('b -> 'a -> 'a)
  }

fun uniform_player game board = (0.0, map (fn x => (x,1.0)) (#movel game))

type ('a,'b) player = 'a -> real * ('b * real) list

type mcts_param =
  {
  nsim : int,
  stopatwin_flag : bool,
  decay : real,
  explo_coeff : real,
  noise_root : bool,
  noise_all : bool,
  noise_coeff : real,
  noise_gen : unit -> real
  }

type ('a,'b) mcts_obj =
  {
  mcts_param : mcts_param, 
  game : ('a,'b) game, 
  player : ('a,'b) player
  }

(* -------------------------------------------------------------------------
   Backup
   ------------------------------------------------------------------------- *)

fun quant_status quant status tree pol =
  let
    val cidl = map snd pol
    fun is_status cid = #status (dfind cid tree) = status
                        handle NotFound => false
  in
    quant is_status cidl
  end

fun exists_win tree pol  = quant_status exists Win tree pol
fun all_lose tree pol = quant_status all Lose tree pol

fun update_node decay tree reward {pol,value,board,sum,vis,status} =
  let val newstatus =
    if status <> Undecided then status
    else if exists_win tree pol then Win
    else if all_lose tree pol then Lose
    else Undecided
  in
    {pol=pol, value=value, board=board, 
     sum=sum+reward, vis=vis+1.0, status=newstatus}
  end

fun backup decay tree (id,reward) =
  let
    val node1 = dfind id tree
    val node2 = update_node decay tree reward node1
    val newtree = dadd id node2 tree
  in
    if null id then newtree else backup decay newtree (tl id, decay * reward)
  end

(* --------------------------------------------------------------------------
   Dirichlet noise
   ------------------------------------------------------------------------- *)

val gammadict = dnew Real.compare
  [(0.01, 99.43258512),(0.02, 49.44221016),(0.03, 32.78499835),
   (0.04, 24.46095502),(0.05, 19.47008531),(0.06, 16.14572749),
   (0.07, 13.77360061),(0.08, 11.99656638),(0.09, 10.61621654),
   (0.1, 9.513507699),(0.2, 4.590843712),(0.3, 2.991568988),
   (0.4, 2.218159544),(0.5, 1.772453851),(0.6, 1.489192249),
   (0.7, 1.298055333),(0.8, 1.164229714),(0.9, 1.068628702)]

fun gamma_of alpha = dfind alpha gammadict
  handle NotFound => raise ERR "gamma_of" (rts alpha)

fun gamma_density alpha x =
  (Math.pow (x, alpha - 1.0) * Math.exp (~ x)) / gamma_of alpha

fun interval (step:real) (a,b) =
  if a + (step / 2.0) > b then [b] else a :: interval step (a + step,b)

fun gamma_distrib alpha =
  map_assoc (gamma_density alpha) (interval 0.01 (0.01,10.0));

fun gamma_noise_gen alpha =
  let 
    val distrib = gamma_distrib alpha 
    val cumul = mk_cumul distrib
  in 
    fn () => select_in_cumul cumul
  end

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
   Node creation
   ------------------------------------------------------------------------- *)

fun filter_available game board (e,p) =
  let
    val p' = filter (fn (m,_) => (#available_move game) board m) p
    val _ = if null p' then raise ERR "filter_available" "" else ()
  in
    (e,p')
  end

fun node_create_backup obj tree (id,board) =
  let
    val game = #game obj
    val param = #mcts_param obj
    val node = 
      let
        fun add_cid pol = let fun f i x = (x, i :: id) in mapi f pol end
        val status = (#status_of game) board
        val (value,pol1) = case status of
            Win       => (1.0,[])
          | Lose      => (0.0,[])
          | Undecided => filter_available game board ((#player obj) board)
        val pol2 = normalize_prepol pol1
        val pol3 = 
          if #noise_all param orelse (#noise_root param andalso null id) 
          then add_noise param pol2 
          else pol2
      in
        {pol= add_cid pol3, value=value,
         board=board, sum=0.0, vis=0.0, status=status}
      end
    val tree1 = dadd id node tree
    val tree2 = backup (#decay param) tree1 (id,(#value node))
  in
    tree2
  end

(* -------------------------------------------------------------------------
   Score of a choice in a policy according to pUCT formula.
   ------------------------------------------------------------------------- *)

fun puct_choice param tree vtot ((move,polv),cid) =
  let
    val (sum,vis) =
      let val child = dfind cid tree in ((#sum child),(#vis child)) end
      handle NotFound => (0.0,0.0)
    val exploitation = sum / (vis + 1.0)
    val exploration  = (polv * Math.sqrt vtot) / (vis + 1.0)
  in
    exploitation + (#explo_coeff param) * exploration
  end

(* -------------------------------------------------------------------------
   Selection of a node to extend by traversing the tree.
   ------------------------------------------------------------------------- *)

datatype ('a,'b) select = Backup of (id * real) | NodeExtension of (id * id)

fun score_status status = case status of
    Undecided => raise ERR "score_status" ""
  | Win => 1.0
  | Lose => 0.0

fun select_child obj tree id =
  let
    val node = dfind id tree
    val status = (#status_of (#game obj)) (#board (dfind id tree))
  in
    if status <> Undecided then Backup (id,score_status status) else
      let
        val param = #mcts_param obj
        val l1 = map_assoc (puct_choice param tree (#vis node)) (#pol node)
        val _ = if null l1 then raise ERR "select_child" "" else ()
        val l2 = dict_sort compare_rmax l1
        val cid  = snd (fst (hd l2))
      in
        if not (dmem cid tree)
        then NodeExtension (id,cid)
        else select_child obj tree cid
      end
  end

(* -------------------------------------------------------------------------
   Expansion + creation + backup
   ------------------------------------------------------------------------- *)

fun find_move pol cid =
  let val r = valOf (List.find (fn (_,x) => x = cid) pol) in
    fst (fst r)
  end
  handle Option => raise ERR "find_move" ""

fun expand obj tree (id,cid) =
  let
    val node = dfind id tree
    val board1 = #board node
    val move = find_move (#pol node) cid
    val board2 = (#apply_move (#game obj)) move board1
  in
    node_create_backup obj tree (cid,board2)
  end

(* -------------------------------------------------------------------------
   MCTS
   ------------------------------------------------------------------------- *)

fun starttree_of obj board =
  node_create_backup obj (dempty id_compare) ([],board)

fun mcts obj starttree =
  let
    val param = #mcts_param obj
    fun loop tree =
      if #vis (dfind [] tree) > Real.fromInt (#nsim param) + 0.5 orelse
         (#stopatwin_flag param andalso #status (dfind [] tree) = Win)
      then tree else
        let val newtree = case select_child obj tree [] of
            Backup (id,sc) => backup (#decay param) tree (id,sc)
          | NodeExtension (id,cid) => expand obj tree (id,cid)
        in
          loop newtree
        end
  in
    loop starttree
  end

(* -------------------------------------------------------------------------
   Statistics
   ------------------------------------------------------------------------- *)

fun mostexplored_child tree id =
  let
    val node  = dfind id tree
    val cidl0 = map snd (#pol node)
    fun visit_of_child cid =
      SOME (cid, #vis (dfind cid tree))
      handle NotFound => NONE
    val cidl1 = List.mapPartial visit_of_child cidl0
  in
    if null cidl1
    then NONE
    else SOME (fst (hd (dict_sort compare_rmax cidl1)))
  end

fun mostexplored_path tree id =
  if not (dmem id tree) then [] else
  (
  case mostexplored_child tree id of
    NONE => []
  | SOME cid => cid :: mostexplored_path tree cid
  )

fun max_depth tree id =
  if not (dmem id tree) then 0 else
  let
    val node = dfind id tree
    val cidl = map snd (#pol node)
    val l = map (max_depth tree) cidl
  in
    1 + (if null l then 0 else list_imax l)
  end

fun is_win tree id = #status (dfind id tree) = Win handle NotFound => false

fun trace_win status_of tree id =
  if not (dmem id tree) then raise ERR "trace_win" "id is not a node" else
  let
    val node = dfind id tree
    val cidl = map snd (#pol node)
    val l = filter (is_win tree) cidl
  in
    if status_of (#board node) = Win then [node] else
    if null l then raise ERR "trace_win" "no winning path" else
    node :: trace_win status_of tree (hd l)
  end

(* -------------------------------------------------------------------------
   Toy example: the goal of this task is to reach a positive number starting
   from zero by incrementing or decrementing.
   ------------------------------------------------------------------------- *)

type toy_board = (int * int)
datatype toy_move = Incr | Decr
val toy_movel = [Incr,Decr];

fun toy_status_of (start,finish) =
    if start >= finish then Win
    else if start < 0 then Lose else Undecided;

fun toy_available_move board move = true

fun toy_apply_move m (start,finish) = case m of
   Incr => (start+1,finish)
 | Decr => (start-1,finish)

fun toy_string_of_move m = case m of
   Incr => "Incr"
 | Decr => "Decr"

fun toy_move_compare (a,b) =
  String.compare (toy_string_of_move a, toy_string_of_move b)

val toy_game =
  {
  board_compare = cpl_compare Int.compare Int.compare,
  string_of_board = fn (a,b) => (its a ^ " " ^ its b),
  movel = toy_movel,
  move_compare = toy_move_compare,
  string_of_move = toy_string_of_move,
  status_of = toy_status_of,
  available_move = toy_available_move,
  apply_move = toy_apply_move
  }

(*
load "aiLib"; open aiLib;
load "psMCTS"; open psMCTS;

val mcts_param =
  {
  nsim = 16000,
  stopatwin_flag = true,
  decay = 1.0,
  explo_coeff = 2.0,
  noise_all = false,
  noise_root = false,
  noise_coeff = 0.25,
  noise_gen = gamma_noise_gen 0.2
  };

val mcts_obj : (toy_board,toy_move) mcts_obj =
  {
  mcts_param = mcts_param,
  game = toy_game,
  player = uniform_player toy_game
  };

val starttree = starttree_of mcts_obj (0,10);
val (tree,t) = add_time (mcts mcts_obj) starttree;
val nodel = trace_win (#status_of (#game mcts_obj)) tree [];

*)


end (* struct *)
