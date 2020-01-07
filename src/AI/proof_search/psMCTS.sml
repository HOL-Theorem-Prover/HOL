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
  board : 'a, pol : 'b pol, value : real, stati : status,
  sum : real, vis : real, status : status
  }
type ('a,'b) tree = (id, ('a,'b) node) Redblackmap.dict

(* -------------------------------------------------------------------------
   Game specification
   ------------------------------------------------------------------------- *)

type ('a,'b) game =
  {
  status_of : 'a -> status, 
  apply_move : 'b -> 'a -> 'a,
  available_movel : 'a -> 'b list,
  string_of_board : 'a -> string,
  string_of_move : 'b -> string
  }

fun uniform_player game board = 
  (0.0, map (fn x => (x,1.0)) (#available_movel game board))

fun random_player game board = 
  (random_real (), map (fn x => (x,1.0)) (#available_movel game board))

type ('a,'b) player = 'a -> real * ('b * real) list

type mctsparam =
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

type ('a,'b) mctsobj =
  {mctsparam : mctsparam, game : ('a,'b) game, player : ('a,'b) player}

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

fun update_node decay tree reward {board,pol,value,stati,sum,vis,status} =
  let val newstatus =
    if status <> Undecided then status
    else if exists_win tree pol then Win
    else if all_lose tree pol then Lose
    else Undecided
  in
    {board=board, pol=pol, value=value, stati=stati, 
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

fun node_create_backup obj tree (id,board) =
  let
    val game = #game obj
    val param = #mctsparam obj
    val node =
      let
        fun add_cid pol = let fun f i x = (x, i :: id) in mapi f pol end
        val status = (#status_of game) board
        val (value,pol1) = case status of
            Win       => (1.0,[])
          | Lose      => (0.0,[])
          | Undecided => (#player obj) board
        val pol2 = normalize_prepol pol1
        val pol3 =
          if #noise_all param orelse (#noise_root param andalso null id)
          then add_noise param pol2
          else pol2
      in
        {pol= add_cid pol3, value=value, stati=status,
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
    val status = #stati (dfind id tree)
  in
    if status <> Undecided then Backup (id,score_status status) else
      let
        val param = #mctsparam obj
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
    val param = #mctsparam obj
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

type toy_board = (int * int * int)
datatype toy_move = Incr | Decr

fun toy_status_of (start,finish,timer) =
    if start >= finish then Win
    else if start < 0 orelse timer <= 0 then Lose 
    else Undecided

fun toy_available_movel board = [Incr,Decr]

fun toy_apply_move m (start,finish,timer) = case m of
   Incr => (start+1,finish,timer-1)
 | Decr => (start-1,finish,timer-1)

val toy_game =
  {
  status_of = toy_status_of,
  apply_move = toy_apply_move,
  available_movel = toy_available_movel,
  string_of_board = (fn (a,b,c) => (its a ^ " " ^ its b ^ " " ^ its c)),
  string_of_move = (fn x => case x of Incr => "Incr" | Decr => "Decr") 
  }

(*
load "aiLib"; open aiLib;
load "psMCTS"; open psMCTS;

val mctsparam =
  {
  nsim = 16000,
  stopatwin_flag = false,
  decay = 1.0,
  explo_coeff = 2.0,
  noise_all = false,
  noise_root = false,
  noise_coeff = 0.25,
  noise_gen = gamma_noise_gen 0.2
  };

val mctsobj : (toy_board,toy_move) mctsobj =
  {
  mctsparam = mctsparam,
  game = toy_game,
  player = uniform_player toy_game
  };

val starttree = starttree_of mctsobj (0,10,100);
val (tree,t) = add_time (mcts mctsobj) starttree;
val nodel = trace_win (#status_of (#game mctsobj)) tree [];

*)


end (* struct *)
