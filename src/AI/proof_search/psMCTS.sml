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
  apply_move : ('a,'b) tree * id -> 'b -> 'a -> ('a * ('a,'b) tree),
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
  timer : real option,
  nsim : int option,
  stopatwin_flag : bool,
  decay : real,
  explo_coeff : real,
  noise_root : bool,
  noise_all : bool,
  noise_coeff : real,
  noise_gen : unit -> real,
  noconfl : bool,
  avoidlose : bool,
  evalwin : bool
  }

type ('a,'b) mctsobj =
  {mctsparam : mctsparam, game : ('a,'b) game, player : ('a,'b) player}

(* -------------------------------------------------------------------------
   Backup
   ------------------------------------------------------------------------- *)

fun quant_status quant test tree pol =
  let
    val cidl = map snd pol
    fun is_status cid =
      test (#status (dfind cid tree)) handle NotFound => false
  in
    quant is_status cidl
  end

fun exists_win tree pol = quant_status exists is_win tree pol
fun all_lose tree pol = quant_status all is_lose tree pol
fun update_node decay tree reward {board,pol,value,stati,sum,vis,status} =
  let val newstatus =
    if not (is_undecided status) then status
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

fun node_create_backup obj (tree,cache) (id,board) =
  let
    val game = #game obj
    val param = #mctsparam obj
    val node =
      let
        fun add_cid pol = let fun f i x = (x, i :: id) in mapi f pol end
        val stati = 
          if (#noconfl param andalso dmem board cache)
          then Lose
          else (#status_of game) board
        val stati' =
          if is_undecided stati andalso null (#available_movel game board)
          then Lose
          else stati
        val (value,pol1) = case stati' of
            Win => (if #evalwin param
                    then fst ((#player obj) board)
                    else 1.0, [])
          | Lose => (0.0,[])
          | Undecided => (#player obj) board
        val pol2 = normalize_prepol pol1
        val pol3 = if #noise_all param then add_noise param pol2 else pol2
      in
        {pol= add_cid pol3, value=value, stati=stati',
         board=board, sum=0.0, vis=0.0, status=stati'}
      end
    val tree1 = dadd id node tree
    val tree2 = backup (#decay param) tree1 (id, #value node)
  in
    (tree2, if #noconfl param then dadd board id cache else cache)
  end

fun add_rootnoise param tree =
  let
    val {pol,value,stati,board,sum,vis,status} = dfind [] tree
    val prepol = add_noise param (map fst pol)
    val newpol = combine (prepol, map snd pol)
  in
    dadd [] {pol= newpol, value=value, stati=stati,
     board=board, sum=sum, vis=vis, status=status} tree
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

datatype ('a,'b) select = 
   Backup of (id * real) | 
   NodeExtension of (id * id) | 
   NoSelection

fun lead_lose tree ((move,polv),cid) =
  (is_lose (#status (dfind cid tree)) handle NotFound => false)

fun select_child obj tree id =
  let
    val node = dfind id tree
    val stati = #stati node
    val status = #status node
    val param = #mctsparam obj
  in
    if not (is_undecided stati)
      then Backup (id, if #evalwin param andalso is_win stati
                       then fst ((#player obj) (#board node)) (* inefficient *)
                       else score_status stati)
    else if #avoidlose param andalso is_lose status
      then Backup (id, score_status status)
    else
    let val l0 =
      if #avoidlose param
      then filter (not o lead_lose tree) (#pol node)
      else #pol node
    in
      if null l0 then NoSelection else
      let
        val l1 = map_assoc (puct_choice param tree (#vis node)) l0
        val l2 = dict_sort compare_rmax l1
        val cid  = snd (fst (hd l2))
      in
        if not (dmem cid tree)
        then NodeExtension (id,cid)
        else select_child obj tree cid
      end
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

fun expand obj (tree,cache) (id,cid) =
  let
    val node = dfind id tree
    val board1 = #board node
    val move = find_move (#pol node) cid
    val (board2,newtree) = (#apply_move (#game obj)) (tree,id) move board1
  in
    node_create_backup obj (tree,cache) (cid,board2)
  end

(* -------------------------------------------------------------------------
   MCTS
   ------------------------------------------------------------------------- *)

fun starttree_of obj board =
  node_create_backup obj
    (dempty id_compare, dempty (#board_compare (#game obj))) ([],board)

fun is_timeout timer tree param =
  (isSome (#nsim param) andalso
   #vis (dfind [] tree) > Real.fromInt (valOf (#nsim param)) + 0.5)
  orelse
  (isSome (#timer param) andalso
   Timer.checkRealTimer timer > Time.fromReal (valOf (#timer param)))  
  orelse
  (#stopatwin_flag param andalso is_win (#status (dfind [] tree)))

fun check_success tree =
  if is_win (#status (dfind [] tree)) then Success else Timeout  

fun mcts obj (starttree,startcache) =
  let
    val timer = Timer.startRealTimer ()
    val param = #mctsparam obj
    fun loop (tree,cache) =
      if is_timeout timer tree param 
      then (check_success tree, (tree,cache)) 
      else
        case select_child obj tree [] of
            Backup (id,sc) => loop (backup (#decay param) tree (id,sc), cache)
          | NodeExtension (id,cid) => loop (expand obj (tree,cache) (id,cid))
          | NoSelection => (Saturated, (tree, cache))
  in
    loop (starttree,startcache)
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

fun trace_win tree id =
  let
    val _ = if not (dmem id tree)
            then raise ERR "trace_win" "id is not a node"
            else ()
    val node = dfind id tree
    val cidl = map snd (#pol node)
    fun loc_is_win tree id = (is_win (#status (dfind id tree))
                         handle NotFound => false)
    val l = filter (loc_is_win tree) cidl
  in
    if is_win (#stati node) then [node] else
    if null l then raise ERR "trace_win" "no winning path" else
    node :: trace_win tree (hd l)
  end

(* does not record last state *)
fun trace_win_movel tree id =
  let
    val _ = if not (dmem id tree)
            then raise ERR "trace_win" "id is not a node"
            else ()
    val node = dfind id tree
  in
    if is_win (#stati node) then [] else
    let
      fun loc_is_win tree (_,x) = 
         (is_win (#status (dfind x tree))
          handle NotFound => false)
      val l = filter (loc_is_win tree) (#pol node)
    in
      if null l then raise ERR "trace_win" "no winning path" else
      let val ((move,_),cid) = hd l in
        (#board node, move) :: trace_win_movel tree cid
      end
    end
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

fun toy_apply_move (tree,id) move (start,finish,timer) = case move of
   Incr => ((start+1,finish,timer-1), tree)
 | Decr => ((start-1,finish,timer-1), tree)

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
  {
  timer = SOME 5.0,
  nsim = (NONE : int option),
  stopatwin_flag = true,
  decay = 1.0,
  explo_coeff = 2.0,
  noise_all = false,
  noise_root = false,
  noise_coeff = 0.25,
  noise_gen = gamma_noise_gen 0.2,
  noconfl = false,
  avoidlose = false,
  evalwin = false
  };

val mctsobj : (toy_board,toy_move) mctsobj =
  {
  mctsparam = mctsparam,
  game = toy_game,
  player = uniform_player toy_game
  };

val starttree = starttree_of mctsobj (0,10,100);
val ((sstatus,(tree,_)),t) = add_time (mcts mctsobj) starttree; 
dlength tree;
val root = dfind [] tree;
val nodel = trace_win tree [];
*)


end (* struct *)
