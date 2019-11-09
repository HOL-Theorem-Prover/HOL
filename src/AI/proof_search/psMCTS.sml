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
  {pol: 'b pol, board: 'a, sum: real, vis: real, status: status}
type ('a,'b) tree = (id, ('a,'b) node) Redblackmap.dict

(* -------------------------------------------------------------------------
   Game specification, fep (evaluation + policy) and additional search 
   parameters   
   ------------------------------------------------------------------------- *)

type ('a,'b) gamespec =
  {
  string_of_board : 'a -> string,
  movel: 'b list,
  move_compare : 'b * 'b -> order,
  string_of_move : 'b -> string,
  status_of : 'a -> status,
  available_move : 'a -> 'b -> bool,
  apply_move : ('b -> 'a -> 'a)
  }

type ('a,'b) fep = 'a -> real * ('b * real) list

fun uniform_fep gamespec board =
  (0.0, map (fn x => (x,1.0)) (#movel gamespec))

type ('a,'b) mcts_param =
  {
  nsim : int, stopatwin_flag : bool, decay : real, explo_coeff : real,
  noise_flag : bool, noise_coeff : real, noise_alpha : real,
  gamespec : ('a,'b) gamespec,
  fep : ('a,'b) fep
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

fun update_node decay tree eval {pol,board,sum,vis,status} =
  let val newstatus =
    if status <> Undecided then status
    else if exists_win tree pol then Win
    else if all_lose tree pol then Lose
    else Undecided
  in
    {pol=pol, board=board, sum=sum+eval, vis=vis+1.0, status=newstatus}
  end

fun backup decay tree (id,eval) =
  let
    val node1 = dfind id tree
    val node2 = update_node decay tree eval node1
    val newtree = dadd id node2 tree
  in
    if null id then newtree else backup decay newtree (tl id, decay * eval)
  end

(* --------------------------------------------------------------------------
   Dirichlet noise
   ------------------------------------------------------------------------- *)

(* divides first number by 100 to get gamma(alpha) *)
val gammatable =
  [(1, 99.43258512),(2, 49.44221016),(3, 32.78499835),(4, 24.46095502),
   (5, 19.47008531),(6, 16.14572749),(7, 13.77360061),(8, 11.99656638),
   (9, 10.61621654),(10, 9.513507699),(20, 4.590843712),(30, 2.991568988),
   (40, 2.218159544),(50, 1.772453851),(60, 1.489192249),(70, 1.298055333),
   (80, 1.164229714),(90, 1.068628702)]

fun gamma_of alpha =
  assoc (Real.round (alpha * 100.0)) gammatable
  handle HOL_ERR _ => raise ERR "gamma_of" (rts alpha)

fun gamma_density alpha x =
  (Math.pow (x, alpha - 1.0) * Math.exp (~ x)) / gamma_of alpha

fun interval (step:real) (a,b) =
  if a + (step / 2.0) > b then [b] else a :: interval step (a + step,b)

fun gamma_distrib alpha =
  map_assoc (gamma_density alpha) (interval 0.01 (0.01,10.0));

fun dirichlet_noise_plain alpha n =
  if n = 0 then [] else
    List.tabulate (n, fn _ => select_in_distrib (gamma_distrib alpha))

fun dirichlet_noise alpha n =
  normalize_proba (dirichlet_noise_plain alpha n)

fun normalize_pol pol =
  let 
    val (l1,l2) = split pol 
    val (l1a,l1b) = split l1
  in 
    combine (combine (l1a, normalize_proba l1b), l2) 
  end

fun add_root_noise param tree =
  let
    val {pol,board,sum,vis,status} = dfind [] tree
    val noisel1 = dirichlet_noise_plain (#noise_alpha param) (length pol)
    val noisel2 = normalize_proba noisel1
    fun f (((move,polv),cid),noise) =
      let 
        val coeff = #noise_coeff param
        val newpolv = (1.0 - coeff) * polv + coeff * noise 
      in
        ((move,newpolv), cid)
      end
    val newpol = normalize_pol (map f (combine (pol,noisel2)))
  in
    dadd [] {pol=newpol,board=board,sum=sum,vis=vis,status=status} tree
  end

(* -------------------------------------------------------------------------
   Node creation
   ------------------------------------------------------------------------- *)

fun rescale_pol pol =
  let
    val tot = sum_real (map (snd o fst) pol)
    fun norm ((move,polv),cid) = ((move,polv / tot),cid)
  in
    if tot > 0.01 then map norm pol else pol
  end

fun filter_available gamespec board (e,p) =
  let 
    val p' = filter (fn (m,_) => (#available_move gamespec) board m) p
    val _ = if null p' then raise ERR "filter_available" "" else ()
  in
    (e,p') 
  end

fun node_create_backup param tree (id,board) =
  let
    val gamespec = #gamespec param
    fun wrap_poli poli = let fun f i x = (x, i :: id) in mapi f poli end
    val status = (#status_of gamespec) board
    val (eval,poli) = case status of
        Win       => (1.0,[])
      | Lose      => (0.0,[])
      | Undecided => filter_available gamespec board ((#fep param) board)
    val node = {pol=rescale_pol (wrap_poli poli),
                board=board, sum=0.0, vis=0.0, status=status}
    val tree1 = dadd id node tree
    val tree2 = backup (#decay param) tree1 (id,eval)
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

fun select_child param tree id =
  let
    val node = dfind id tree
    val status = (#status_of (#gamespec param)) (#board (dfind id tree))
  in
    if status <> Undecided then Backup (id,score_status status) else
      let
        val l1 = map_assoc (puct_choice param tree (#vis node)) (#pol node)
        val _ = if null l1 then raise ERR "select_child" "" else ()
        val l2 = dict_sort compare_rmax l1
        val cid  = snd (fst (hd l2))
      in
        if not (dmem cid tree)
        then NodeExtension (id,cid)
        else select_child param tree cid
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

fun expand param tree (id,cid) =
  let
    val node = dfind id tree
    val board1 = #board node
    val move = find_move (#pol node) cid
    val board2 = (#apply_move (#gamespec param)) move board1
  in
    node_create_backup param tree (cid,board2)
  end

(* -------------------------------------------------------------------------
   MCTS
   ------------------------------------------------------------------------- *)

fun starttree_of param board =
  node_create_backup param (dempty id_compare) ([],board)

fun mcts (param : ('a, 'b) mcts_param) starttree =
  let
    val starttree_noise =
      if #noise_flag param then add_root_noise param starttree else starttree
    fun loop tree =
      if #vis (dfind [] tree) > Real.fromInt (#nsim param) + 0.5 orelse
         (#stopatwin_flag param andalso #status (dfind [] tree) = Win)
      then tree else
        let val newtree = case select_child param tree [] of
            Backup (id,sc) => backup (#decay param) tree (id,sc)
          | NodeExtension (id,cid) => expand param tree (id,cid)
        in
          loop newtree
        end
  in
    loop starttree_noise
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

val toy_gamespec =
  {
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

val param : (toy_board,toy_move) mcts_param =
  {
  nsim = 16000, 
  stopatwin_flag = true,
  decay = 1.0,
  explo_coeff = 2.0,
  noise_flag = false,
  noise_coeff = 0.25,
  noise_alpha = 0.2,
  gamespec = toy_gamespec,
  fep = uniform_fep toy_gamespec
  };

val starttree = starttree_of param (0,10);
val tree = mcts param starttree;
val nodel = trace_win (#status_of (#gamespec param)) tree [];
*)


end (* struct *)
