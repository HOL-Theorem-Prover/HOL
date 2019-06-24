(* ========================================================================= *)
(* FILE          : psMCTS.sml                                                *)
(* DESCRIPTION   : MCTS algorithm                                            *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

(* -------------------------------------------------------------------------
   Warning: root node has address [0] (not []).
   ------------------------------------------------------------------------- *)

structure psMCTS :> psMCTS =
struct

open HolKernel Abbrev boolLib aiLib

val ERR = mk_HOL_ERR "psMCTS"

(* -------------------------------------------------------------------------
   Global fixed parameters
   ------------------------------------------------------------------------- *)

val exploration_coeff = ref 2.0 (* 2.4 from a comment in Leela chess blog *)

(* -------------------------------------------------------------------------
   Timers
   ------------------------------------------------------------------------- *)

val backuptime = ref 0.0
val selecttime = ref 0.0
val fevalpolitime = ref 0.0
val statusoftime  = ref 0.0
val applymovetime = ref 0.0

fun backup_timer f x = total_time backuptime f x
fun select_timer f x = total_time selecttime f x
fun fevalpoli_timer f x  = total_time fevalpolitime f x
fun status_of_timer f x  = total_time statusoftime f x
fun apply_move_timer f x = total_time applymovetime f x

fun init_timers () =
  (
  backuptime    := 0.0;
  selecttime    := 0.0;
  fevalpolitime := 0.0;
  statusoftime  := 0.0;
  applymovetime := 0.0
  )

fun string_of_timers tim =
  String.concatWith "\n"
    [
    "  backup time     : " ^ Real.toString (!backuptime),
    "  select time     : " ^ Real.toString (!selecttime),
    "  fevalpoli time  : " ^ Real.toString (!fevalpolitime),
    "  status_of time  : " ^ Real.toString (!statusoftime),
    "  apply_move time : " ^ Real.toString (!applymovetime)
    ]

(* -------------------------------------------------------------------------
   Debug
   ------------------------------------------------------------------------- *)

fun string_of_id id = String.concatWith " " (map int_to_string id)

fun string_of_poli poli =
  let fun f ((s,r),i) =
    s ^ " " ^ Real.toString (approx 2 r) ^ " " ^ int_to_string i
  in
    String.concatWith "\n  " (map f poli)
  end

(* -------------------------------------------------------------------------
   Node
   ------------------------------------------------------------------------- *)

datatype status = Undecided | Win | Lose

fun string_of_status status = case status of
    Undecided => "Undecided"
  | Lose      => "Lose"
  | Win       => "Win"

type 'a sit    = bool * 'a
type 'b choice = (('b * real) * int list)

type ('a,'b) node =
{
  pol    : 'b choice list,
  sit    : 'a sit,
  sum    : real,
  vis    : real,
  status : status
}

type ('a,'b) tree = (int list, ('a,'b) node) Redblackmap.dict

(* -------------------------------------------------------------------------
   Backup
   ------------------------------------------------------------------------- *)

fun quant_status quant status tree pol =
  let
    val cidl    = map snd pol
    fun is_status cid = #status (dfind cid tree) = status
                        handle NotFound => false
  in
    quant is_status cidl
  end

fun all_win tree pol     = quant_status all Win tree pol
fun all_lose tree pol    = quant_status all Lose tree pol
fun exists_win tree pol  = quant_status exists Win tree pol
fun exists_lose tree pol = quant_status exists Lose tree pol

fun update_node decay tree eval {pol,sit,sum,vis,status} =
  let
    val newstatus =
      if status = Undecided then
        if fst sit then
          (if exists_win tree pol then Win else
           if all_lose tree pol   then Lose else
           Undecided)
        else
          (if all_win tree pol     then Win else
           if exists_lose tree pol then Lose else
           Undecided)
      else status
  in
    {pol=pol, sit=sit, sum=sum+eval, vis=vis+1.0, status=newstatus}
  end

fun backup decay tree (id,eval) =
  let
    val node1 = dfind id tree
    val node2 = update_node decay tree eval node1
    val newtree = dadd id node2 tree
  in
    case tl id of
      []  => newtree
    | pid => backup decay newtree (pid, decay * eval)
  end

(* --------------------------------------------------------------------------
   Adding dirichlet noise
   ------------------------------------------------------------------------- *)

val alpha_glob = ref 0.2

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

fun proba_norm l =
  let val sum = sum_real l in
    if sum <= 0.0 then raise ERR "proba_norm" "" else
    map (fn x => x / sum) l
  end

fun dirichlet_noise alpha n =
  if n = 0 then [] else
  let val l =
    List.tabulate (n, fn _ => select_in_distrib (gamma_distrib alpha)) in
    proba_norm l
  end

fun add_root_noise tree =
  let
    val {pol,sit,sum,vis,status} = dfind [0] tree
    val noisel = dirichlet_noise (!alpha_glob) (length pol)
    fun f (((move,polv),cid),noise) = ((move, 0.75 * polv + 0.25 * noise), cid)
    val newpol = map f (combine (pol,noisel))
  in
    dadd [0] {pol=newpol,sit=sit,sum=sum,vis=vis,status=status} tree
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

fun node_create_backup decay fevalpoli status_of tree (id,sit) =
  let
    fun wrap_poli poli = let fun f i x = (x, i :: id) in mapi f poli end
    val ((eval,poli),status) =
      case status_of sit of
        Win       => ((1.0,[]),Win)
      | Lose      => ((0.0,[]),Lose)
      | Undecided => (fevalpoli sit, Undecided)
    val node =
      {pol=rescale_pol (wrap_poli poli),
       sit=sit, sum=0.0, vis=0.0, status=status}
    val tree1 = dadd id node tree
    val tree2 = backup_timer (backup decay tree1) (id,eval)
  in
    tree2
  end

(* -------------------------------------------------------------------------
   Value of a choice
   ------------------------------------------------------------------------- *)

fun value_choice player tree vtot ((move,polv),cid) =
  let
    val (sum,vis) =
      let val child = dfind cid tree in ((#sum child),(#vis child)) end
      handle NotFound => (0.0,0.0)
    val exploitation = (if player then sum else vis - sum) / (vis + 1.0)
    val exploration  = (polv * Math.sqrt vtot) / (vis + 1.0)
  in
    exploitation + (!exploration_coeff) * exploration
  end

(* -------------------------------------------------------------------------
   Selection of a node to extend by traversing the tree.
   Arbitrary choice: if no move available then the first player loses.
   ------------------------------------------------------------------------- *)

datatype ('a,'b) select =
  TreeUpdate of ('a,'b) tree | NodeSelect of (int list * int list)

fun select_child decay tree id =
  let
    val node = dfind id tree handle NotFound => raise ERR "select_child" ""
    val pol = #pol node
  in
    if null pol then
      case #status (dfind id tree) of
          Undecided => TreeUpdate (backup decay tree (id,0.0))
          (* raise ERR "select_child" "" *)
        | Win => TreeUpdate (backup decay tree (id,1.0))
        | Lose => TreeUpdate (backup decay tree (id,0.0))
    else
      let
        val player  = fst (#sit node)
        val l1      = map_assoc (value_choice player tree (#vis node)) pol
        val l2      = dict_sort compare_rmax l1
        val choice  = fst (hd l2)
        val cid     = snd choice
      in
        if not (dmem cid tree)
        then NodeSelect (id,cid)
        else select_child decay tree cid
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

fun expand decay fevalpoli status_of apply_move tree (id,cid) =
  let
    val node = dfind id tree
    val sit1 = #sit node
    val move = find_move (#pol node) cid
    val sit2 = apply_move move sit1
  in
    node_create_backup decay fevalpoli status_of tree (cid,sit2)
  end

(* -------------------------------------------------------------------------
   MCTS
   ------------------------------------------------------------------------- *)

type ('a,'b) mcts_param = 
  ( 
    int * real * bool *
    ('a sit -> status) * ('b -> 'a sit -> 'a sit) *
    ('a sit -> real * ('b * real) list)
  )

fun starttree_of (nsim,decay,noiseb,status_of,apply_move,fep) startsit =
  let val empty_tree = dempty (list_compare Int.compare) in
    node_create_backup decay fep status_of empty_tree ([0],startsit)
  end

(* two players *)
val stopatwin_flag = ref false

fun mcts (nsim,decay,noiseb,status_of,apply_move,fep) starttree =
  let
    val starttree_noise =
      if noiseb then add_root_noise starttree else starttree
    val fep_timed = fevalpoli_timer fep
    val status_of_timed = status_of_timer status_of
    val apply_move_timed = apply_move_timer apply_move
    fun loop tree =
      if #vis (dfind [0] tree) > Real.fromInt nsim + 0.5 
         orelse (!stopatwin_flag andalso #status (dfind [0] tree) = Win)      
      then tree 
      else
      let
        val selecto = select_timer (select_child decay tree) [0]
        val newtree  = case selecto of
            TreeUpdate tree_upd => tree_upd
          | NodeSelect (id,cid) => expand decay
          fep_timed status_of_timed apply_move_timed tree (id,cid)
      in
        loop newtree
      end
  in
    loop starttree_noise
  end

fun mk_uniform_fep apply_move movel = 
  let fun fep sit =
    let val movel' = filter (fn x => can (apply_move x) sit) movel in   
      if null movel' 
      then raise ERR "mk_uniform_fep" "no move available"
      else (0.0, map (fn x => (x,1.0)) movel')
    end
  in fep end

fun mcts_uniform nsim (status_of, apply_move, movel) startsit =
  let 
    val fep = mk_uniform_fep apply_move movel
    val param = (nsim,1.0,false,status_of,apply_move,fep)
  in
    mcts param (starttree_of param startsit)
  end

(* -------------------------------------------------------------------------
   Changing the root of the tree to an arbitrary node. Allow reuse of
   the trees during bigsteps.
   ------------------------------------------------------------------------- *)

fun remove_prefix prefix l = case (prefix,l) of
    ([],_) => l
  | (_,[]) => raise ERR "remove_prefix" ""
  | (a1 :: m1, a2 :: m2) =>
    if a1 = a2 then remove_prefix m1 m2 else raise ERR "remove_prefix" ""

fun remove_suffix_add0 suffix l =
  rev (0 :: (remove_prefix (rev suffix) (rev l)))

fun cut_tree tree suffix =
  let
    val l0 = dlist tree
    fun change_entry (id,{pol,sit,sum,vis,status}) =
      let
        fun f x = remove_suffix_add0 suffix x
        val newid = f id
        val newpol = map_snd f pol
      in
        (newid, {pol=newpol, sit=sit, sum=sum, vis=vis, status=status})
      end
    val l1 = mapfilter change_entry l0
  in
    dnew (list_compare Int.compare) l1
  end

(* -------------------------------------------------------------------------
   Statistics
   ------------------------------------------------------------------------- *)

fun best_child tree id =
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

fun node_variation tree id =
  if not (dmem id tree) then [] else
  (
  case best_child tree id of
    NONE => []
  | SOME cid => cid :: node_variation tree cid
  )

fun root_variation tree = node_variation tree [0]

fun max_depth tree id = 
  if not (dmem id tree) then 0 else
  let 
    val node = dfind id tree
    val cidl = map snd (#pol node)
    val l = map (max_depth tree) cidl
  in
    1 + (if null l then 0 else list_imax l)
  end

fun is_win tree id = 
  #status (dfind id tree) = Win handle NotFound => false

fun trace_one_win status_of tree id = 
  if not (dmem id tree) then raise ERR "trace_one_win" "" else
  let 
    val node = dfind id tree
    val cidl = map snd (#pol node)
    val l = filter (is_win tree) cidl
  in
    if status_of (#sit node) = Win then [node] else
    if null l then raise ERR "trace_one_win" "" else
    node :: trace_one_win status_of tree (hd l)
  end

(* -------------------------------------------------------------------------
   Policy distribution
   ------------------------------------------------------------------------- *)

fun make_distrib tree id =
  let
    val node = dfind id tree
    val pol = #pol node
    fun f (_,cid) = SOME (#vis (dfind cid tree)) handle NotFound => NONE
  in
    map_assoc f pol
  end

(* -------------------------------------------------------------------------
   Policy distribution : training examples
   ------------------------------------------------------------------------- *)

fun move_of_cid node cid =
  let val pol = #pol node in fst (assoc cid (map swap pol)) end

fun evalpoli_example tree =
  let
    val root = dfind [0] tree
    val dis0 = make_distrib tree [0]
    val dis1 = map_snd (fn x => if isSome x then valOf x else 0.0) dis0
    val tot  = sum_real (map snd dis1)
  in
    if tot < 0.5 then NONE else
    let
      val eval = #sum root / #vis root
      val poli = map (fn (((move,_),_),r) => (move,r / tot)) dis1
    in
      SOME (eval,poli)
    end
  end

(* -------------------------------------------------------------------------
   Policy distribution: big step selection
   ------------------------------------------------------------------------- *)

fun print_distrib g l =
  let
    fun f1 (((move,r),_),_) = g move ^ " " ^ (rts (approx 4 r))
    fun f2 (((move,_),_),r) = g move ^ " " ^ (rts (approx 4 r))
  in
    print_endline ("  " ^ String.concatWith ", " (map f1 l));
    print_endline ("  " ^ String.concatWith ", " (map f2 l))
  end

fun best_in_distrib distrib =
  let fun cmp (a,b) = Real.compare (snd b,snd a) in
    fst (hd (dict_sort cmp distrib))
  end

val temperature_flag = ref false

fun select_bigstep tree id =
  let
    val node = dfind id tree
    val dis0 = make_distrib tree id
    val dis1 = map_snd (fn x => if isSome x then valOf x else 0.0) dis0
    val dis2 = mapfilter (fn ((_,cid),b) => (cid, valOf b)) dis0
    val tot  = sum_real (map snd dis1)
  in
    if tot < 0.5 (* ends when no moves are available *)
    then ([], NONE)
    else (dis1, SOME (if !temperature_flag 
                      then select_in_distrib dis2 
                      else best_in_distrib dis2))
  end



end (* struct *)
