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
   Global fixed parameters
   ------------------------------------------------------------------------- *)

val exploration_coeff = ref 2.0
val temperature_flag = ref false
val alpha_glob = ref 0.2
val stopatwin_flag = ref false

(* -------------------------------------------------------------------------
   Node
   ------------------------------------------------------------------------- *)

datatype status = Undecided | Win | Lose

type id = int list (* node identifier *)
val id_compare = list_compare Int.compare
type 'b pol = (('b * real) * id) list
type 'b dis = ((('b * real) * id) * real) list

type ('a,'b) node =
{
  pol    : 'b pol,
  sit    : 'a,
  sum    : real,
  vis    : real,
  status : status
}

type ('a,'b) tree = (id, ('a,'b) node) Redblackmap.dict

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

fun update_node decay tree eval {pol,sit,sum,vis,status} =
  let val newstatus =
    if status <> Undecided then status
    else if exists_win tree pol then Win
    else if all_lose tree pol then Lose 
    else Undecided
  in
    {pol=pol, sit=sit, sum=sum+eval, vis=vis+1.0, status=newstatus}
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
    if sum <= 0.0001 then raise ERR "proba_norm" "" else
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
    val {pol,sit,sum,vis,status} = dfind [] tree
    val noisel = dirichlet_noise (!alpha_glob) (length pol)
    fun f (((move,polv),cid),noise) = ((move, 0.75 * polv + 0.25 * noise), cid)
    val newpol = map f (combine (pol,noisel))
  in
    dadd [] {pol=newpol,sit=sit,sum=sum,vis=vis,status=status} tree
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

fun node_create_backup param tree (id,sit) =
  let
    fun wrap_poli poli = let fun f i x = (x, i :: id) in mapi f poli end
    val status = #status_of param sit 
    val (eval,poli) = case status of
        Win       => (1.0,[])
      | Lose      => (0.0,[])
      | Undecided => #fevalpoli param sit
    val node = {pol=rescale_pol (wrap_poli poli),
                sit=sit, sum=0.0, vis=0.0, status=status}
    val tree1 = dadd id node tree
    val tree2 = backup (#decay param) tree1 (id,eval)
  in
    tree2
  end

(* -------------------------------------------------------------------------
   Value of a choice in a policy according to PCUT formula.
   ------------------------------------------------------------------------- *)

fun value_choice tree vtot ((move,polv),cid) =
  let
    val (sum,vis) =
      let val child = dfind cid tree in ((#sum child),(#vis child)) end
      handle NotFound => (0.0,0.0)
    val exploitation = sum / (vis + 1.0)
    val exploration  = (polv * Math.sqrt vtot) / (vis + 1.0)
  in
    exploitation + (!exploration_coeff) * exploration
  end

(* -------------------------------------------------------------------------
   Selection of a node to extend by traversing the tree.
   Assumption: every move proposed by the fevalpoli is applicable.
   ------------------------------------------------------------------------- *)

datatype ('a,'b) select = Backup of (id * real) | NodeExtension of (id * id)

fun score_status status = case status of 
    Undecided => raise ERR "score_status" "" 
  | Win => 1.0
  | Lose => 0.0

fun select_child param tree id =
  let 
    val node = dfind id tree 
    val status = #status_of param (#sit (dfind id tree))
  in
    if status <> Undecided then Backup (id,score_status status) else
      let
        val l1 = map_assoc (value_choice tree (#vis node)) (#pol node)
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
    val sit1 = #sit node
    val move = find_move (#pol node) cid
    val sit2 = (#apply_move param) move sit1
  in
    node_create_backup param tree (cid,sit2)
  end

(* -------------------------------------------------------------------------
   MCTS
   ------------------------------------------------------------------------- *)

type ('a,'b) mctsparam = 
  {
  nsim : int, decay : real, noise : bool,
  status_of : 'a -> status,
  apply_move : 'b -> 'a -> 'a,
  fevalpoli : 'a -> real * ('b * real) list
  }

fun starttree_of param startsit =
  node_create_backup param (dempty id_compare) ([],startsit)

fun mcts param starttree =  
  let
    val starttree_noise =
      if #noise param then add_root_noise starttree else starttree
    fun loop tree =
      if #vis (dfind [] tree) > Real.fromInt (#nsim param) + 0.5 orelse 
         (!stopatwin_flag andalso #status (dfind [] tree) = Win)      
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

fun root_variation tree = node_variation tree []

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
  if not (dmem id tree) then raise ERR "trace_win" "" else
  let 
    val node = dfind id tree
    val cidl = map snd (#pol node)
    val l = filter (is_win tree) cidl
  in
    if status_of (#sit node) = Win then [node] else
    if null l then raise ERR "trace_win" "" else
    node :: trace_win status_of tree (hd l)
  end

(* -------------------------------------------------------------------------
   Big steps and example extraction
   ------------------------------------------------------------------------- *)

fun make_distrib tree =
  let
    val pol = #pol (dfind [] tree)
    val _ = if null pol then raise ERR "make_distrib" "pol" else ()
    fun f (_,cid) = #vis (dfind cid tree) handle NotFound => 0.0
    val dis = map_assoc f pol 
    val tot = sum_real (map snd dis)
    val _ = if tot < 0.5 then raise ERR "make_distrib" "tot" else ()
  in
    (dis,tot)
  end

fun evalpoli_example tree =
  let
    val root = dfind [] tree
    val (dis,tot) = make_distrib tree
    val eval = #sum root / #vis root
    val poli = map (fn (((move,_),_),r) => (move,r / tot)) dis
  in
    (eval,poli)
  end

fun print_distrib g l =
  let
    fun f1 (((move,r),_),_) = g move ^ " " ^ (rts (approx 4 r))
    fun f2 (((move,_),_),r) = g move ^ " " ^ (rts (approx 4 r))
  in
    print_endline ("  " ^ String.concatWith ", " (map f1 l));
    print_endline ("  " ^ String.concatWith ", " (map f2 l))
  end

fun select_bigstep tree =
  let 
    val (d,_) = make_distrib tree 
    val choice = 
      if !temperature_flag then select_in_distrib d else best_in_distrib d
  in
    (snd choice, d)
  end


end (* struct *)
