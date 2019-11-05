(* ========================================================================= *)
(* FILE          : psBigSteps.sml                                            *)
(* DESCRIPTION   : MCTS algorithm                                            *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure psBigSteps :> psBigSteps =
struct

open HolKernel Abbrev boolLib aiLib psMCTS

val ERR = mk_HOL_ERR "psBigSteps"

(* -------------------------------------------------------------------------
   Parameters     
   ------------------------------------------------------------------------- *)

type ('a,'b) bigstepsparam =
  {
  temp_flag : bool,
  max_bigsteps : 'a -> int,
  }


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

fun starttree_of param startsit =
  node_create_backup param (dempty id_compare) ([],startsit)

fun mcts param starttree =
  let
    val starttree_noise =
      if #noise param then add_root_noise param starttree else starttree
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
   Tree re-use
   ------------------------------------------------------------------------- *)

fun is_prefix l1 l2 = case (l1,l2) of
    ([],_) => true
  | (_,[]) => false
  | (a1 :: m1, a2 :: m2) => a1 = a2 andalso is_prefix m1 m2 

fun is_suffix l1 l2 = is_prefix (rev l1) (rev l2)

fun rm_prefix l1 l2 = case (l1,l2) of
    ([],_) => l2
  | (_,[]) => raise ERR "rm_prefix" ""
  | (a1 :: m1, a2 :: m2) => 
    (if a1 = a2 then rm_prefix m1 m2 else raise ERR "rm_prefix" "")

fun rm_suffix l1 l2 = rm_prefix (rev l1) (rev l2)

fun cut_tree id tree = 
  let
    val l = filter (fn x => is_suffix id (fst x)) (dlist tree)
    fun change_node (x,{pol,sit,sum,vis,status}) =
      (rm_suffix id x, 
        {pol=map_snd (rm_suffix id) pol,
         sit=sit,sum=sum,vis=vis,status=status})
  in
    dnew id_compare (map change_node l)
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
