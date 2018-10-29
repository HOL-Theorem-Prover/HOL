(* ========================================================================= *)
(* FILE          : tttMCTS.sml                                               *)
(* DESCRIPTION   : MCTS algorithm.                                           *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure tttMCTS :> tttMCTS =
struct
 
open HolKernel boolLib Abbrev tttTools tttNN

val ERR = mk_HOL_ERR "tttMCTS"
val dbg = dbg_file "tttMCTS"


val logfile = tactictoe_dir ^ "/exp/log"
val sumfile = tactictoe_dir ^ "/exp/summary"

fun log s = (print_endline s; append_endline logfile s)
fun summary s = 
  (print_endline s; append_endline logfile s; append_endline sumfile s)

fun erase_log () = (erase_file logfile; erase_file sumfile)


(* -------------------------------------------------------------------------
   Global fixed parameters
   ------------------------------------------------------------------------- *)

val exploration_coeff = 1.0

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

val selecttime = ref 0.0
fun select_timer f x = total_time selecttime f x
val backuptime = ref 0.0
fun backup_timer f x = total_time backuptime f x 

(* -------------------------------------------------------------------------
   Node
   ------------------------------------------------------------------------- *)

datatype status = Undecided | Win | Lose

fun string_of_status status = case status of
    Undecided => "Undecided"
  | Lose      => "Lose"
  | Win       => "Win"

type 'a pos    = bool * 'a
type 'b choice = (('b * real) * int list)


type ('a,'b) node = 
{
  pol    : 'b choice list,
  pos    : 'a pos,
  id     : int list,
  sum    : real,
  vis    : real,
  status : status
}

type ('a,'b) tree = (int list, ('a,'b) node) Redblackmap.dict

fun genealogy id = 
  if null id then [] else id :: genealogy (tl id) 

fun access_child tree (_,cid) =
  (case #status (dfind cid tree) of Undecided => true | _ => false)
  handle NotFound => true

fun access_poli tree pol = filter (access_child tree) pol

(* -------------------------------------------------------------------------
   Backup
   ------------------------------------------------------------------------- *)

(* not efficient but conceptually simple *)
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

fun update_node decay tree eval {pol,pos,id,sum,vis,status} =
  let 
    val newstatus =
      if status = Undecided then
        if fst pos then
          (if exists_win tree pol then Win else
           if all_lose tree pol   then Lose else
           Undecided)
        else
          (if all_win tree pol     then Win else
           if exists_lose tree pol then Lose else
           Undecided)
      else status
  in
    {pol=pol, pos=pos, id=id, sum=sum + decay * eval, vis=vis+1.0, status=newstatus} 
  end

fun backup decay tree (id,eval) =
  let
    val node1   = dfind id tree
    val node2   = update_node decay tree eval node1
    val newtree = dadd id node2 tree
  in
    case tl id of
      []  => newtree
    | pid => backup decay newtree (pid,eval)
  end

(*
  ---------------------------------------------------------------------------
  Node creation
  --------------------------------------------------------------------------- *)

fun node_create_backup decay fevalpoli status_of tree (id,pos) =
  let 
    fun wrap_poli poli = let fun f i x = (x, i :: id) in mapi f poli end
    val ((eval,poli),status) = 
      case status_of pos of
        Win       => ((1.0,[]),Win)
      | Lose      => ((0.0,[]),Lose) 
      | Undecided => (fevalpoli pos,Undecided)
    val node           = 
      {pol=wrap_poli poli, pos=pos, id=id, sum=0.0, vis=0.0, status=status}
    val tree1 = dadd id node tree
    val tree2 = backup_timer (backup decay tree1) (id,eval)
  in
    tree2
  end

(*
  ---------------------------------------------------------------------------
  Value of a choice
  --------------------------------------------------------------------------- *)

fun value_choice player tree vtot ((move,polv),cid) =
  let 
    val (sum,vis) = 
      let val child = dfind cid tree in ((#sum child),(#vis child)) end
      handle NotFound => (0.0,0.0)
    val exploitation = (if player then sum else vis - sum) / (vis + 1.0)
    val exploration  = (polv * Math.sqrt vtot) / (vis + 1.0)
  in
    exploitation + exploration_coeff * exploration
  end    

(*
  ---------------------------------------------------------------------------
  Selection of a node to extend by traversing the tree
  --------------------------------------------------------------------------- *)

fun select_child tree id =
  let 
    val node  = dfind id tree handle NotFound => raise ERR "select_child" ""
    val pol   = filter (access_child tree) (#pol node)
  in
    if null pol then raise ERR "select_child" "empty policy" else    
      let
        val player  = fst (#pos node)
        val l1      = map_assoc (value_choice player tree (#vis node)) pol
        val l2      = dict_sort compare_rmax l1
        val choice  = fst (hd l2)
        val cid     = snd choice
      in
        if not (dmem cid tree) 
        then (id,cid)
        else select_child tree cid
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
    val pos1 = #pos node
    val move = find_move (#pol node) cid
    val pos2 = apply_move move pos1
  in
    node_create_backup decay fevalpoli status_of tree (cid,pos2)
  end

(* -------------------------------------------------------------------------
   MCTS
   ------------------------------------------------------------------------- *)

fun mcts (nsim,decay) fevalpoli status_of apply_move startpos =
  let
    val tree0 = dempty (list_compare Int.compare)
    val tree1 = node_create_backup decay 
      fevalpoli status_of tree0 ([0],startpos)
    fun loop nsim tree =
      if nsim <= 0 orelse 
         #status (dfind [0] tree) <> Undecided then tree else
      let
        val (id,cid) = select_timer (select_child tree) [0]
        val newtree  = expand decay 
          fevalpoli status_of apply_move tree (id,cid)
      in
        loop (nsim - 1) newtree
      end
  in
    loop nsim tree1
  end

(* -------------------------------------------------------------------------
   Statistics
   ------------------------------------------------------------------------- *)

datatype wintree = Wleaf of int list | Wnode of (int list * wintree list)

fun wtree_of tree id =
  let 
    val node  = dfind id tree 
    val cidl0 = map snd (#pol node)
    fun is_win cid = 
      (#status (dfind cid tree) = Win handle NotFound => false)
    val cidl1 = filter is_win cidl0
  in
    if null cidl1 
    then Wleaf id 
      else Wnode (id, map (wtree_of tree) cidl1)
  end

fun depth_of_wtree wtree = case wtree of
    Wleaf => 1
  | Wnode (t1,t2) => Int.max (depth_of_wtree t1, depth_of_wtree t2) + 1
  
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

(* -------------------------------------------------------------------------
   Choosing a big step
   ------------------------------------------------------------------------- *)

fun move_win tree cid =
  #status (dfind cid tree) = Win handle NotFound => false

fun visit_of_child tree cid = 
  if not (dmem cid tree) 
  then NONE
  else SOME (cid, #vis (dfind cid tree))

fun print_distrib l = 
  log ("  " ^ String.concatWith " " (map (Real.toString o approx 4 o snd) l))

(* could still contain critical bugs *)
fun proba_child tree id =
  let 
    val node  = dfind id tree
    val cidl0 = map snd (#pol node) 
    val poliwin = map_assoc (move_win tree) cidl0 
    val _ = if #status = Win then 
      log ("  Proof depth: " ^ 
        int_to_string (depth_of_wtree (wtree_of tree id)))
      else ()
  in
    if fst (#pos node) andalso (#status node = Win) andalso (#vis node < 1.1)
      then (log "  Axiom"; NONE)
    else if fst (#pos node) andalso exists snd poliwin
      then 
        let
          fun f (a,x) = if x then SOME (a,1.0) else NONE
          val poliwindis = List.mapPartial f poliwin
        in
          (print_distrib poliwindis; SOME (select_in_distrib poliwindis))
        end
    else
      let val cidl1 = List.mapPartial (visit_of_child tree) cidl0 in
        if null cidl1 
        then (log "  Error: no child"; NONE)
        else (print_distrib cidl1; SOME (select_in_distrib cidl1))
      end
  end


end (* struct *)
