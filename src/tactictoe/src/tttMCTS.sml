(* ========================================================================== *)
(* FILE          : tttMCTS.sml                                                *)
(* DESCRIPTION   : MCTS algorithm                                             *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University          *)
(* DATE          : 2018                                                       *)
(* ========================================================================== *)

structure tttMCTS :> tttMCTS =
struct
 
open HolKernel boolLib Abbrev tttTools tttNN

val ERR = mk_HOL_ERR "tttMCTS"
val dbg = dbg_file "tttMCTS"

(*----------------------------------------------------------------------------
 * Node
 *----------------------------------------------------------------------------*)

type 'a pos = bool * 'a list option
type choice = (string * real * int list)

type 'a node = 
{
  pol   : choice list,
  pos   : 'a pos,
  id    : int list,
  sum   : real ref,
  vis   : real ref
}

type 'a tree = (int list, 'a node) Redblackmap.dict

(*
  ---------------------------------------------------------------------------
  Backup
  --------------------------------------------------------------------------- *)

fun backup tree (id,eval) =
  let 
    val node = dfind id tree
    val (sum,vis) = (#sum node, #vis node)
  in
    sum := eval + !sum;
    vis := 1.0 + !vis;
    case tl id of
      []  => () (* root *)
    | pid => backup tree (pid, eval)
  end

(*
  ---------------------------------------------------------------------------
  Node creation
  --------------------------------------------------------------------------- *)

fun node_create_backup fevalpoli tree id pos =
  let 
    val (eval,poli)  = fevalpoli id pos
    val node = 
      {
      pol = poli,
      pos = pos, 
      id  = id,
      sum = ref 0.0, 
      vis = ref 0.0
      }
    val newtree = dadd id node tree
    val _ = backup newtree (id,eval)
  in
    newtree
  end

(*
  ---------------------------------------------------------------------------
  Evaluation
  --------------------------------------------------------------------------- *)

fun value_child player tree vtot (move, polv, cid) =
  let val (sum,vis) = 
    let val child = dfind cid tree in (!(#sum child),!(#vis child)) end
    handle NotFound => (0.0,0.0)
  in
    if player 
    then 
      sum / (vis + 1.0) +
      (1.0 * polv * Math.sqrt vtot) / (vis + 1.0)
    else 
      (vis - sum) / (vis + 1.0) +
      (1.0 * polv * Math.sqrt vtot) / (vis + 1.0)
  end    

(*
  ---------------------------------------------------------------------------
  Selection (pole =def policy entry)
  --------------------------------------------------------------------------- *)

datatype endcheck = InProgress | Win | Lose 

datatype select =
    StopWin of int list
  | StopLose of int list
  | Expand  of (int list * (string * real * int list))

fun string_of_id id = String.concatWith " " (map int_to_string id)
  

fun string_of_pol pol =
  let fun f (s,r,i) = 
    s ^ " " ^ Real.toString (approx 2 r) ^ " " ^ int_to_string i 
  in
    String.concatWith "\n  " (map f pol)
  end

fun select_child endcheck tree (pid,pole as (_,_,id)) =
  if not (dmem id tree) 
  then (dbg ("Expand " ^ string_of_id id); Expand (pid,pole))
  else
  let val node = dfind id tree in
    case endcheck (#pos node) of
    Win        => (dbg ("Win "  ^ string_of_id id); StopWin id)
  | Lose       => (dbg ("Lose " ^ string_of_id id); StopLose id)
  | InProgress => 
    let
      val pol     = #pol node 
      val _       = dbg "InProgress" 
      val vtot    = !(#vis node)
      val player  = fst (#pos node)
      val l1      = map_assoc (value_child player tree vtot) pol
      val l2      = dict_sort compare_rmax l1
      val newpole = fst (hd l2)
      val _       = dbg ("move: " ^ #1 newpole)
    in
      select_child endcheck tree (id,newpole)
    end
  end

fun traverse endcheck tree = 
  let val dummy_pole = ("",0.0,[0]) in
    select_child endcheck tree ([],dummy_pole)
  end
(*
  ---------------------------------------------------------------------------
  Expansion + backup
  --------------------------------------------------------------------------- *)

fun expand fevalpoli endcheck apply_move tree result =
  case result of
    StopWin id                => (backup tree (id,1.0); tree)
  | StopLose id               => (backup tree (id,0.0); tree)
  | Expand (pid,(move,sc,id)) =>
    let 
      val parent = dfind pid tree
      val pos    = apply_move move (#pos parent)
    in
      node_create_backup fevalpoli tree id pos
    end
 
(*
  ---------------------------------------------------------------------------
  MCTS
  --------------------------------------------------------------------------- *)

fun mcts nsim fevalpoli endcheck apply_move startpos =
  let
    val tree0 = dempty (list_compare Int.compare)
    val tree1 = node_create_backup fevalpoli tree0 [0] startpos
    fun loop nsim tree =
      if nsim <= 0 then tree else
      let 
        val _ = dbg ("\nsimulation " ^ int_to_string nsim)
        val result = traverse endcheck tree
        val newtree = expand fevalpoli endcheck apply_move tree result
      in
        loop (nsim - 1) newtree
      end
  in
    loop nsim tree1
  end

(*
  ---------------------------------------------------------------------------
  Creating a policy for MCTS.
  --------------------------------------------------------------------------- *)

fun rand_evalpoli movel pos =
  (random_real (), map (fn _ => random_real ()) movel)

fun wrap_poli pid poli =
  let fun f i (a,b) = (a, b, i :: pid) in
    mapi f poli
  end

(*
  ---------------------------------------------------------------------------
  Creating a training set for a neural network to learn from.
  --------------------------------------------------------------------------- *)

fun traineval_of_node node = (!(#sum node) / (!(#vis node) + 1.0))

fun trainpoli_of_child tree vtot (move,_,cid) =
  let val vis = !(#vis (dfind cid tree)) handle NotFound => 0.0 in
    (move, vis / vtot)
  end

fun trainpoli_of_node tree node = 
  map (trainpoli_of_child tree (!(#vis node))) (#pol node)

fun trainex_of_node tree (node: 'a node) =
  (traineval_of_node node, map snd (trainpoli_of_node tree node))

(*
  ---------------------------------------------------------------------------
  statistics
  --------------------------------------------------------------------------- *)

fun id_of_move (node: 'a node) move =
  #3 (valOf (List.find (fn x => #1 x = move) (#pol node)))

fun main_variation tree =
  let 
    fun next_node (node: 'a node) =
      let
        val poli = dict_sort compare_rmax (trainpoli_of_node tree node)
        val id   = id_of_move node (fst (hd poli))
      in
        dfind id tree
      end
    val l = ref []
    fun loop_node nodea =
      let val nodeb = next_node nodea in
        (l := nodea :: !l; loop_node nodeb)
      end
      handle _ => rev (nodea :: !l)
  in
    loop_node (dfind [0] tree)
  end

end (* struct *)
