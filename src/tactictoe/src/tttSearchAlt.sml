(* ========================================================================= *)
(* FILE          : tttSearchAlt.sml                                          *)
(* DESCRIPTION   : MCTS instantiation: tactical prover                       *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure tttSearchAlt  :> tttSearchAlt =
struct
 
open HolKernel boolLib Abbrev tttTools tttNN tttNNtree tttMCTS tttSynt

val ERR = mk_HOL_ERR "tttSearchAlt"
val dbg = dbg_file "tttSearchAlt"

(* Tools *)
fun dset cmp l = dnew cmp (map (fn x => (x,())) l)
fun has_boolty x = type_of x = bool

(* -------------------------------------------------------------------------
   Timers (Move timers to MCTS ?)
   ------------------------------------------------------------------------- *)

val fevalpolitime = ref 0.0
val statusoftime  = ref 0.0
val applymovetime = ref 0.0
val synttime      = ref 0.0

fun fevalpoli_timer f x  = total_time fevalpolitime f x
fun status_of_timer f x  = total_time statusoftime f x
fun apply_move_timer f x = total_time applymovetime f x
fun synt_timer f x       = total_time synttime f x
 
fun init_timers () =
  (
  backuptime    := 0.0;
  selecttime    := 0.0;
  fevalpolitime := 0.0;
  statusoftime  := 0.0;
  applymovetime := 0.0;
  synttime      := 0.0
  )

fun string_of_timers tim =
  let 
    val sl = 
      [
      "total time      : " ^ Real.toString tim,
      "backup time     : " ^ Real.toString (!backuptime), 
      "select time     : " ^ Real.toString (!selecttime), 
      "synt time       : " ^ Real.toString (!synttime), 
      "fevalpoli time  : " ^ Real.toString (!fevalpolitime), 
      "status_of time  : " ^ Real.toString (!statusoftime), 
      "apply_move time : " ^ Real.toString (!applymovetime)
      ]
  in
    String.concatWith "\n" sl
  end

(* -------------------------------------------------------------------------
   Game primitives
   ------------------------------------------------------------------------- *)

(* board *)
datatype search_board = Board1 of goal | Board2 of goal list

fun dest_board1 x = case x of
    Board1 g => g
  | _        => raise ERR "dest_board1" ""

fun dest_board2 x = case x of
    Board2 gl => gl
  | _         => raise ERR "dest_board2" ""


(* move *)
datatype 'a search_move = 
    Player1 of ('a * (search_board pos -> search_board pos))  
  | Player2 of ('a * (search_board pos -> search_board pos))

(* starting position *)
fun search_mk_startpos cj = (true, Board1 ([],cj))

(* -------------------------------------------------------------------------
   Status (end of the game)
   ------------------------------------------------------------------------- *)

fun search_status_of pos =
  if not (fst pos) andalso null (dest_board2 (snd pos)) 
  then Win
  else Undecided

(* -------------------------------------------------------------------------
   Applying a move
   ------------------------------------------------------------------------- *)

fun search_apply_move move pos = case move of
    Player1 (_,movef)  => movef pos
  | Player2 (_,movef)  => movef pos

(* -------------------------------------------------------------------------
   MCTS wrapper
   ------------------------------------------------------------------------- *)

fun search_mcts (nsim,decay) fevalpoli target =
  let
    val _ = init_timers ()
    val fevalpoli'  = fevalpoli_timer fevalpoli
    val status_of   = status_of_timer search_status_of
    val apply_move  = apply_move_timer search_apply_move
    val startpos    = search_mk_startpos target
    val (tree,tim)  =
      add_time (mcts (nsim,decay) fevalpoli' status_of apply_move) startpos
    val timerinfo   = string_of_timers tim
    val _ = print_endline timerinfo
  in
    (target,tree)
  end   

(* -------------------------------------------------------------------------
   Statistics
   ------------------------------------------------------------------------- *)

datatype wintree = Wleaf of int list | Wnode of (int list * wintree list)

fun winning_tree tree id =
  let 
    val node  = dfind id tree 
    val cidl0 = map snd (#pol node)
    fun is_win cid = 
      (#status (dfind cid tree) = Win handle NotFound => false)
    val cidl1 = filter is_win cidl0
  in
    if null cidl1 
    then Wleaf id 
      else Wnode (id, map (winning_tree tree) cidl1)
  end

fun string_of_pos pos = case pos of
    (true, Board1 g)   => string_of_goal g
  | (false, Board2 gl) => String.concatWith "  ||  " (map string_of_goal gl)
  | _ => raise ERR "string_of_pos" ""

fun string_of_wintree tree wintree =
  let
    fun string_of_id id = String.concatWith "." (map int_to_string (rev id))
    fun f id = string_of_id id ^ ": " ^ string_of_pos (#pos (dfind id tree))
  in
    case wintree of
      Wleaf id     => f id
    | Wnode (id,l) => f id ^ "\n" ^
      String.concatWith "\n" (map (string_of_wintree tree) l)
  end


(* Example
  load "tttSearchAlt"; 
  open tttTools tttMCTS tttSearchAlt;
  val target = ``0 = 0 + 0`` ;
*)


(* code to be moved
    
  fun is_nodewin node = #status node = Win
  fun is_treewin tree = is_nodewin (dfind [0] tree)  

  val _    = 
      log (int_to_string i ^ ": " ^ term_to_string target)  

  val status = #status (dfind [0] tree)
    val _ = log ("  " ^ string_of_status status)
    val proof_file = 
      "exp/proof/gen" ^ int_to_string ngen ^ "/" ^ int_to_string i
    val wintrees = if not (status = Win) then "NoProof" else
      let val wintree = winning_tree tree [0] in 
        "Proof" ^ "\n" ^ string_of_wintree 0 tree wintree
      end
    val _ = writel_path tactictoe_dir proof_file 
      [timerinfo ^ "\n\n" ^ wintrees]

fun success_rate l =
  let val winl = map fst (filter (is_treewin o snd) l) in
    length winl
  end

*)


end (* struct *)
