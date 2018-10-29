signature tttCutter =
sig
  
  include Abbrev

  (* 'a is the representation of the board *)  
  type 'a pos = bool * 'a
  (* ''b is the representation of a move *)
  type 'b choice = (('b * real) * int list)
  type ('a,'b) node = 
  {
    pol   : 'b choice list,
    pos   : 'a pos,
    id    : int list,
    sum   : real,
    vis   : real,
    status : tttMCTS.status
  }
  type ('a,'b) tree = (int list, ('a,'b) node) Redblackmap.dict 
  
  (* game configuration *)
  datatype cutter_move  = Forget of goal | Cut of term | Choice of goal 
  datatype cutter_board = Board1 of goal | Board2 of goal list
  
  (* destructors *)
  val dest_cutmove    : cutter_move  -> term
  val dest_choicemove : cutter_move  -> goal
  val dest_board1     : cutter_board -> goal
  val dest_board2     : cutter_board -> goal list

  (* starting position *)
  val cutter_mk_startpos : term -> cutter_board pos
  (* policy and evaluation function *)
  val cutter_fevalpoli : 
    term list ->
    (tttNNtree.treenn * tttNNtree.treenn) *
             (tttNNtree.treenn * tttNNtree.treenn) ->
    cutter_board pos -> real * (cutter_move * real) list
  (* status function *)
  val is_refl   : goal -> bool 
  val is_inst   : term -> goal -> bool
  val is_subs   : goal -> bool
  val is_apterm : goal -> bool
  val is_primitive : term list -> goal -> bool
  val cutter_status_of : term list ->  cutter_board pos -> tttMCTS.status

  (* apply_move function *)
  val cutter_apply_move : 
    cutter_move -> cutter_board pos -> cutter_board pos
  
  (* statistics *)
  datatype wintree = Wleaf of int list | Wnode of (int list * wintree list)
  val winning_tree : (cutter_board, cutter_move) tree -> int list -> wintree
  val success_rate : 
    (term * (cutter_board, cutter_move) tree) list -> int 

  (* mcts wrapper *)
  val cutter_mcts :  int * real ->
           term list ->
             (tttNNtree.treenn * tttNNtree.treenn) *
             (tttNNtree.treenn * tttNNtree.treenn) ->
               term list ->
                 cutter_board tttMCTS.pos ->
                   (cutter_board, cutter_move) tttMCTS.tree

  
  (* collecting examples from big steps *)
  val list_collect_exl : 
     int * real ->
           int ->
             term list ->
 (tttNNtree.treenn * tttNNtree.treenn) *
             (tttNNtree.treenn * tttNNtree.treenn) ->
                 term list ->
                   term list ->
                     (
                     (term * real) list * (term * real) list *
                     (term * real) list * (term * real) list) list

  
  val wrap_train_treenn : int * (term * int) list -> (term * real) list -> tttNNtree.treenn

  (* reinforcement learning loop 
  val rl_gen : int ->
           term list * term list ->
             term list ->
               term list ->
                 int * 'a ->
                   tttNNtree.opdict * tttNN.nn * tttNN.nn ->
                     tttNNtree.opdict * tttNNtree.nn * tttNNtree.nn

*)

end
