signature tttSearchAlt =
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
  datatype search_board = Board1 of goal | Board2 of goal list
  datatype 'a search_move  = 
    Player1 of ('a * (search_board pos -> search_board pos))  
  | Player2 of ('a * (search_board pos -> search_board pos))

  (* destructors *)
  val dest_board1     : search_board -> goal
  val dest_board2     : search_board -> goal list

  (* starting position *)
  val search_mk_startpos : term -> search_board pos

  (* status function *)
  val search_status_of : search_board pos -> tttMCTS.status

  (* apply_move function *)
  val search_apply_move : 
    'a search_move -> search_board pos -> search_board pos
  
  (* statistics *)
  datatype wintree = Wleaf of int list | Wnode of (int list * wintree list)
  val winning_tree : (search_board, 'a search_move) tree -> int list -> wintree

  (* mcts wrapper *)
  val search_mcts : 
    int * real ->
    (search_board pos -> real * ('a search_move * real) list) ->
    term -> 
    term * (search_board, 'a search_move) tree

  (* debugging *)
  val string_of_pos : search_board pos -> string
  val string_of_wintree : 
    (search_board, 'a search_move) tree ->
    wintree ->
    string


end
