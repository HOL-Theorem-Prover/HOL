signature psMCTS =
sig

  include Abbrev

  (* outcome *)
  datatype status = Undecided | Win | Lose

  (* search tree: 'a is a board position, 'b is a move *)
  type id = int list
  val id_compare : int list cmp
  type 'b pol = (('b * real) * id) list
  type ('a,'b) node =
    {pol : 'b pol, board : 'a, sum : real, vis : real, status : status}
  type ('a,'b) tree = (id, ('a,'b) node) Redblackmap.dict

  (* dirichlet noise *)
  val gamma_distrib : real -> (real * real) list
  val dirichlet_noise : real -> int -> real list

  (* search function *)
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
  type ('a,'b) guider = 'a -> real * ('b * real) list
  val uniform_guider : ('a,'b) gamespec -> ('a,'b) guider
  
  type ('a,'b) mcts_param =
    {
    nsim : int, stopatwin_flag : bool, decay : real, explo_coeff : real,
    noise_flag : bool, noise_coeff : real, noise_alpha : real,
    gamespec : ('a,'b) gamespec,
    guider : ('a,'b) guider
    }
  val starttree_of : ('a,'b) mcts_param -> 'a -> ('a,'b) tree
  val mcts : ('a,'b) mcts_param -> ('a,'b) tree -> ('a,'b) tree

  (* statistics *)
  val mostexplored_path : ('a,'b) tree -> id -> id list
  val max_depth : ('a,'b) tree -> id -> int
  val trace_win : ('a -> status) -> ('a,'b) tree -> id -> ('a,'b) node list

  (* toy example *)
  type toy_board = (int * int)
  datatype toy_move = Incr | Decr
  val toy_gamespec : (toy_board,toy_move) gamespec

end
