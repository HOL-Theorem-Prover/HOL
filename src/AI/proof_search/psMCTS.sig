signature psMCTS =
sig

  include Abbrev

  (* outcome *)
  datatype status = Undecided | Win | Lose

  (* search tree: 'a is a board position, 'b is a move *)
  type id = int list
  val id_compare : id * id -> order
  type 'b pol = (('b * real) * id) list
  type ('a,'b) node =
    {
    pol : 'b pol,
    value : real,
    board : 'a,
    sum : real,
    vis : real,
    status : status
    }
  type ('a,'b) tree = (id, ('a,'b) node) Redblackmap.dict

  (* dirichlet noise *)
  val gamma_distrib : real -> (real * real) list
  val gamma_noise_gen : real -> (unit -> real)

  (* search function *)
  type ('a,'b) game =
    {
    status_of : 'a -> status, 
    apply_move : 'b -> 'a -> 'a,
    available_movel : 'a -> 'b list,
    string_of_board : 'a -> string,
    string_of_move : 'b -> string
    }

  type ('a,'b) player = 'a -> real * ('b * real) list
  val uniform_player : ('a,'b) game -> ('a,'b) player
  val random_player : ('a,'b) game -> ('a,'b) player

  type mctsparam =
    {
    nsim : int,
    stopatwin_flag : bool,
    decay : real,
    explo_coeff : real,
    noise_root : bool,
    noise_all : bool,
    noise_coeff : real,
    noise_gen : unit -> real
    }

  type ('a,'b) mctsobj =
    {
    mctsparam : mctsparam,
    game : ('a,'b) game,
    player : ('a,'b) player
    }

  val starttree_of : ('a,'b) mctsobj -> 'a -> ('a,'b) tree
  val mcts : ('a,'b) mctsobj -> ('a,'b) tree -> ('a,'b) tree

  (* statistics *)
  val mostexplored_path : ('a,'b) tree -> id -> id list
  val max_depth : ('a,'b) tree -> id -> int
  val trace_win : ('a -> status) -> ('a,'b) tree -> id -> ('a,'b) node list

  (* toy example *)
  type toy_board = (int * int * int)
  datatype toy_move = Incr | Decr
  val toy_game : (toy_board,toy_move) game

end
