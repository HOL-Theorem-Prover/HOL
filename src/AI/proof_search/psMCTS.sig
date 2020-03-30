signature psMCTS =
sig

  include Abbrev

  (* outcome *)
  datatype status = Undecided | Win | Lose
  val is_undecided : status -> bool 
  val is_win : status -> bool
  val is_lose : status -> bool
  val string_of_status : status -> string  

  (* search tree: 'a is a board position, 'b is a move *)
  type id = int list
  val id_compare : id * id -> order
  type 'b pol = (('b * real) * id) list
  type ('a,'b) node =
    {
    board : 'a, pol : 'b pol, value : real, stati : status,
    sum : real, vis : real, status : status
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
    string_of_move : 'b -> string,
    board_compare : 'a * 'a -> order,
    move_compare : 'b * 'b -> order,
    movel : 'b list
    }

  type ('a,'b) player = 'a -> real * ('b * real) list
  val uniform_player : ('a,'b) game -> ('a,'b) player
  val random_player : ('a,'b) game -> ('a,'b) player

  type mctsparam =
    {
    timer : real option,
    nsim : int option,
    stopatwin_flag : bool,
    decay : real,
    explo_coeff : real,
    noise_root : bool,
    noise_all : bool,
    noise_coeff : real,
    noise_gen : unit -> real,
    noconfl : bool,
    avoidlose : bool,
    evalwin : bool
    }

  type ('a,'b) mctsobj =
    {mctsparam : mctsparam, game : ('a,'b) game, player : ('a,'b) player}

  val add_rootnoise : mctsparam -> ('a,'b) tree -> ('a,'b) tree
  val starttree_of : ('a,'b) mctsobj -> 'a ->
    (('a,'b) tree * ('a,id) Redblackmap.dict)
  val mcts : ('a,'b) mctsobj -> (('a,'b) tree * ('a,id) Redblackmap.dict) ->
    (('a,'b) tree * ('a,id) Redblackmap.dict)

  (* statistics *)
  val mostexplored_path : ('a,'b) tree -> id -> id list
  val max_depth : ('a,'b) tree -> id -> int
  val trace_win : ('a,'b) tree -> id -> ('a,'b) node list

  (* toy example *)
  type toy_board = (int * int * int)
  datatype toy_move = Incr | Decr
  val toy_game : (toy_board,toy_move) game

end
