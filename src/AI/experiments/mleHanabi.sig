signature mleHanabi =
sig
  
  include Abbrev

  datatype color = Red | Yellow | Green | Blue | White | NoColor
  type card = int * color

  val summary_file : string ref
  val ncore_explore : int ref
  val dim_glob : int ref 
  val ncore_train : int ref
  val bsize_glob : int ref
  val lr_glob : real ref
  val nepoch_glob : int ref
  val ngame_glob : int ref
  val nsim_glob : int ref

  datatype move =
    Play of int
  | Discard of int
  | ColorClue of color
  | NumberClue of int

  type board =
    {
    p1turn : bool,
    hand1 : card vector, hand2 : card vector,
    clues1 : card vector, clues2 : card vector,
    clues : int, score : int, bombs : int,
    deck : card list, disc : card list, pile : card vector
    }

  val random_startboard : unit -> board
  val write_boardll : board list list -> unit
  val read_boardll : unit -> board list list
  val movel_glob : move list
  val nocard : card
  val nohand : card vector
  val has_noclues : board -> bool
  val cardl_ext : card list
  val operl : (term * int) list
  val nntm_of_board : board -> term
  val nntm_of_move : move -> term
  val nntm_of_boardmove : (board * move) -> term
  val tnn_game : mlTreeNeuralNetwork.dhtnn -> ((board * move) list * int)
  val select_hand : ((card * real) list -> card) -> 
    mlTreeNeuralNetwork.tnn list -> board -> card vector
  val accuracy : mlTreeNeuralNetwork.tnn list -> board list -> real
  val rl_loop : int -> mlTreeNeuralNetwork.dhtnn
 
  val dhtnn_file : unit -> string
  val tnnl_file : unit -> string list

  val explore_parallel : 
    mlTreeNeuralNetwork.dhtnn * mlTreeNeuralNetwork.tnn list -> 
    board list list -> (term * real list * real list) list list
  val lookahead : 
    int * mlTreeNeuralNetwork.dhtnn * mlTreeNeuralNetwork.tnn list ->
    board -> term * real list * real list
  val lookahead_boardl :  
    int * mlTreeNeuralNetwork.dhtnn * mlTreeNeuralNetwork.tnn list ->
    int * int -> board list -> unit


end
