signature mleHanabi =
sig
  
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
  val operl : (term * int) list
  val nntm_of_board : board -> term
  val nntm_of_move : move -> term
  val nntm_of_boardmove : (board * move) -> term
  val random_game : unit -> ((board * move) list * int)
  val tnn_game : mlTreeNeuralNetwork.tnn -> ((board * move) list * int)
  val extract_ex : ((board * move) list * int) -> (term * real list) list
  val rl_loop : int -> mlTreeNeuralNetwork.tnn

end
