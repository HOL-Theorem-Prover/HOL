signature mleProgram =
sig

  include Abbrev

  datatype move =
      Read of int 
    | Write of int
    | Incr of int 
    | Decr of int
    | Cond
    | Loop
    | EndLoop
    | EndCond
    | Macro of int

  type program = move list

  val macro_array : move list option vector ref

  type state = (int,int) Redblackmap.dict
  type board = (int list * int) * (state list * program) * (program * program)
  
  val gamespec : (board,move) mlReinforce.gamespec
  val extspec : board mlReinforce.extgamespec

  val mk_startsit : int list * (program * int) -> (bool * board)
  val inputl_org : int list list
  val statel_org : state list
  val state_of_inputl : int list -> state
  val compare_statel : state list * state list -> order
  val ol_of_statel : state list -> int list
  val compare_ol : int list * int list -> order  

  val level_parameters : (int * int * int * int) list ref
  val exec_prog : program -> state -> state
  val random_prog : (int * int * int * int) -> program
  val gen_olsizel : int -> (int list * (program * int)) list
  val rand_olsize : int -> (int list * (program * int))

  val explore_dhtnn : mlTreeNeuralNetwork.dhtnn -> 
    (int list * (move list * int)) -> (board, move) psMCTS.node list
  val explore_random :
    (int list * (move list * int)) -> (board, move) psMCTS.node list
  val extract_prog :
    (board, move) psMCTS.node -> program
  val mk_ol : (int * int -> int) -> int list

end
