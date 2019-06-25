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
  type program = move list

  type state = (int,int) Redblackmap.dict
  type board = (int list * int) * (state list * program) * (program * program)
  
  val gamespec : (board,move) mlReinforce.gamespec

  val mk_startsit : int list * (program * int) -> (bool * board)
  val inputl_org : int list list
  val statel_org : state list
  val state_of_inputl : int list -> state

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
