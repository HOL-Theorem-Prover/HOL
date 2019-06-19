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

  val level_parameters : (int * int * int * int) list
  val random_prog : (int * int * int * int) -> program
  val gen_olsizel : int -> (int list * int) list
  val rand_olsize : int -> (int list * int)

  val explore_dhtnn : mlTreeNeuralNetwork.dhtnn -> 
    (int list * int) -> (board, move) psMCTS.node list
  val explore_random :
    (int list * int) -> (board, move) psMCTS.node list
  val extract_prog :
    (board, move) psMCTS.node list -> program

end
