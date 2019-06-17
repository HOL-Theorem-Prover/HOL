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

  type board = (int list * int) * (state list * program) * 
    (program * program * int)
  
  val gamespec : (board,move) mlReinforce.gamespec

  val random_prog : int -> program
  val gen_olsizel : int -> (int list * int) list
  val rand_olsize : int -> (int list * int)

  val explore_gamespec : (int list * int) -> (board, move) psMCTS.node list

end
