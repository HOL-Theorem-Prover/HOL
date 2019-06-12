signature mleProgram =
sig

  include Abbrev

  datatype instruction = 
      Read of int
    | Write of int
    | Incr of int
    | Decr of int
  type program = instruction list
  
  type state = (int,int) Redblackmap.dict

  type board = 
    (int list * int) * 
    ((state list, unit) Redblackmap.dict * state list * program)
  
  datatype move = 
    ReadMove of int | WriteMove of int | 
    IncrMove of int | DecrMove of int


  val gamespec : (board,move) mlReinforce.gamespec

  val gen_olsizel : int -> (int list * int) list

  val explore_gamespec : (int list * int) -> (board, move) psMCTS.node list

end
