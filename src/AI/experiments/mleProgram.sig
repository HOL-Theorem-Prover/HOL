signature mleProgram =
sig

  include Abbrev

  type iol = (int list * int) list

  datatype program =
    Read of (int * program) |
    Write of (int * program) |
    Incr of (int * program) |
    Reset of (int * program) |
    Loop of ((int * program) * program) |
    End |
    Cont

  val compare_iol : iol * iol -> order
  val iol_of_prog : program -> iol
  val gen_prog : int -> program list
  val random_prog : int -> program

  datatype board =
    Board of (iol * int * program) | FailBoard
  datatype move =
    AddrMove | ReadMove | WriteMove | IncrMove | ResetMove | LoopMove | EndMove

  val mk_startsit : ((int list * int) list * int) -> board psMCTS.sit
  val gamespec : (board,move) mlReinforce.gamespec
  val mk_targetl : int -> int -> (bool * board) list

  (* exploration *)
  val explore_gamespec : ((int list * int) list * int) -> unit
  val reinforce_fixed : string ->  int ->
    (term * real list * real list) list * mlTreeNeuralNetwork.dhtnn

end
