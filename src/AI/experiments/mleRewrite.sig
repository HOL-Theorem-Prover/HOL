signature rlGameArithGround =
sig

  include Abbrev

  type pos = int list
  type pb = (term * pos)
  datatype board = Board of pb | FailBoard
  datatype move = Arg of int | Paramod of (int * bool)
  type gamespec =
    {
    filter_sit : board psMCTS.sit -> ((move * real) list -> (move * real) list),
    movel : move list,
    string_of_move : move -> string,
    status_of : (board psMCTS.sit -> psMCTS.status),
    apply_move : (move -> board psMCTS.sit -> board psMCTS.sit),
    operl : (term * int) list,
    nntm_of_sit: board psMCTS.sit -> term
    }
  val gamespec : gamespec

  val mk_pretargetl : int -> term list
  val mk_targetl : int -> board psMCTS.sit list 
  val total_cost_target : board psMCTS.sit -> int

  val mk_startsit : term -> board psMCTS.sit
  val dest_startsit : board psMCTS.sit -> term

end
