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
    dim : int,
    nntm_of_sit: board psMCTS.sit -> term
    }

  val gamespec : gamespec
  val targetl_n4 : board psMCTS.sit list

end
