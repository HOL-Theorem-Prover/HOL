signature rlGameRewrite =
sig

  include Abbrev

  type pos = int list

  datatype board = Board of (term * pos) | FailBoard

  datatype move =
    Down | Left | Right |
    AddZero | MultZero | AddReduce | MultReduce | AddExpand | MultExpand |
    AddZeroExpand

  type gamespec =
    {
    mk_startsit: term -> board psMCTS.sit,
    nntm_of_sit: board psMCTS.sit -> term,
    movel: move list,
    status_of : (board psMCTS.sit -> psMCTS.status),
    apply_move : (move -> board psMCTS.sit -> board psMCTS.sit),
    operl : (term * int) list,
    dim : int
    }

  val gamespec : gamespec

  val mk_targetl : int -> int -> board psMCTS.sit list

end
