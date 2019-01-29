signature rlGameParamod =
sig

  include Abbrev

  type pos = int list
  type pb = ((term * bool) * pos) list
  datatype board = Board of pb | FailBoard

  datatype move = Down | Left | Right | Rotate | ParamodL | ParamodR

  type gamespec =
    {
    mk_startsit: pb -> board psMCTS.sit,
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
