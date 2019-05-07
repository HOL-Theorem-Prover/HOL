signature rlGameBool =
sig

  include Abbrev

  type pb = ((term * bool) list) list

  datatype board = Board of pb | FailBoard

  datatype move = Rotate | Swap | RotateCl | Resolve | Delete

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

  val nntm_of_pb : pb -> term
  val mk_targetl : int -> pb list

end
