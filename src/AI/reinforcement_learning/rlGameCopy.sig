signature rlGameCopy =
sig

  include Abbrev

  type pos = int list

  datatype board = Board of (term * (term * pos)) | FailBoard

  datatype move =
    Down | Left | Right |
    Sz | Sal | Sar | Sss |
    Asa | Asl | Asr | Aac | Aasl | Aasr

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

end
