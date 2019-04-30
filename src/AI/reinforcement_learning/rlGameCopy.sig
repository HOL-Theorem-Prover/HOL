signature rlGameCopy =
sig

  include Abbrev

  type board = (term * term)
  type move = (term * int)

  type gamespec =
    {
    mk_startsit: term -> board psMCTS.sit,
    nntm_of_sit: board psMCTS.sit -> term,
    movel: move list,
    status_of : (board psMCTS.sit -> psMCTS.status),
    apply_move : (move -> board psMCTS.sit -> board psMCTS.sit),
    operl : (term * int) list,
    mk_targetl: int -> int -> term list
    }

  val gamespec : gamespec

end
