signature mleSynthesize =
sig

  include Abbrev

  type board = (term * term)
  type move = (term * int)

  type gamespec =
    {
    nntm_of_sit: board psMCTS.sit -> term,
    movel: move list,
    status_of : (board psMCTS.sit -> psMCTS.status),
    filter_sit : board psMCTS.sit -> ((move * real) list -> (move * real) list),
    apply_move : (move -> board psMCTS.sit -> board psMCTS.sit),
    operl : (term * int) list,
    mk_targetl: int -> int -> board psMCTS.sit list,
    write_targetl: board psMCTS.sit list -> unit,
    read_targetl: unit -> board psMCTS.sit list,
    string_of_move : move -> string
    }

  val gamespec : gamespec

end
