signature rlGameAim =
sig

  include Abbrev

  val read_thml : string -> term list
  val read_axl : string -> term list


  type pos = int list
  type pb = ((term * pos) * int option)
  datatype board = Board of pb | FailBoard
  datatype move = ChooseAx of int | Arg0 | Arg1 | Arg2 | ParamodL | ParamodR

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

  val targetl : board psMCTS.sit list
 

end
