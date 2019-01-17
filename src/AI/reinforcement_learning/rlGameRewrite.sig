signature rlGameRewrite =
sig

  include Abbrev

  (* board *)
  datatype board =
    StopBoard of (term * int list) |
    LrBoard of (term * int list) |
    SubBoard of (term * int list) |
    FailBoard

  type sit = bool * board
  val nntm_of_sit : sit -> term

  (* moves *)
  datatype stopchoice = Stop | Cont
  val move_stop : stopchoice -> sit -> sit
  val all_stopchoice : stopchoice list

  datatype lrchoice = Left | Right
  val all_lrchoice : lrchoice list
  val move_lr : lrchoice -> sit -> sit

  datatype subchoice =
    AddZero | MultZero | AddReduce | MultReduce | AddExpand | MultExpand |
    AddZeroExpand
  val all_subchoice : subchoice list
  val move_sub : subchoice -> sit -> sit

  (* all moves *)
  datatype move =
    StopMove of stopchoice | LrMove of lrchoice | SubMove of subchoice
  val apply_move : move -> situation -> situation
  val string_of_move : move -> string

end
