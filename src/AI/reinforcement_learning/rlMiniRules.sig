signature rlMiniRules =
sig

  include Abbrev

  (* helpers *)
  val is_refl : term -> bool
  val sub_tac : (term * int list) -> term -> term

  (* board *)
  datatype board =
    StopBoard of (term * int list) |
    LrBoard of (term * int list) |
    SubBoard of (term * int list)

  type situation = bool * board
  val nntm_of_sit : situation -> term

  (* moves *)
  datatype stopchoice = Stop | Cont
  val move_stop : stopchoice -> situation -> situation
  val all_stopchoice : stopchoice list

  datatype lrchoice = Left | Right
  val all_lrchoice : lrchoice list
  val move_lr : lrchoice -> situation -> situation

  datatype subchoice =
    AddZero | MultZero | AddReduce | MultReduce | AddExpand | MultExpand |
    AddZeroExpand
  val all_subchoice : subchoice list
  val move_sub : subchoice -> situation -> situation

  (* all moves *)
  datatype move =
    StopMove of stopchoice | LrMove of lrchoice | SubMove of subchoice
  val apply_move : move -> situation -> situation
  val string_of_move : move -> string

end
