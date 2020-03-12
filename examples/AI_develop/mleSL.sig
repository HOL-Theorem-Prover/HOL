signature mleSL =
sig

  include Abbrev

  type board = tnn * (real * int) list 
  datatype move = Incr | Decr | Still

  val game : (board,move) game

end
