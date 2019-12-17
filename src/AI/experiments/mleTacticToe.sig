signature mleTacticToe =
sig

  include Abbrev
  
  type board = (goal list * goal list) * term * (int * int)
  type move = term
  
  val delsimps : string list
  val ttt_empty : term
  val string_of_goall : goal list -> string 
  val mk_startboard : (goal list * goal list) -> board
  val dest_startboard : board -> (goal list * goal list)
  val game : (board,move) psMCTS.game
  val nntm_of_board : board -> term
  val test_one : int -> (string * real * goal * goal list) -> bool

end
