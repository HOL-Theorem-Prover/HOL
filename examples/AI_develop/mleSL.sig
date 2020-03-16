signature mleSL =
sig

  include Abbrev
  

  type board = mlTreeNeuralNetwork.tnn * (real * int) list 
  datatype move = Incr | Decr | Still

  val boardstart : board
  val game : (board,move) psMCTS.game
  val loss_player : (board,move) psMCTS.player

end
