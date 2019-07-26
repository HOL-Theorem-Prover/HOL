signature mleHanabi =
sig

  include Abbrev

  datatype color = Red | Yellow | Green | Blue | White | NoColor
  type card = int * color

  datatype move =
    Play of int
  | Discard of int
  | ColorClue of color
  | NumberClue of int

  type board =
    {
    objective : int,
    p1turn : bool,
    hand1 : card vector, hand2 : card vector,
    clues1 : card vector, clues2 : card vector,
    clues : int, score : int, bombs : int,
    deck : card list, disc : card list, pile : card vector
    }

  val random_startboard : int -> board

  val gamespec : (board,move) mlReinforce.gamespec
  val extspec : board mlReinforce.extgamespec

  val play_game : mlTreeNeuralNetwork.tnn -> board -> int
  val explore : mlTreeNeuralNetwork.tnn -> board -> (term * real list) list
  val explore_extspec :
    (mlTreeNeuralNetwork.tnn, board, (term * real list) list) smlParallel.extspec
  val collect :
    int -> mlTreeNeuralNetwork.tnn -> int -> (term * real list) list
  val play_ngame : mlTreeNeuralNetwork.tnn -> int -> real

end
