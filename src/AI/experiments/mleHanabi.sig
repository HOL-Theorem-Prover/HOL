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

  val compare_move : (move * move) -> order
 
  type obsc = move option * card * int
  type obs = card * int
  type obsc_dict = (obsc, (card,int) Redblackmap.dict) Redblackmap.dict
  type obs_dict = (obs, (card,int) Redblackmap.dict) Redblackmap.dict
  type nn = mlNeuralNetwork.nn
   
  type board =
    {
    p1turn : bool,
    lastmove1 : move option, lastmove2: move option,
    hand1 : card vector, hand2 : card vector,
    clues1 : card vector, clues2 : card vector,
    clues : int, score : int, bombs : int,
    deck : card list, disc : card list, pile : card vector
    }
   
  val hanabi_dir : string
  val summary_file : string ref
  val player_mem : ((obsc_dict * obs_dict) * (nn * nn)) ref

  (* encoding *)
  val compare_card : (card * card) -> order
  val random_startboard : unit -> board
  val oh_board : (obsc_dict * obs_dict) -> board -> real vector
  
  (* observables *)
  val compare_obsc : (obsc * obsc) -> order
  val compare_obs : (obs * obs) -> order  
  val observe_hand : board -> (obsc * card) list * (obs * card) list
  val update_observable : 
    (board  * (obsc_dict * obs_dict)) -> (obsc_dict * obs_dict)
  val empty_obs : (obsc_dict * obs_dict)
  val print_obs : (obsc_dict * obs_dict) -> board -> int -> unit

  (* guesses *)
  val guess_board : obsc_dict -> board -> board
  
  (* lookahead *)
  val lookahead : int -> (obsc_dict * obs_dict) -> (nn * nn) -> board ->
    move * (real vector * real vector) * (real vector * real vector)

  (* playing a game *)    
  val best_move : (obsc_dict * obs_dict) -> nn -> board -> move
  val play_game : (obsc_dict * obs_dict) -> nn -> board -> int
  val play_ngame : (obsc_dict * obs_dict) -> nn -> int -> real

  (* statistics *)
  val stats_player : int -> (obsc_dict * obs_dict) * (nn * nn) -> unit
  val symdiff_player : int -> 
    (obsc_dict * obs_dict) * (nn * nn) -> 
    (obsc_dict * obs_dict) * (nn * nn) -> unit
  (* reinforcement learning *)
  val rl_loop : int -> 
    ((nn * nn) * (obsc_dict * obs_dict) * board * int list)



end
