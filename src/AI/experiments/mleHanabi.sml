(* ========================================================================= *)
(* FILE          : mleHanabi.sml                                             *)
(* DESCRIPTION   : Hanabi card game                                          *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mleHanabi :> mleHanabi =
struct

open HolKernel boolLib Abbrev aiLib smlParallel
  mlNeuralNetwork mlTreeNeuralNetwork psMCTS mlReinforce

val ERR = mk_HOL_ERR "mleHanabi"

(* -------------------------------------------------------------------------
   Deck
   ------------------------------------------------------------------------- *)

datatype color = Red | Yellow | Green | Blue | White | NoColor
val colorl = [Red,Yellow,Green,Blue,White]
val colorl_ext = NoColor :: colorl
val numberl = [1,2,3,4,5]
val numberl_ext = [0,1,2,3,4,5]

type card = int * color

val nocard = (0,NoColor)

fun string_of_color c = case c of
    Red => "r"
  | White => "w"
  | Blue => "b"
  | Yellow => "y"
  | Green => "g"
  | NoColor => "_"

fun color_of_char c = case c of
    #"r" => Red
  | #"w" => White
  | #"b" => Blue
  | #"y" => Yellow
  | #"g" => Green
  | #"_" => NoColor
  | _ => raise ERR "color_of_char" ""

fun string_of_card (n,c) = its n ^ string_of_color c

fun compare_card (card1,card2) =
  String.compare (string_of_card card1, string_of_card card2)

fun card_of_string s =
  (string_to_int (Char.toString (String.sub (s,0))) ,
   color_of_char (String.sub (s,1)))

val full_deck =
  List.concat (map (fn x => [(1,x),(1,x),(1,x)]) colorl) @
  List.concat (map (fn x => [(2,x),(2,x)]) colorl)

val cardl_ext = 
  List.concat (map (fn x => [(1,x)]) colorl) @
  List.concat (map (fn x => [(2,x)]) colorl) @ [nocard]

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

datatype move =
    Play of int
  | Discard of int
  | ColorClue of color
  | NumberClue of int

fun string_of_move move = case move of
    Play i => "P" ^ its i
  | Discard i => "D" ^ its i
  | ColorClue c => "C" ^ string_of_color c
  | NumberClue n => "N" ^ its n

val positionl = [0,1,2,3,4]

val movel =
  map Play positionl @ map Discard positionl @
  map ColorClue colorl @ map NumberClue numberl

fun compare_move (m1,m2) =
  String.compare (string_of_move m1, string_of_move m2)

type board =
  {
  p1turn : bool,
  lastmove1 : move option, lastmove2: move option,
  hand1 : card vector, hand2 : card vector,
  clues1 : card vector, clues2 : card vector,
  clues : int, score : int, bombs : int,
  deck : card list, disc : card list, pile : card vector
  }

fun string_of_p1turn p1turn = if p1turn then "Player1" else "Player2"

fun string_of_hand hand =
  String.concatWith " " (map string_of_card (vector_to_list hand))

fun hand_of_string s =
  Vector.fromList (map card_of_string (String.tokens Char.isSpace s))

fun nice_of_board {p1turn,lastmove1,lastmove2,hand1,hand2,clues1,clues2,
  clues,score,bombs,deck,disc,pile} =
  String.concatWith "\n  "
  [string_of_p1turn p1turn,
   String.concatWith " " (map its [score,clues,bombs,length deck]),
   "", string_of_hand hand1, string_of_hand clues1,
   "", string_of_hand hand2, string_of_hand clues2,
   "", String.concatWith " " (map string_of_card disc),
   "", string_of_hand pile,
   ""]

val nohand = Vector.fromList (List.tabulate (5, fn _ => nocard))

fun random_startboard () =
  let
    val d1 = shuffle full_deck
    val (v1,d2) = part_n 5 d1
    val (v2,d3) = part_n 5 d2
  in
    {
    p1turn = true,
    lastmove1 = NONE, lastmove2 = NONE,
    hand1 = Vector.fromList v1, hand2 = Vector.fromList v2,
    clues1 = nohand,
    clues2 = nohand,
    clues = 8, score = 0, bombs = 0,
    deck = d3 @ [nocard,nocard],
    disc = [],
    pile = Vector.fromList (map (fn x => (0,x)) colorl)
    }
  end

(* -------------------------------------------------------------------------
   Compute distrib
   ------------------------------------------------------------------------- *)

type obsc = (move option * card * int)
type obs = card * int
type obsc_dict = (obsc, (card,int) Redblackmap.dict) Redblackmap.dict
type obs_dict = (obs, (card,int) Redblackmap.dict) Redblackmap.dict
type nn = mlNeuralNetwork.nn

fun obsc_card {p1turn,lastmove1,lastmove2,hand1,hand2,clues1,clues2,
  clues,score,bombs,deck,disc,pile} pos = 
  let 
    val moveo = if p1turn then lastmove2 else lastmove1
    val clue = Vector.sub (if p1turn then clues1 else clues2, pos) 
    val card = Vector.sub (if p1turn then hand1 else hand2, pos) 
  in
    ((moveo,clue,pos),card)
  end

fun drop_moveo ((moveo,clue,pos),card) = ((clue,pos),card)

fun observe_hand (board:board) = 
  let val l = map (obsc_card board) positionl in
    (l, map drop_moveo l)
  end

fun partial_compare cmp (a,b) = case (a,b) of
    (NONE,NONE) => EQUAL
  | (NONE,_) => LESS
  | (_,NONE) => GREATER
  | (SOME a', SOME b') => cmp (a',b')

fun triple_compare (cmp1,cmp2,cmp3) ((a1,a2,a3),(b1,b2,b3)) =
  cpl_compare (cpl_compare cmp1 cmp2) cmp3 (((a1,a2),a3),((b1,b2),b3))

val compare_obsc =
   triple_compare
   (partial_compare compare_move, compare_card, Int.compare)

val compare_obs = cpl_compare compare_card Int.compare

val empty_guess = dempty compare_card

fun update_d ((k,card),d) =
  let 
    val oldguess = dfind k d handle NotFound => empty_guess
    val freq = dfind card oldguess handle NotFound => 0
    val newguess = dadd card (freq + 1) oldguess
  in
    dadd k newguess d
  end

fun dis_from_guess d = 
  let fun f card = Real.fromInt (dfind card d) handle NotFound => 0.0 in
    map_assoc f cardl_ext
  end

fun proba_from_dis dis =
  let val tot = sum_real (map snd dis) in
    if tot > 0.000001 
    then map_snd (fn x => x / tot) dis
    else raise ERR "proba_from_dis" ""
  end
 
fun proba_from_guess d = proba_from_dis (dis_from_guess d)

fun update_observable (board,(d1,d2)) =
  let val (l1,l2) = observe_hand board in
    (foldl update_d d1 l1, foldl update_d d2 l2)  
  end

(* -------------------------------------------------------------------------
   Representation of board as onehot encoding
   ------------------------------------------------------------------------- *)

fun onehot (k,n) =
  let fun f i = if i = k then 1.0 else ~1.0 in List.tabulate (n,f) end

fun oh_color c =  onehot (assoc c (number_snd 0 colorl_ext), length colorl_ext)
fun oh_number i = onehot (i,length numberl_ext)
fun oh_card (i,c) = oh_number i @ oh_color c
fun oh_hand v = List.concat (map oh_card (vector_to_list v))


fun obs_of_board {p1turn,lastmove1,lastmove2,hand1,hand2,clues1,clues2,
  clues,score,bombs,deck,disc,pile} pos = 
  let 
    val moveo = if p1turn then lastmove2 else lastmove1
    val clue = Vector.sub (if p1turn then clues1 else clues2, pos) 
    val card = Vector.sub (if p1turn then hand1 else hand2, pos) 
  in
    (moveo,clue,pos)
  end

fun norm l = map (fn x => x * 2.0 - 1.0) l
fun denorm v = map (fn x => (x + 1.0) * 0.5) (vector_to_list v)

fun card_match clue card =
  (fst clue = fst card orelse fst clue = 0) andalso
  (snd clue = snd card orelse snd clue = NoColor)

fun uniform_guess clue = 
  dnew compare_card (map_assoc (fn x => if card_match clue x then 1 else 0) cardl_ext)

fun stats_pos (d1,d2) board pos =
  let
    val (moveo,clue,pos) = obs_of_board board pos
    val guess1 = dfind (moveo,clue,pos) d1 
      handle NotFound => uniform_guess clue
    val dis1 = proba_from_guess guess1
    val guess2 = dfind (clue,pos) d2
      handle NotFound => uniform_guess clue
    val dis2 = proba_from_guess guess2
  in
    norm (map snd dis1) @ norm (map snd dis2)
  end

fun all_stats (d1,d2) board = 
  List.concat (map (stats_pos (d1,d2) board) positionl)


fun oh_board (d1,d2) 
  (board as {p1turn,lastmove1,lastmove2,hand1,hand2,clues1,clues2,clues,
  score,bombs,deck,disc,pile}) =
  let 
    val stats = all_stats (d1,d2) board
    val t1 = if p1turn then clues1 else clues2
    val t2 = if p1turn then clues2 else clues1
    val hand = if p1turn then hand2 else hand1
    val lastmove = if p1turn then lastmove2 else lastmove1
  in
    Vector.fromList 
    (List.concat [stats, oh_hand t1, oh_hand t2, oh_hand hand, oh_hand pile])
  end

(* 
load "mleHanabi"; open mleHanabi;
load "aiLib"; open aiLib;
val board = random_startboard ();
val oh = oh_board (dempty compare_obsc, dempty compare_obs) board;
*)

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

fun draw_card i card hand =
  let
    val dummy = (~1,NoColor)
    val l1 = vector_to_list (Vector.update (hand,i,dummy))
    val l2 = filter (fn x => x <> dummy) l1
  in
    Vector.fromList (card :: l2)
  end

(* -------------------------------------------------------------------------
   Play
   ------------------------------------------------------------------------- *)

fun is_playable card pile =
  let fun test c = if snd card = snd c then fst card = fst c + 1 else true in
    card <> nocard andalso Vector.all test pile
  end

fun update_pile card pile =
  let fun f c = if snd card = snd c then card else c in
    Vector.map f pile
  end

fun apply_move_play move i
  {p1turn,lastmove1,lastmove2,hand1,hand2,clues1,clues2,
   clues,score,bombs,deck,disc,pile} =
  let
    val newcard = hd deck
    val hand = if p1turn then hand1 else hand2
    val cluev = if p1turn then clues1 else clues2
    val played = Vector.sub (hand,i)
    val playb = is_playable played pile
  in
    {
    p1turn = not p1turn,
    lastmove1 = if p1turn then SOME move else lastmove1,
    lastmove2 = if not p1turn then SOME move else lastmove2,
    hand1 =  if p1turn then draw_card i newcard hand1  else hand1,
    hand2 =  if not p1turn then draw_card i newcard hand2 else hand2,
    clues1 = if p1turn then draw_card i nocard clues1 else clues1,
    clues2 = if not p1turn then draw_card i nocard clues2 else clues2,
    clues = clues,
    score = if playb then score + 1 else score,
    bombs = if not playb then bombs + 1 else bombs,
    deck = tl deck,
    disc = if not playb then played :: disc else disc,
    pile = if playb then update_pile played pile else pile
    }
  end

(* -------------------------------------------------------------------------
   Discard
   ------------------------------------------------------------------------- *)

fun apply_move_discard move i     
  {p1turn,lastmove1,lastmove2,hand1,hand2,clues1,clues2,
  clues,score,bombs,deck,disc,pile} =
  let
    val newcard = hd deck handle Empty => nocard
    val hand = if p1turn then hand1 else hand2
    val discarded = Vector.sub (hand,i)
  in
    {
    p1turn = not p1turn,
    lastmove1 = if p1turn then SOME move else lastmove1,
    lastmove2 = if not p1turn then SOME move else lastmove2,
    hand1 =  if p1turn then draw_card i newcard hand1 else hand1,
    hand2 =  if not p1turn then draw_card i newcard hand2 else hand2,
    clues1 = if p1turn then draw_card i nocard clues1 else clues1,
    clues2 = if not p1turn then draw_card i nocard clues2 else clues2,
    clues = if clues < 8 then clues + 1 else clues,
    score = score,
    bombs = bombs,
    deck = tl deck,
    disc = discarded :: disc,
    pile = pile
    }
  end

(* -------------------------------------------------------------------------
   Clue
   ------------------------------------------------------------------------- *)

fun update_color color (handv,cluev) =
  let
    val l = combine (vector_to_list handv, vector_to_list cluev)
    fun f ((n1,c1),(n2,c2)) = if c1 = color then (n2,c1) else (n2,c2)
  in
    Vector.fromList (map f l)
  end

fun update_number number (handv,cluev) =
  let
    val l = combine (vector_to_list handv, vector_to_list cluev)
    fun f ((n1,c1),(n2,c2)) = if n1 = number then (n1,c2) else (n2,c2)
  in
    Vector.fromList (map f l)
  end

fun apply_move_clue move f 
  {p1turn,lastmove1,lastmove2,hand1,hand2,clues1,clues2,
  clues,score,bombs,deck,disc,pile} =
  {
  p1turn = not p1turn,
  lastmove1 = if p1turn then SOME move else lastmove1,
  lastmove2 = if not p1turn then SOME move else lastmove2,
  hand1 = hand1, hand2 = hand2,
  clues1 = if not p1turn then f (hand1,clues1) else clues1,
  clues2 = if p1turn then f (hand2,clues2) else clues2,
  clues = if clues > 0 then clues - 1 else raise ERR "apply_move_clue" "",
  score = score, bombs = bombs,
  deck = deck, disc = disc, pile = pile
  }

(* -------------------------------------------------------------------------
   Apply move
   ------------------------------------------------------------------------- *)

fun apply_move move board = case move of
    Play i => apply_move_play move i board
  | Discard i => apply_move_discard move i board
  | ColorClue c => apply_move_clue move (update_color c) board
  | NumberClue n => apply_move_clue move (update_number n) board

fun is_applicable board move = case move of
    ColorClue _ => #clues board > 0
  | NumberClue _ => #clues board > 0
  | _ => true

(* -------------------------------------------------------------------------
   Play game (filter examples that are all zero ar all ones.
   ------------------------------------------------------------------------- *)

fun best_move (d1,d2) nn board =
  let
    val dis1 = combine (movel, denorm (infer_nn nn (oh_board (d1,d2) board)))
    val dis2 = filter (fn (x,_) => is_applicable board x) dis1
  in
    select_in_distrib dis2
  end

(* does not match the rules exactly *)
fun is_endboard board = null (#deck board) orelse (#bombs board >= 3)

fun play_game (d1,d2) nn board =
  if is_endboard board
  then #score board
  else play_game (d1,d2) nn (apply_move (best_move (d1,d2) nn board) board)

fun play_ngame (d1,d2) nn ngame =
  let
    val boardl = List.tabulate (ngame, fn _ => random_startboard ())
    val l = map (play_game (d1,d2) nn) boardl
  in
    average_real (map Real.fromInt l)
  end

(* -------------------------------------------------------------------------
   Evaluation
   ------------------------------------------------------------------------- *)

fun helper (k,n) =
  let fun f i = if i = k then 1.0 else 0.0 in List.tabulate (n,f) end

fun proba_from_reall l = 
  let val tot = sum_real l in map (fn x => x / tot) l end

fun eval_board (d1,d2) nn board =
  if is_endboard board 
  then helper (#score board,10)
  else proba_from_reall ((denorm o infer_nn nn o oh_board (d1,d2)) board)

fun expectancy l =
  let fun f i x = Real.fromInt i * x in sum_real (mapi f l) end

(* -------------------------------------------------------------------------
   Guesses on current player hand dependent on observables
   ------------------------------------------------------------------------- *)

fun guess_card d1 board pos =
  let
    val (moveo,clue,pos) = obs_of_board board pos
    val guess = dfind (moveo,clue,pos) d1 
      handle NotFound => uniform_guess clue
    val dis = dis_from_guess guess
  in
    select_in_distrib dis  
  end

fun guess_board d1 (board as 
  {p1turn,lastmove1,lastmove2,hand1,hand2,clues1,clues2,
  clues,score,bombs,deck,disc,pile}) =
  let val hand = Vector.fromList (map (guess_card d1 board) positionl) in
    {
    p1turn = p1turn,
    lastmove1 = lastmove1,
    lastmove2 = lastmove2,
    hand1 = if p1turn then hand else hand1, 
    hand2 = if not p1turn then hand else hand2,
    clues1 = clues1,
    clues2 = clues2,
    clues = clues, score = score, bombs = bombs,
    deck = deck, disc = disc, pile = pile
    }
  end

(* -------------------------------------------------------------------------
   Depth-limited lookahead for improved policy and eval.
   Value of a choice in a policy according to PCUT formula.
   ------------------------------------------------------------------------- *)

fun value_choice vtot (move,(polv,sum,vis)) =
  let
    val exploitation = sum / (vis + 1.0)
    val exploration  = (polv * Math.sqrt vtot) / (vis + 1.0)
  in
    exploitation + (!exploration_coeff) * exploration
  end

fun select_in_polext board vtot polext =
  let 
    val dis1 = map (fn x => (fst x, value_choice vtot x)) (dlist polext) 
    val dis2 = filter (fn (x,_) => is_applicable board x) dis1
  in
    select_in_distrib dis2
  end

fun lookahead_once move (d1,d2) nneval board =
  let 
    val board1 = guess_board d1 board  
    val board2 = apply_move move board1 
  in
    eval_board (d1,d2) nneval board2
  end

fun lookahead_loop nsim (d1,d2) (nneval,nnpoli) board 
  (sumtot,vtot) polext rewarddisl =
  if nsim <= 0 then ((sumtot,vtot),polext,rewarddisl) else
  let 
    val move = select_in_polext board vtot polext
    val rewarddis = lookahead_once move (d1,d2) nneval board 
    val reward = expectancy rewarddis
    val (polv,sum,vis) = dfind move polext
    val newpolext = dadd move (polv, sum + reward, vis + 1.0) polext
  in
    lookahead_loop (nsim - 1) (d1,d2) (nneval,nnpoli) board 
    (sumtot + reward, vtot + 1.0) newpolext (rewarddis :: rewarddisl)
  end

fun lookahead_aux nsim (d1,d2) (nneval,nnpoli) board =
  let 
    val (sumtot,vtot) = (expectancy (eval_board (d1,d2) nneval board), 1.0)
    val pol = combine (movel,
      denorm (infer_nn nnpoli (oh_board (d1,d2) board)))
    val polext = dnew compare_move (map (fn (a,b) => (a,(b,0.0,0.0))) pol)
  in
    lookahead_loop nsim (d1,d2) (nneval,nnpoli) board (sumtot,vtot) polext []
  end

(* -------------------------------------------------------------------------
   Extract eval example
   ------------------------------------------------------------------------- *)

fun merge_rewarddisl rewarddisl = map sum_real (list_combine rewarddisl)

fun extract_evalex (d1,d2) board rewarddisl =
  let
    val input = oh_board (d1,d2) board
    val rewarddis = merge_rewarddisl rewarddisl
    val evalout = Vector.fromList (norm rewarddis)
  in
    (input,evalout)
  end

(* -------------------------------------------------------------------------
   Extract poli example
   ------------------------------------------------------------------------- *)

fun proba_from_reall l = 
  let val tot = sum_real l in map (fn x => x / tot) l end

fun extract_poliex (d1,d2) board polext =
  let
    val input = oh_board (d1,d2) board
    fun f (_,(_,_,x)) = x
  in
    (input, Vector.fromList (norm (proba_from_reall (map f (dlist polext)))))
  end

fun lookahead nsim (d1,d2) (nneval,nnpoli) board =
  let 
    val (_,polext,rewarddisl) =
      lookahead_aux nsim (d1,d2) (nneval,nnpoli) board
  in
    (extract_evalex (d1,d2) board rewarddisl,
     extract_poliex (d1,d2) board polext)
  end

(* -------------------------------------------------------------------------
   Reinforcement learning loop
   ------------------------------------------------------------------------- *)

fun rl_start () =
  let
    val obs = (dempty compare_obsc, dempty compare_obs)
    val nneval = random_nn (tanh,dtanh) [350,350,10]
    val nnpoli = random_nn (tanh,dtanh) [350,350,20]
  in
    print_endline "rl_start";
    ((nneval,nnpoli), obs, random_startboard (), [])
  end

val summaryfile = HOLDIR ^ "/src/AI/experiments/hanabi"

fun summary s = (print_endline s; append_endline summaryfile s)

fun rl_loop_once ((nne,nnp),obs,board,scl) =
  let
    val newobs = update_observable (board,obs)
    val nsim = 1600
    val (evalex,poliex) = lookahead nsim obs (nne,nnp) board
    val (newnne,_) = train_nn_batch 1 nne [evalex]
    val (newnnp,_) = train_nn_batch 1 nnp [poliex]
    val move = best_move obs nnp board
    val board1 = apply_move move board 
    val _ = print_endline 
      (string_of_move move ^ "-" ^ its (#score board1) ^ " ")
    val board2 = if is_endboard board1 then random_startboard () else board1
    val newscl = if is_endboard board1 
                 then first_n 100 (#score board1 :: scl) 
                 else scl
    val _ = 
      if is_endboard board1 
      then summary ("Moving average: " ^ 
           (rts (average_real (map Real.fromInt newscl))))
      else ()
  in
    ((newnne,newnnp),newobs,board2,newscl)
  end

fun rl_loop n = 
  let val _ = erase_file summaryfile in
    funpow n rl_loop_once (rl_start ())
  end
  
(*
load "mleHanabi"; open mleHanabi;
load "mlNeuralNetwork"; open mlNeuralNetwork;
load "aiLib"; open aiLib;
val r = rl_loop (1000 * 1000);
*)



end (* struct *)
