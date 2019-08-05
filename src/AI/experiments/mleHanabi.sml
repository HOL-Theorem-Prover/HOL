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
type obsc_dict = (obsc, (card * real) list) Redblackmap.dict
type obs_dict = (obs, (card * real) list) Redblackmap.dict
type nn = mlNeuralNetwork.nn

fun observe_card {p1turn,lastmove1,lastmove2,hand1,hand2,clues1,clues2,
  clues,score,bombs,deck,disc,pile} pos = 
  let 
    val moveo = if p1turn then lastmove2 else lastmove1
    val clue = Vector.sub (if p1turn then clues1 else clues2, pos) 
    val card = Vector.sub (if p1turn then hand1 else hand2, pos) 
  in
    ((moveo,clue,pos),card)
  end

fun observe_hand (board:board) = List.tabulate (5, observe_card board);

fun partial_compare cmp (a,b) = case (a,b) of
    (NONE,NONE) => EQUAL
  | (NONE,_) => LESS
  | (_,NONE) => GREATER
  | (SOME a', SOME b') => cmp (a',b')

fun triple_compare (cmp1,cmp2,cmp3) ((a1,a2,a3),(b1,b2,b3)) =
  cpl_compare (cpl_compare cmp1 cmp2) cmp3 (((a1,a2),a3),((b1,b2),b3))
  

fun mk_proba l = 
  let val tot = sum_int (map snd l) in
    map_snd (fn x => int_div x tot) l
  end

fun mk_carddis cardl = 
  let 
    val d = count_dict (dempty compare_card) cardl 
    fun f x = if dmem x d then dfind x d else 0 
  in
    mk_proba (map_assoc f cardl_ext)
  end

val compare_obsc =
   triple_compare
   (partial_compare compare_move, compare_card, Int.compare)

val compare_obs = cpl_compare compare_card Int.compare

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

fun s23 (a,b,c) = (b,c)

fun mk_proba l = 
  let 
    val tot = sum_int (map snd l) 
    fun f x = int_div x tot
  in
    map_snd f l
  end

fun card_match clue card =
  (fst clue = fst card orelse fst clue = 0) andalso
  (snd clue = snd card orelse snd clue = NoColor)

fun uniform_guess clue = 
  mk_proba (map_assoc (fn x => if card_match clue x then 1 else 0) cardl_ext)

fun stats_pos (d1,d2) board pos =
  let
    val (moveo,clue,pos) = obs_of_board board pos
    val dis1 = dfind (moveo,clue,pos) d1 
      handle NotFound => uniform_guess clue
    val dis2 = dfind (clue,pos) d2
      handle NotFound => uniform_guess clue
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
    val dis2 = filter (fn x => is_applicable board (fst x)) dis1
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

fun eval_board (d1,d2) nn board =
  if is_endboard board 
  then helper (#score board,10)
  else (denorm o infer_nn nn o oh_board (d1,d2)) board

fun expectancy l = 
  let fun f i x = Real.fromInt i * x in sum_real (mapi f l) end

(* -------------------------------------------------------------------------
   Guesses on current player hand
   todo: refine to include more visible information
   ------------------------------------------------------------------------- *)

fun guess_card d1 board pos =
  let
    val (moveo,clue,pos) = obs_of_board board pos
    val dis1 = dfind (moveo,clue,pos) d1 handle NotFound => uniform_guess clue
  in
    select_in_distrib dis1    
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
   Depth-limited lookahead for improved policy and eval
   ------------------------------------------------------------------------- *)

fun value_choice vtot (move,(polv,sum,vis)) =
  let
    val exploitation = sum / (vis + 1.0)
    val exploration  = (polv * Math.sqrt vtot) / (vis + 1.0)
  in
    exploitation + (!exploration_coeff) * exploration
  end

fun select_in_polext vtot polext =
  let val l0 = map_assoc (value_choice vtot) (dlist polext) in
    fst (select_in_distrib l0)
  end

fun lookahead_once move (d1,d2) nneval board =
  let 
    val board1 = guess_board d1 board  
    val board2 = apply_move move board1 
  in
    expectancy (eval_board (d1,d2) nneval board2)
  end

fun lookahead_loop nsim (d1,d2) (nneval,nnpoli) board (sumtot,vtot) polext =
  if nsim <= 0 then ((sumtot,vtot),polext) else
  let 
    val move = select_in_polext vtot polext
    val reward = lookahead_once move (d1,d2) nneval board 
    val (polv,sum,vis) = dfind move polext
    val newpolext = dadd move (polv, sum + reward, vis + 1.0) polext
  in
    lookahead_loop (nsim - 1) (d1,d2) (nneval,nnpoli) board 
    (sumtot + reward, vtot + 1.0) newpolext
  end

fun lookahead nsim (d1,d2) (nneval,nnpoli) board =
  let 
    val (sumtot,vtot) = (expectancy (eval_board (d1,d2) nneval board), 1.0)
    val pol = combine (movel,denorm (infer_nn nnpoli (oh_board (d1,d2) board)))
    val polext = dnew compare_move (map (fn (a,b) => (a,(b,0.0,0.0))) pol)
  in
    lookahead_loop nsim (d1,d2) (nneval,nnpoli) board (sumtot,vtot) polext
  end

(* -------------------------------------------------------------------------
   Value of a choice in a policy according to PCUT formula.
   ------------------------------------------------------------------------- *)


(*
load "mleHanabi"; open mleHanabi;
load "mlNeuralNetwork"; open mlNeuralNetwork;
load "aiLib"; open aiLib;
val d1 = dempty compare_obsc
val board1 = random_startboard ()
val board2 = guess_board d1 board1;
#hand1 board1;
*)

(*
load "mleHanabi"; open mleHanabi;
load "mlNeuralNetwork"; open mlNeuralNetwork;
load "aiLib"; open aiLib;

val nsim = 1000
val (d1,d2) = (dempty compare_obsc, dempty compare_obs)
val nneval = random_nn (tanh,dtanh) [350,350,10]
val nnpoli = random_nn (tanh,dtanh) [350,350,20]
val board = random_startboard ()
val ((sumtot,vtot),polext) = lookahead nsim (d1,d2) (nneval,nnpoli) board;
dlist polext;
*)

(*
fun lookahead (d1,d2) (nnpoli,nneval) board =
*)



(*
fun collect_boardl_aux acc nn board =
  if null (#deck board) orelse (#bombs board >= 3)
  then rev (board :: acc)
  else collect_boardl_aux (board :: acc) 
    nn (apply_move (best_move nn board) board)

fun collect_boardl nn board = collect_boardl_aux [] nn board
fun compute_dis nn ngame = 
  let 
    val boardl1 = List.tabulate (ngame, fn _ => random_startboard ())
    val boardl2 = List.concat (map (collect_boardl nn) boardl1)
    val obsl1 = List.concat (map observe_hand boardl2)
    fun drop_fst (a,b,c) = (b,c)
    val obsl2 = map_fst drop_fst obsl1
    val dis1 = dmap (fn (_,l) => mk_carddis l) (dregroup compare_obsc obsl1)
    val dis2 = dmap (fn (_,l) => mk_carddis l) (dregroup compare_obs obsl2)
  in
    (dis1, dis2)
  end
*)

(*
load "mleHanabi"; open mleHanabi;
load "mlNeuralNetwork"; open mlNeuralNetwork;
load "aiLib"; open aiLib;
val nn = random_nn (tanh,dtanh) [350,350,20];
val ngame = 100;
val (r,t) = 
  add_time (play_ngame (dempty compare_obsc, dempty compare_obs) nn) ngame;

*)

(*
make play depend on distribs (dis1 and dis2)
*)


end (* struct *)
