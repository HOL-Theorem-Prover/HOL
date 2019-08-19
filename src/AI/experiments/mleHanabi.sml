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
   Misc
   ------------------------------------------------------------------------- *)

val hanabi_dir = HOLDIR ^ "/src/AI/experiments/hanabi_result"
val summary_dir = ref (hanabi_dir ^ "/default")
fun summary file s = 
  (print_endline s; 
   append_endline (!summary_dir ^ "/" ^ file) s)
fun sr r = pad 5 "0" (rts_round 3 r)
type ex = real list * real list

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

val possible_cards =
  List.concat (map (fn x => [(1,x)]) colorl) @
  List.concat (map (fn x => [(2,x)]) colorl) @
  List.concat (map (fn x => [(3,x)]) colorl) @
  List.concat (map (fn x => [(4,x)]) colorl) @
  List.concat (map (fn x => [(5,x)]) colorl)

val cardl_glob = List.concat (map (fn x => [(1,x),(2,x)]) colorl)

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

fun pretty_board {p1turn,lastmove1,lastmove2,hand1,hand2,clues1,clues2,
  clues,score,bombs,deck,disc,pile} =
  String.concatWith "\n  "
  [
   string_of_p1turn p1turn,
   String.concatWith " " (map its [score,clues,bombs,length deck]),
   "", string_of_hand hand1, string_of_hand clues1,
   "", string_of_hand hand2, string_of_hand clues2,
   "", String.concatWith " " (map string_of_card disc),
   "", string_of_hand pile,
   ""]

val nohand = Vector.fromList (List.tabulate (5, fn _ => nocard))

val maxclues = 8
val maxscore = 10
val maxbombs = 2

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
    clues1 = Vector.fromList v1,
    clues2 = Vector.fromList v2,
    clues = maxclues, score = 0, bombs = 0,
    deck = d3 @ [nocard],
    disc = [],
    pile = Vector.fromList (map (fn x => (0,x)) colorl)
    }
  end

fun random_pile () =
  Vector.fromList (map (fn x => (random_int (0,4),x)) colorl)

fun random_card () = random_elem possible_cards

(* -------------------------------------------------------------------------
   Guessed hands conditionned on observables
   ------------------------------------------------------------------------- *)

type obsc = (move option * card * int)
type obs = card * int
type obsc_dict = (obsc, (card,int) Redblackmap.dict) Redblackmap.dict
type obs_dict = (obs, (card,int) Redblackmap.dict) Redblackmap.dict
type nn = mlNeuralNetwork.nn
type player = (obsc_dict * obs_dict) * (nn * nn)

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

fun distrib_from_guess d = 
  let fun f card = Real.fromInt (dfind card d) handle NotFound => 0.0 in
    normalize_distrib (map_assoc f cardl_ext)
  end
 
fun update_observable (board,(d1,d2)) =
  let val (l1,l2) = observe_hand board in
    (foldl update_d d1 l1, foldl update_d d2 l2)  
  end

(* -------------------------------------------------------------------------
   Representation of board as onehot encoding
   ------------------------------------------------------------------------- *)

fun onehot (k,n) =
  let fun f i = if i = k then 1.0 else 0.0 in List.tabulate (n,f) end

fun nohot n = let fun f i = 0.0 in List.tabulate (n,f) end

fun oh_color c =  onehot (assoc c (number_snd 0 colorl_ext), length colorl_ext)
fun oh_number i = onehot (i,length numberl_ext)
fun oh_card (i,c) = oh_number i @ oh_color c

fun oh_hand v = List.concat (map oh_card (vector_to_list v))
fun oh_pile v = List.concat (map (oh_number o fst) (vector_to_list v))

fun oh_move m = onehot (assoc m (number_snd 0 movel), length movel)

fun oh_moveo mo = 
  if isSome mo 
  then [1.0] @ oh_move (valOf mo)
  else nohot (length movel + 1)

fun obs_of_board {p1turn,lastmove1,lastmove2,hand1,hand2,clues1,clues2,
  clues,score,bombs,deck,disc,pile} pos = 
  let 
    val moveo = if p1turn then lastmove2 else lastmove1
    val clue = Vector.sub (if p1turn then clues1 else clues2, pos) 
    val card = Vector.sub (if p1turn then hand1 else hand2, pos) 
  in
    (moveo,clue,pos)
  end

fun card_match clue card =
  (fst clue = fst card orelse fst clue = 0) andalso
  (snd clue = snd card orelse snd clue = NoColor)

fun uniform_guess clue = 
  let val l = 
    map_assoc (fn x => if card_match clue x then 1 else 0) cardl_ext
  in
    dnew compare_card l
  end

fun nnin_of_obspos (d1,d2) board pos =
  let
    val (moveo,clue,pos) = obs_of_board board pos
    val guess1 = dfind (moveo,clue,pos) d1 
      handle NotFound => uniform_guess clue
    val dis1 = distrib_from_guess guess1
    val guess2 = dfind (clue,pos) d2
      handle NotFound => uniform_guess clue
    (* if dlenght guess2 then *)
    val dis2 = distrib_from_guess guess2
  in
    (map snd dis1) @ (map snd dis2)
  end

fun string_of_carddis dis =
  let fun f (c,sc) = string_of_card c ^ "-" ^ sr sc in
    String.concatWith " " (map f dis)
  end

fun print_obs (d1,d2) board pos =
  let
    val (moveo,clue,pos) = obs_of_board board pos
    val guess1 = dfind (moveo,clue,pos) d1 
      handle NotFound => uniform_guess clue
    val dis1 = distrib_from_guess guess1
    val guess2 = dfind (clue,pos) d2
      handle NotFound => uniform_guess clue
    val dis2 = distrib_from_guess guess2
  in
    print_endline (string_of_carddis dis1);
    print_endline (string_of_carddis dis2)
  end

val empty_obs = (dempty compare_obsc, dempty compare_obs)

fun nnin_of_obs obs board = 
  List.concat (map (nnin_of_obspos obs board) positionl)

fun oh_disc disc =
  let 
    val d = count_dict (dempty compare_card) disc 
    fun f n x = if (dfind x d = n) handle NotFound => false then 1.0 else 0.0 
    fun g x = if fst x = 1 then [f 1 x, f 2 x, f 3 x] else [f 1 x, f 2 x]
  in
    List.concat (map g cardl_glob)
  end

fun oh_board (d1,d2) 
  (board as {p1turn,lastmove1,lastmove2,hand1,hand2,clues1,clues2,clues,
  score,bombs,deck,disc,pile}) =
  let
    val t1 = if p1turn then hand1 else hand2
    val t2 = if p1turn then hand2 else hand1
  in
    (
    List.concat 
     [onehot (bombs,maxbombs + 1), onehot (clues,maxclues + 1),
      onehot (score,maxscore + 1),
      oh_hand t1, oh_hand t2,
      oh_pile pile, oh_disc disc]
    )
  end

(* 
load "mleHanabi"; open mleHanabi;
load "aiLib"; open aiLib;
val board = random_startboard ();
print_obs empty_obs board 0;
oh_board empty_obs (random_startboard ());
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
    clues1 = if p1turn then draw_card i newcard hand1  else hand1
             (* if p1turn then draw_card i nocard clues1 else clues1 *),
    clues2 = if not p1turn then draw_card i newcard hand2 else hand2
             (* if not p1turn then draw_card i nocard clues2 else clues2 *),
    clues = if playb andalso fst played = 5 andalso clues < maxclues 
            then clues + 1
            else clues,
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
    clues1 = if p1turn then draw_card i newcard hand1 else hand1
     (* if p1turn then draw_card i nocard clues1 else clues1 *),
    clues2 = if not p1turn then draw_card i newcard hand2 else hand2
     (* if not p1turn then draw_card i nocard clues2 else clues2 *),
    clues = if clues >= maxclues then maxclues else clues + 1,
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

fun is_applicable (board:board) move = case move of
    ColorClue _ => #clues board > 0
  | NumberClue _ => #clues board > 0
  | Discard _ => true
  | Play _ => true

(* -------------------------------------------------------------------------
   Play game (filter examples that are all zero ar all ones.
   ------------------------------------------------------------------------- *)

fun infer_poli (obs,(nne,nnp)) board =
  normalize_proba (infer_nn nnp (oh_board obs board))

fun best_move player board =
  let 
    val pol1 = combine (movel, infer_poli player board)
    val pol2 = filter (fn x => is_applicable board (fst x)) pol1
  in
    best_in_distrib pol2
  end

fun is_endboard board =
  null (#deck board) orelse 
  #bombs board > maxbombs orelse
  #score board >= maxscore


(* -------------------------------------------------------------------------
   Evaluation
   ------------------------------------------------------------------------- *)

fun infer_eval (obs,(nne,nnp)) board =
  if is_endboard board 
  then onehot (#score board,maxscore + 1)
  else (normalize_proba o infer_nn nne o oh_board obs) board

fun eval_expectancy l =
  let fun f i x = Real.fromInt i * x in sum_real (mapi f l) end

(* -------------------------------------------------------------------------
   Guesses on current player hand dependent on observables
   ------------------------------------------------------------------------- *)

fun guess_card d1 board pos =
  let
    val (moveo,clue,pos) = obs_of_board board pos
    val guess = dfind (moveo,clue,pos) d1 
      handle NotFound => uniform_guess clue
    val dis = distrib_from_guess guess
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

fun value_choice vtot pol move =
  let
    val (prior,sum,vis) = dfind move pol
    val exploitation = sum  / (vis + 1.0)
    val exploration  = prior * Math.sqrt vtot / (vis + 1.0)
  in
    exploitation + (!exploration_coeff) * exploration
  end

fun select_in_pol board vtot pol =
  let 
    val dis1 = map_assoc (value_choice vtot pol) movel
    val dis2 = filter (fn (x,_) => is_applicable board x) dis1
  in
    best_in_distrib dis2
  end

fun lookahead_once move player board =
  let 
    val board1 = guess_board (fst (fst player)) board  
    val board2 = apply_move move board1 
  in
    infer_eval player board2
  end

fun lookahead_loop nsim player board vtot pol rewarddisl =
  if nsim <= 0 then (pol,rewarddisl) else
  let 
    val move = select_in_pol board vtot pol
    val rewarddis = lookahead_once move player board 
    val reward = eval_expectancy rewarddis / (Real.fromInt maxscore)
    val (polv,sum,vis) = dfind move pol
    val newpol = dadd move (polv, sum + reward, vis + 1.0) pol
  in
    lookahead_loop (nsim - 1) player board 
    (vtot + 1.0) newpol (rewarddis :: rewarddisl)
  end

fun add_noise pol =
  let 
    val alpha = 0.3
    val noisel = dirichlet_noise alpha (length pol)
    fun f ((m,r1),r2) = (m, 0.75 * r1 + 0.25 * r2) 
  in
    map f (combine (pol,noisel))
  end

fun lookahead_aux nsim player board =
  let
    val pol1 = combine (movel, infer_poli player board)
    val pol2 = add_noise pol1
    val pol3 = dnew compare_move (map (fn (a,b) => (a,(b,0.0,0.0))) pol2)
  in
    lookahead_loop nsim player board 1.0 pol3 []
  end

(* -------------------------------------------------------------------------
   Extract eval example
   ------------------------------------------------------------------------- *)

fun merge_rewarddisl rewarddisl = map sum_real (list_combine rewarddisl)

fun extract_evalex (d1,d2) board rewarddisl =
  let
    val input = oh_board (d1,d2) board
    val rewarddis = merge_rewarddisl rewarddisl
    val evalout = normalize_proba rewarddis
  in
    (input,evalout)
  end

(* -------------------------------------------------------------------------
   Extract poli example
   ------------------------------------------------------------------------- *)

fun extract_poliex (d1,d2) board pol =
  let
    val input = oh_board (d1,d2) board
    fun f m = #3 (dfind m pol) 
      handle NotFound => raise ERR "extract_poliex" ""
  in
    (input, normalize_proba (map f movel))
  end

fun lookahead nsim (player as ((d1,d2),_)) board =
  let 
    val (pol,rewarddisl) = lookahead_aux nsim player board
    fun f m = #3 (dfind m pol)
    val dis1 = combine (movel, normalize_proba (map f movel))
    val dis2 = filter (fn (x,_) => is_applicable board x) dis1
  in
    (if random_int (0,9) = 0 
     then select_in_distrib dis2
     else best_in_distrib dis2,
     extract_evalex (d1,d2) board rewarddisl,
     extract_poliex (d1,d2) board pol)
  end


(* -------------------------------------------------------------------------
   Play game with lookahead and output the result to a file
   ------------------------------------------------------------------------- *)

fun example_game k player = 
  let 
    val _ = (mkDir_err hanabi_dir; mkDir_err (!summary_dir))
    val file = "game" ^ its k  
    fun f s = summary file s
    val _ = erase_file (!summary_dir ^ "/" ^ file)
    fun loop board =
      if is_endboard board then f (pretty_board board) else 
      let
        val (move,_,_) = lookahead 400 player board
        val newboard = apply_move move board 
      in
        f ("Move " ^ string_of_move move ^ " by");
        f (pretty_board board);
        loop newboard
      end
  in
    loop (random_startboard ())
  end

(* -------------------------------------------------------------------------
   Statistics
   ------------------------------------------------------------------------- *)

fun collect_boardl player board =
  if is_endboard board then [] else 
  let 
    val move = best_move player board
    val newboard = apply_move move board 
  in
    board :: collect_boardl player newboard
  end

fun print_stats_ll b ol fi ll = 
  let
    val newll = combine (ol,list_combine ll)
    fun f (i,l) = summary "stats" (fi i ^ ": " ^ 
      sr (average_real l) ^ " " ^ sr (standard_deviation l))
  in
    app f newll;
    if b then 
      let val el =  map eval_expectancy ll in
        summary "stats" ("eval_expectancy: " ^ sr (average_real el) ^ " " ^ 
               sr (absolute_deviation el))
      end
    else ()
  end

fun stats_player ngame player =
  let
    fun f _ = collect_boardl player (random_startboard ())
    val boardl = List.concat (List.tabulate (ngame,f))
    val lle = map (infer_eval player) boardl
    val llp = map (infer_poli player) boardl
  in
    summary "stats" "eval"; 
    print_stats_ll true (List.tabulate (maxscore + 1,I)) its lle;
    summary "stats" "poli"; 
    print_stats_ll false movel string_of_move llp
  end

fun symdiff_player ngame player1 player2 =
  let 
    fun f1 _ = collect_boardl player1 (random_startboard ())
    val boardl1 = List.concat (List.tabulate (ngame div 2,f1))
    fun f2 _ = collect_boardl player2 (random_startboard ())
    val boardl2 = List.concat (List.tabulate (ngame div 2,f2))
    val boardl = boardl1 @ boardl2
    val lle1 = map (infer_eval player1) boardl
    val llp1 = map (infer_poli player1) boardl
    val lle2 = map (infer_eval player2) boardl
    val llp2 = map (infer_poli player2) boardl
    fun dist (a,b) = Real.abs (a - b)
    fun diff (l1,l2) = average_real (map dist (combine (l1,l2)))
    val diffe = average_real (map diff (combine (lle1,lle2)))
    val diffp = average_real (map diff (combine (llp1,llp2)))
  in
    summary "stats" ("eval (mean absolute diff): " ^ sr diffe);
    summary "stats" ("poli (mean absolute diff): " ^ sr diffp)
  end

val player_mem = 
  ref ((dempty compare_obsc, dempty compare_obs),
       (random_nn (tanh,dtanh) [371,10],
       random_nn (tanh,dtanh) [371,20]))

fun write_stats k scl player =
  let fun f (a,b) = summary "stats" (its a ^ ": " ^ its b) in
    summary "stats" ("Statistics " ^ its k);
    stats_player 1000 player;
    symdiff_player 1000 player (!player_mem);
    app f (dlist (count_dict (dempty Int.compare) scl));
    example_game k player
  end  

(* -------------------------------------------------------------------------
   Reinforcement learning loop
   ------------------------------------------------------------------------- *)

fun random_player () =
  let
    val n = length (oh_board empty_obs (random_startboard ()))
    val nne = random_nn (tanh,dtanh) [n, n, maxscore + 1]
    val nnp = random_nn (tanh,dtanh) [n, n, length movel]
  in
    (empty_obs,(nne,nnp))
  end

fun rl_start () =
  let val player = random_player () in
    print_endline "rl_start";
    player_mem := player;
    (player, random_startboard (), [])
  end

fun update_player (obs,(nne,nnp)) (evalex,poliex) =
  let
    val newobs = obs (* update_observable (board,obs) *)
    val (newnne,_) = train_nn_batch 1 nne [scale_ex evalex]
    val (newnnp,_) = train_nn_batch 1 nnp [scale_ex poliex]
  in
    (newobs,(newnne,newnnp))
  end

fun rl_loop_once k (player,board,scl) =
  let
    val nsim = 800
    val (move,evalex,poliex) = lookahead nsim player board
    val newplayer = update_player player (evalex,poliex)
    val board1 = apply_move move board 
    val _ = print (string_of_move move ^ "-" ^ its (#score board1) ^ " ")
    val board2 = if is_endboard board1 then random_startboard () else board1
    val newscl = if is_endboard board1 
                 then first_n 1000 (#score board1 :: scl) 
                 else scl
    val _ = if is_endboard board1 then (print "\n";
      summary "score" (its k ^ "," ^ sr (average_int newscl)))
      else ()
    val _ = if k mod 1000 = 0 andalso k <> 0
      then (write_stats k scl player; player_mem := player)
      else ()
  in
    (newplayer,board2,newscl)
  end

fun rl_loop_aux (k,n) x = 
  if k >= n then x else rl_loop_aux (k+1,n) (rl_loop_once k x)

fun clean_expdir () =
  (
  mkDir_err hanabi_dir; 
  mkDir_err (!summary_dir);
  erase_file (!summary_dir ^ "/score");
  erase_file (!summary_dir ^ "/stats")
  )

fun rl_loop n = 
  let val _ = clean_expdir () in
    rl_loop_aux (0,n) (rl_start ())
  end

(*
load "mleHanabi"; open mleHanabi;
load "mlNeuralNetwork"; open mlNeuralNetwork;
load "aiLib"; open aiLib;
summary_dir := hanabi_dir ^ "/runtest";
val (player,board,scl) = rl_loop 100000;
write_nn (hanabi_dir ^ "/run1_nne") nne;
write_nn (hanabi_dir ^ "/run1_nnp") nnp;
*)

(* -------------------------------------------------------------------------
   Parallelization
   ------------------------------------------------------------------------- *)

fun worker_play_game player _ =
  let
    val _ = print_endline "new_game"
    val nsim = 800
    fun loop acc board =
      if is_endboard board then (split acc, #score board) else
      let
        val (move,evalex,poliex) = lookahead nsim player board
        val _ = print_endline (string_of_move move)
        val newboard = apply_move move board 
      in
        loop ((evalex,poliex) :: acc) newboard
      end
  in
    loop [] (random_startboard ())
  end

fun write_player file (obs,(nne,nnp)) =
  (write_nn (file ^ "_nne") nne; write_nn (file ^ "_nnp") nnp)

fun read_player file =
  (empty_obs, (read_nn (file ^ "_nne"), read_nn (file ^ "_nnp")))

fun write_result file ((eex,pex),sc) =
  (
  write_exl (file ^ "_eex") eex;
  write_exl (file ^ "_pex") pex;
  writel (file ^ "_score") [its sc]
  )

fun read_result file =
  (
  (read_exl (file ^ "_eex"), read_exl (file ^ "_pex")),
  (string_to_int o only_hd o readl) (file ^ "_score")
  )

fun write_argl file argl = writel file [its (length argl)]
fun read_argl file =  
  List.tabulate ((string_to_int o only_hd o readl) file, fn _ => ())

val extspec : (player, unit, (ex list * ex list) * int) smlParallel.extspec =
  {
  self = "mleHanabi.extspec",
  reflect_globals = fn () => "()",
  function = worker_play_game,
  write_param = write_player,
  read_param = read_player,
  write_argl = write_argl,
  read_argl = read_argl,
  write_result = write_result,
  read_result = read_result
  }

fun process_result r =
  let 
    val (l,scl) = split r
    val (eexll,pexll) = split l 
  in
    (List.concat eexll, List.concat pexll, scl)
  end

fun train_player (obs,(nne,nnp)) (eex,pex) =
  let
    val ncore = 4
    val nepoch = 2
    val bsize = 16
    val newnne = train_nn ncore nepoch nne bsize eex
    val newnnp = train_nn ncore nepoch nnp bsize pex
  in
    (obs,(newnne,newnnp)) 
  end

fun rl_para_once ncore k (player,scl) =
  let
    val _ = print_endline ("Generation " ^ its k)
    val argl = (List.tabulate (100, fn _ => ()))
    val (eex,pex,scl_loc) = process_result 
      (smlParallel.parmap_queue_extern ncore extspec player argl)
    val newplayer = train_player player (eex,pex)
    val newscl = first_n 1000 (scl_loc @ scl)
    val _ = summary "score" (its k ^ "," ^ (sr (average_int newscl)))
    val _ =
      if k mod 10 = 0 andalso k <> 0
      then (write_stats k scl newplayer; player_mem := player)
      else ()
  in
    (newplayer,newscl)
  end

fun rl_para ncore n = 
  let 
    val _ = clean_expdir ()
    val player = random_player ()
    val _ = player_mem := player
    fun loop (k,n) x = 
      if k >= n then x else loop (k+1,n) (rl_para_once ncore k x)
  in
    loop (0,n) (player,[])
  end

(* -------------------------------------------------------------------------
   Experiment: trying to learn each step backward from the endgame.
   ------------------------------------------------------------------------- *)

fun is_endgame (board:board) = 
  #clues board = 0 andalso length (#deck board) = 1 

fun collect_boardl_forced () =
  let fun loop board = 
    if is_endgame board then [board] else
    let 
      fun test move = 
        is_applicable board move andalso
        not (is_endboard (apply_move move board))             
      fun random_move () = random_elem (filter test movel)    
      val newboard = apply_move (random_move ()) board 
    in
      if is_endboard newboard then loop board else board :: loop newboard
    end
  in
    loop (random_startboard ())
  end

fun random_playerdict () = 
  let val l = cartesian_product 
    (List.tabulate (16, fn x => x + 1)) (List.tabulate (9,I)) 
  in
    dnew (cpl_compare Int.compare Int.compare) 
    (map_assoc (fn x => random_player ()) l)
  end

fun slice_board board = (length (#deck board), #clues board)

fun pd_infer_eval playerdict board =
  if is_endboard board 
  then onehot (#score board,maxscore + 1)
  else 
    let val (obs,(nne,_)) =  dfind (slice_board board) playerdict in
      (normalize_proba o infer_nn nne o oh_board obs) board
    end

fun pd_infer_poli playerdict board =
  let val (obs,(_,nnp)) = dfind (slice_board board) playerdict in
    normalize_proba (infer_nn nnp (oh_board obs board))
  end

fun pd_lookahead_once move playerdict board =
  let 
    val ((d1,_),_) = dfind (slice_board board) playerdict
    val board1 = guess_board d1 board
    val board2 = apply_move move board1 
  in
    pd_infer_eval playerdict board2
  end

fun pd_lookahead_loop nsim playerdict board 
  (sumtot,vtot) pol rewarddisl =
  if nsim <= 0 then ((sumtot,vtot),pol,rewarddisl) else
  let 
    val move = select_in_pol board vtot pol
    val rewarddis = pd_lookahead_once move playerdict board 
    val reward = eval_expectancy rewarddis / (Real.fromInt maxscore)
    val (polv,sum,vis) = dfind move pol
    val newpol = dadd move (polv, sum + reward, vis + 1.0) pol
  in
    pd_lookahead_loop (nsim - 1) playerdict board 
    (sumtot + reward, vtot + 1.0) newpol (rewarddis :: rewarddisl)
  end

fun pd_lookahead_aux nsim playerdict board =
  let
    val (sumtot,vtot) = 
      (eval_expectancy (pd_infer_eval playerdict board), 1.0)
    val pol1 = combine (movel, pd_infer_poli playerdict board)
    val pol2 = add_noise pol1
    val pol3 = dnew compare_move (map (fn (a,b) => (a,(b,0.0,0.0))) pol2)
  in
    pd_lookahead_loop nsim playerdict board (sumtot,vtot) pol3 []
  end

fun pd_lookahead nsim playerdict board =
  let 
    val (_,pol,rewarddisl) =
      pd_lookahead_aux nsim playerdict board
    fun f m = #3 (dfind m pol)
    val dis1 = combine (movel, normalize_proba (map f movel))
    val dis2 = filter (fn (x,_) => is_applicable board x) dis1
  in
    (if random_int (0,9) = 0 
     then select_in_distrib dis2
     else best_in_distrib dis2,
     extract_evalex empty_obs board rewarddisl,
     extract_poliex empty_obs board pol)
  end

fun pd_collect_example_aux acc1 acc2 playerdict boardl =
  if null boardl then (acc1,acc2) else
  let val (_,evalex,poliex) = pd_lookahead 400 playerdict (hd boardl) in
    print_endline (its (length boardl));
    pd_collect_example_aux (evalex :: acc1) (poliex :: acc2) 
      playerdict (tl boardl)
  end

fun pd_collect_example playerdict boardl = 
  pd_collect_example_aux [] [] playerdict boardl;


fun pd_play_game playerdict =
  let
    val _ = print_endline "new_game"
    val nsim = 400
    fun loop board =
      if is_endboard board then #score board else
      let
        val (a,b) = slice_board board
        val _ = print_endline (its a ^ " " ^ its b)
        val (move,_,_) = pd_lookahead nsim playerdict board
        val _ = print_endline (string_of_move move)
        val newboard = apply_move move board 
      in
        loop newboard
      end
  in
    loop (random_startboard ())
  end

fun pd_train_player (obs,(nne,nnp)) (eex,pex) =
  let
    val ncore = 4
    val nepoch = 100
    val bsize = 16
    val newnne = train_nn ncore nepoch nne bsize eex
    val newnnp = train_nn ncore nepoch nnp bsize pex
  in  
    (obs,(newnne,newnnp)) 
  end


(*
load "mleHanabi"; open mleHanabi;
load "mlNeuralNetwork"; open mlNeuralNetwork;
load "aiLib"; open aiLib;  


fun mk_ex () =
  let
    val pile = random_pile ()
    val card = random_card ()
  in 
    (oh_pile pile @ oh_card card, 
     if is_playable card pile then [1.0] else [0.0])
  end
;

fun score_pile pile = sum_int (map fst (vector_to_list pile));

fun onehot (k,n) =
  let fun f i = if i = k then 1.0 else 0.0 in List.tabulate (n,f) end

fun mk_ex () =
  let
    val pile = random_pile ()
    val score = score_pile pile
  in 
    (oh_pile pile, onehot (score,26))
  end
;

val exl = List.tabulate (20000,fn _ => mk_ex ());

val dimin = length (oh_pile (random_pile ()));
val nn = random_nn (tanh,dtanh) [dimin, dimin, 26];
learningrate_glob := 0.02;
val newnn = train_nn 4 100 nn 16 exl;



val boardll = List.tabulate (1000, fn _ => collect_boardl_forced ());
val boardl = List.concat boardll;
val board = hd boardl;

fun compute_playable (board: board) =
  let 
    val opphand = if #p1turn board then #hand2 board else #hand1 board 
    fun f card = if is_playable card (#pile board) then 1.0 else 0.0
  in
    (oh_board empty_obs board, map f (vector_to_list opphand))
  end;


val exl = List.tabulate (10000,fn _ => mk_ex ());
val n = length (oh_pile (random_pile ()) @ oh_card (random_card ()))
val n2 = length (oh_board empty_obs (random_startboard ()));
val nn = random_nn (tanh,dtanh) [n2, n2, 1];
learning_rate := 0.02;
val newnn = train_nn 4 100 nn 16 exl;

val boardl1 = map (fn x => (slice_board x, x)) boardl;
val boarddict = dregroup (cpl_compare Int.compare Int.compare) boardl1;
learningrate_glob := 0.0002;

fun update_playerdict ((a,b),playerdict) =
  let 
    val boardl = dfind (a,b) boarddict
    val (eex,pex) = pd_<collect_example newplayerdict boardl
    val newplayer = pd_train_player (random_player ()) (eex,pex)
  in
    dadd (a,b) newplayer playerdict
  end;

val splicel = cartesian_product 
  (List.tabulate (16, fn x => x + 1)) (List.tabulate (9,I)) 

val finalplayerdict = foldl update_playerdict playerdict splicel;

val l1 = List.tabulate (100, fn _ => pd_play_game finalplayerdict);
val n1 = average_int l1;
*)

(*
load "mleHanabi"; open mleHanabi;
load "mlNeuralNetwork"; open mlNeuralNetwork;
load "aiLib"; open aiLib;
summary_dir := hanabi_dir ^ "/looking";
val ncore = 20;
val ngen = 500;
learningrate_glob := 0.002;
val (player,scl) = rl_para ncore ngen;
*)


(* 
evaluate:
-- source of noise (noise + temperature)
-- effect of nsim
-- effect of observables with window
-- effect of training with window
-- effect of lookahead to depth 2
idea:
-- standard (training,exploration,competition)
-- one nn and per player (per maximal number of available moves): 
   games end when no clues are available and no moves are available.
   force games to end on the last turn.
*)


end (* struct *)
