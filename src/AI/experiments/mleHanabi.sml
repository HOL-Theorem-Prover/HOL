(* ========================================================================= *)
(* FILE          : mleHanabi.sml                                             *)
(* DESCRIPTION   : Hanabi card game                                          *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mleHanabi :> mleHanabi =
struct

open HolKernel boolLib Abbrev aiLib smlParallel 
  mlTreeNeuralNetwork mlReinforce

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

fun card_of_string s =
  (string_to_int (Char.toString (String.sub (s,0))) , 
   color_of_char (String.sub (s,1)))

val full_deck = 
  List.concat (map (fn x => [(1,x),(1,x),(1,x)]) colorl) @
  List.concat (map (fn x => [(2,x),(2,x)]) colorl)



(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board =
  {
  p1turn : bool,
  hand1 : card vector, hand2 : card vector,
  clues1 : card vector, clues2 : card vector,
  clues : int, score : int, bombs : int,
  deck : card list, disc : card list, pile : card vector
  }

fun string_of_p1turn p1turn = 
  if p1turn then "Player1" else "Player2"

fun string_of_hand hand = 
  String.concatWith " " (map string_of_card (vector_to_list hand))

fun hand_of_string s = 
  Vector.fromList (map card_of_string (String.tokens Char.isSpace s))

fun nice_of_board {p1turn,hand1,hand2,clues1,clues2,
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
    hand1 = Vector.fromList v1, 
    hand2 = Vector.fromList v2,
    clues1 = nohand,
    clues2 = nohand,
    clues = 8,
    score = 0, 
    bombs = 0,
    deck = d3 @ [nocard,nocard],
    disc = [],
    pile = Vector.fromList (map (fn x => (0,x)) colorl)
    }
  end

fun status_of board = 
  if #score board >= !level_glob then Win 
  else if null (#deck board) then Lose
  else Undecided

(* -------------------------------------------------------------------------
   Representation of board as a tree neural network
   ------------------------------------------------------------------------- *)

fun mk_color c = mk_var ("color_" ^ string_of_color c, bool)
fun mk_number i = mk_var ("number_" ^ its i, bool)  
val cardop = ``cardop : bool -> bool -> bool``
fun mk_card (i,c) = mk_binop cardop (mk_number i,mk_color c)

val isuc = ``isuc : bool -> bool``;
val izero = ``izero : bool``;
fun mk_isucn n = if n <= 0 then izero else mk_comb (isuc, mk_isucn (n-1))
val emptyop = ``empty : bool``;

val bool5 = ``: bool -> bool -> bool -> bool -> bool -> bool``
val bool6 = ``: bool -> bool -> bool -> bool -> bool -> bool -> bool``
val hand1op = mk_var ("hand1op",bool5) 
val hand2op = mk_var ("hand2op",bool5)
val clues1op = mk_var ("clues1op",bool5)
val clues2op = mk_var ("clues2op",bool5)
val pileop = mk_var ("pileop",bool5)
fun mk_hand cop v = list_mk_comb (cop, map mk_card (vector_to_list v))

val discardop = ``discardop : bool -> bool -> bool``
val boardmoveop = ``boardmoveop : bool -> bool -> bool``
val infoop = ``infoop : bool -> bool -> bool``
val concatop = mk_var ("concatop",bool6)
fun list_mk_binop oper l = case l of
    [] => raise ERR "list_mk_binop" "empty list"
  | [a] => a
  | a :: m => mk_binop oper (a,list_mk_binop oper m)

fun narg_oper oper = (length o fst o strip_type o type_of) oper

val boardopl = 
  map mk_color colorl_ext @ 
  map mk_number numberl_ext @ 
  [cardop,isuc,izero,hand1op,hand2op,clues1op,clues2op,pileop,
   discardop,concatop,emptyop,infoop,boardmoveop]

fun nntm_of_board {p1turn,hand1,hand2,clues1,clues2,clues,
  score,bombs,deck,disc,pile} =
  list_mk_comb (concatop, 
  [
   if p1turn then emptyop else mk_hand hand1op hand1,
   if not (p1turn) then emptyop else mk_hand hand2op hand2,
   mk_hand clues1op clues1,
   mk_hand clues2op clues2,
   list_mk_binop infoop (map mk_isucn [clues,score,bombs]),
   mk_hand pileop pile
  ]
  )

val operl = map_assoc narg_oper boardopl

(* -------------------------------------------------------------------------
   Move
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

fun move_compare (m1,m2) = 
  String.compare (string_of_move m1, string_of_move m2) 

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
    Vector.all test pile
  end

fun update_pile card pile =
  let fun f c = if snd card = snd c then card else c in
    Vector.map f pile
  end

fun apply_move_play i {p1turn,hand1,hand2,clues1,clues2,
  clues,score,bombs,deck,disc,pile} =
  let 
    val newcard = hd deck
    val hand = if p1turn then hand1 else hand2
    val played = Vector.sub (hand,i)
    val playb = is_playable played pile
  in
    {
    p1turn = not p1turn,
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

fun apply_move_discard i {p1turn,hand1,hand2,clues1,clues2,
  clues,score,bombs,deck,disc,pile} =
  let 
    val newcard = hd deck handle Empty => nocard
    val hand = if p1turn then hand1 else hand2
    val discarded = Vector.sub (hand,i)
  in
    {
    p1turn = not p1turn,
    hand1 =  if p1turn then update_hand i newcard hand1 else hand1, 
    hand2 =  if not p1turn then update_hand i newcard hand2 else hand2,
    clues1 = if p1turn then update_hand i nocard clues1 else clues1,
    clues2 = if not p1turn then update_hand i nocard clues2 else clues2,
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

fun apply_move_clue f {p1turn,hand1,hand2,clues1,clues2,clues,
  score,bombs,deck,disc,pile} =
  {
  p1turn = not p1turn,
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
    Play i => apply_move_play i board
  | Discard i => apply_move_discard i board
  | ColorClue c => apply_move_clue (update_color c) board
  | NumberClue n => apply_move_clue (update_number n) board

fun is_applicable board move = case move of
    ColorClue _ => #clues board > 0 
  | NumberClue _ => #clues board > 0 
  | _ => true

fun filter_sit sit l =
  let fun test (m,_) = is_applicable sit move in filter test l end

(* -------------------------------------------------------------------------
   Targets
   ------------------------------------------------------------------------- *)

fun mk_targetl level ntarget = 
  List.tabulate (ntarget, fn _ => random_startboard ())

fun write_targetl file targetl =
  let 
    val macrol = vector_to_list (!macro_array)
    val olsizel = map dest_startsit targetl 
  in
    writel (file ^ "_macrol") (map string_of_macro macrol);
    writel (file ^ "_targetl") (map string_of_olsize olsizel)
  end

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

val gamespec : (board,move) mlReinforce.gamespec =
  {
  movel = movel,
  move_compare = move_compare,
  string_of_move = string_of_move,
  filter_sit = filter_sit,
  status_of = status_of,
  apply_move = apply_move,
  operl = operl,
  nntm_of_sit = nntm_of_board,
  mk_targetl = mk_targetl,
  write_targetl = write_targetl,
  read_targetl = read_targetl,
  max_bigsteps = max_bigsteps
  }




(* 
load "mleHanabi"; open mleHanabi;
load "aiLib"; open aiLib;
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;

summary_file := "hanabi_run21";
dim_glob := 4;
nepoch_glob := 100;
bsize_glob := 16;
lr_glob := 0.02;
ngame_glob := 500;
ncore_explore := 8;
ncore_train := 8;
nsim_glob := 1;
level_glob := 1;

val dhtnn = rl_loop 100;
*)

(*
val tnnl = List.tabulate (5, fn _ => random_tnn (4,11) operl);
val dhtnn = random_dhtnn (4,20) operl;
val board = random_startboard ();
val nsim = 16000;
val ex = lookahead (nsim,dhtnn,tnnl) board;
val pol = combine (movel_glob, #3 ex);
*)

end (* struct *)
