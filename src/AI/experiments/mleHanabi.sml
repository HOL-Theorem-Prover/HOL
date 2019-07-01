(* ========================================================================= *)
(* FILE          : mleHanabi.sml                                             *)
(* DESCRIPTION   : Hanabi card game                                          *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mleHanabi :> mleHanabi =
struct

open HolKernel boolLib Abbrev aiLib smlParallel psMCTS
  mlTreeNeuralNetwork mlReinforce

val ERR = mk_HOL_ERR "mleHanabi"
fun debug s = 
  debug_in_dir (HOLDIR ^ "/src/AI/experiments/debug") "mleHanabi" s
val eval_dir = HOLDIR ^ "/src/AI/experiments/eval"
val summary_file = ref "default"
fun summary s = 
  (mkDir_err eval_dir; 
   print_endline s;
   append_endline (eval_dir ^ "/" ^ !summary_file) s)

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

fun string_of_card (n,c) = 
  if (n,c) = nocard then "__"  else its n ^ string_of_color c

val full_deck = 
  List.concat (map (fn x => [(1,x),(1,x),(1,x)]) colorl) @
  List.concat (map (fn x => [(2,x),(2,x)]) colorl)
(* @
  List.concat (map (fn x => [(3,x),(3,x)]) colorl) @
  List.concat (map (fn x => [(4,x),(4,x)]) colorl) @
  List.concat (map (fn x => [(5,x)]) colorl)
*)

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

fun string_of_board {p1turn,hand1,hand2,clues1,clues2,
  clues,score,bombs,deck,disc,pile} =
  String.concatWith "\n  " 
  [string_of_p1turn p1turn,
   String.concatWith " " (map its [score,clues,bombs,length deck]),
   "", string_of_hand hand1, string_of_hand clues1,
   "", string_of_hand hand2, string_of_hand clues2, 
   "", String.concatWith " " (map string_of_card disc), 
   "", string_of_hand pile,
   ""]

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
    clues1 = Vector.fromList (List.tabulate (5, fn _ => nocard)),
    clues2 = Vector.fromList (List.tabulate (5, fn _ => nocard)),
    clues = 8,
    score = 0, 
    bombs = 0,
    deck = d3 @ [nocard,nocard],
    disc = [],
    pile = Vector.fromList (map (fn x => (0,x)) colorl)
    }
  end

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

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

datatype move =
    Play of int
  | Discard of int
  | ColorClue of color
  | NumberClue of int

fun mk_play i = mk_var ("play_" ^ its i, bool) 
fun mk_discard i = mk_var ("discard_" ^ its i, bool) 
fun mk_cluec c = mk_var ("cluec_" ^ string_of_color c, bool)
fun mk_cluen n = mk_var ("cluen_" ^ its n, bool)

fun nntm_of_move move = case move of
    Play i => mk_play i
  | Discard i => mk_discard i
  | ColorClue c => mk_cluec c
  | NumberClue n => mk_cluen n

fun string_of_move move = case move of
    Play i => "P" ^ its i
  | Discard i => "D" ^ its i
  | ColorClue c => "C" ^ string_of_color c
  | NumberClue n => "N" ^ its n

val positionl = [0,1,2,3,4]

val movel_glob = 
  map Play positionl @ map Discard positionl @
  map ColorClue colorl @ map NumberClue numberl

val moveopl = map nntm_of_move movel_glob

val operl = map_assoc narg_oper (moveopl @ boardopl)

fun nntm_of_boardmove (board,move) =
  mk_binop boardmoveop (nntm_of_board board, nntm_of_move move)


fun move_compare (m1,m2) = 
  String.compare (string_of_move m1, string_of_move m2) 

fun update_hand i card hand = 
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
    hand1 =  if p1turn then update_hand i newcard hand1  else hand1, 
    hand2 =  if not p1turn then update_hand i newcard hand2 else hand2,
    clues1 = if p1turn then update_hand i nocard clues1 else clues1,
    clues2 = if not p1turn then update_hand i nocard clues2 else clues2,
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

(* -------------------------------------------------------------------------
   Choose move
   ------------------------------------------------------------------------- *)

fun random_move board = 
  let val movel = filter (is_applicable board) movel_glob in
    random_elem movel
  end

fun random_game () =
  let
    fun loop acc board =
      (
      if null (#deck board) orelse #bombs board > 3
      then (rev acc, #score board) 
      else 
        let val move = random_move board in
          loop ((board,move) :: acc) (apply_move move board)
        end 
      )
  in
    loop [] (random_startboard ())
  end

fun choose_move_temp tnn board =
  let 
    val ml = filter (is_applicable board) movel_glob 
    val mtml = map_assoc (fn x => nntm_of_boardmove (board,x)) ml
    val mscl = map_snd (hd o infer_tnn tnn) mtml
  in
    select_in_distrib mscl
  end

fun tnn_game_temp tnn =
  let
    fun loop acc board =
      (
      if null (#deck board) orelse #bombs board > 3
      then (rev acc, #score board) 
      else 
        let val move = choose_move_temp tnn board in
          loop ((board,move) :: acc) (apply_move move board)
        end 
      )
  in
    loop [] (random_startboard ())
  end

fun best_in_distrib distrib =
  let fun cmp (a,b) = Real.compare (snd b,snd a) in
    fst (hd (dict_sort cmp distrib))
  end

fun choose_move tnn board =
  let 
    val ml = filter (is_applicable board) movel_glob 
    val mtml = map_assoc (fn x => nntm_of_boardmove (board,x)) ml
    val mscl = map_snd (hd o infer_tnn tnn) mtml
  in
    best_in_distrib mscl
  end

fun tnn_game tnn =
  let
    fun loop acc board =
      (
      if null (#deck board) orelse #bombs board > 3
      then (rev acc, #score board) 
      else 
        let val move = choose_move tnn board in
          loop ((board,move) :: acc) (apply_move move board)
        end 
      )
  in
    loop [] (random_startboard ())
  end

fun extract_ex (bml,sc) = 
  let 
    val sc' = Real.fromInt sc / 11.0
    fun f bm = (nntm_of_boardmove bm, [sc'])
  in
    map f bml
  end


val ncore_explore = ref 8
val dim_glob = ref 8
val ncore_train = ref 8
val bsize_glob = ref 32
val lr_glob = ref 0.02
val nepoch_glob = ref 20
val ngame_glob = ref 4000

fun train_tnn exl =
  let
    val tt = (exl,first_n 100 exl)
    val tnn = random_tnn (!dim_glob,1) operl
    val schedule = [(!nepoch_glob,!lr_glob)]
  in
    prepare_train_tnn (!ncore_train,!bsize_glob) tnn tt schedule
  end

fun gen_ex_temp ngame tnn =
  let 
    fun f () = tnn_game_temp tnn
    val gamel = smlParallel.parmap_queue (!ncore_explore) 
      f (List.tabulate (ngame, fn _ => ()))
    val r = average_real (map (Real.fromInt o snd) gamel)   
    val _ = summary (rts r)
  in
    List.concat (map extract_ex gamel)
  end

fun summary_parameters () =
  (
  erase_file (eval_dir ^ "/" ^ !summary_file);
  summary (String.concatWith "\n  " 
  ["summary_file: " ^ !summary_file,
   "ncore_explore: " ^ its (!ncore_explore),
   "dim_glob: " ^ its (!dim_glob),
   "ncore_train: " ^ its (!ncore_train),
   "bsize_glob: " ^ its (!bsize_glob),
   "lr_glob: " ^ rts (!lr_glob),
   "nepoch_glob: " ^ its (!nepoch_glob),
   "ngame_glob: " ^ its (!ngame_glob)])
  ) 

fun rl_loop_aux (n,nmax) tnn =
  if n >= nmax then tnn else
  let 
    val _ = summary ("Generation " ^ its n)
    val exl = gen_ex_temp (!ngame_glob) tnn
    val _ = summary ("Training " ^ its n)
    val tnn' = train_tnn exl
    val _ = write_tnn 
      (eval_dir ^ "/" ^ !summary_file ^ "_gen" ^ its (n+1)) tnn'
  in
    rl_loop_aux (n+1,nmax) tnn'  
  end

fun rl_loop nmax = 
  (
  summary_parameters ();
  rl_loop_aux (0,nmax) (random_tnn (!dim_glob,1) operl)
  )

(* 
load "mleHanabi"; open mleHanabi;
load "aiLib"; open aiLib;
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;

summary_file := "hanabi_run4";
ncore_explore := 8;
dim_glob := 8;
ncore_train := 8;
bsize_glob := 16;
lr_glob := 0.02;
nepoch_glob := 20;
ngame_glob := 2000;

val tnn = rl_loop 20;
*)

end (* struct *)
