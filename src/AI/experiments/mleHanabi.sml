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
fun debug s = 
  debug_in_dir (HOLDIR ^ "/src/AI/experiments/debug") "mleHanabi" s
val eval_dir = HOLDIR ^ "/src/AI/experiments/eval"
val summary_file = ref "default"
fun summary s = 
  (mkDir_err eval_dir; 
   print_endline s;
   append_endline (eval_dir ^ "/" ^ !summary_file) s)

val nsim_glob = ref 1600

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

fun update_hand1 {p1turn,hand1,hand2,clues1,clues2,clues,
  score,bombs,deck,disc,pile} hand =
  {
  p1turn=p1turn, hand1=hand, hand2=hand2,
  clues1=clues1,clues2=clues2,clues=clues,
  score=score,bombs=bombs,deck=deck,disc=disc,pile=pile
  }

fun update_hand2 {p1turn,hand1,hand2,clues1,clues2,clues,
  score,bombs,deck,disc,pile} hand =
  {
  p1turn=p1turn, hand1=hand1, hand2=hand,
  clues1=clues1,clues2=clues2,clues=clues,
  score=score,bombs=bombs,deck=deck,disc=disc,pile=pile
  }

fun update_disc {p1turn,hand1,hand2,clues1,clues2,clues,
  score,bombs,deck,disc,pile} newdisc =
  {
  p1turn=p1turn, hand1=hand1, hand2=hand2,
  clues1=clues1, clues2=clues2, clues=clues,
  score=score, bombs=bombs, deck=deck, 
  disc=newdisc, pile=pile
  }

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
   Play a game
   ------------------------------------------------------------------------- *)

fun choose_move tnn board =
  let
    val (_,scl) = infer_dhtnn tnn (nntm_of_board board)
    val mscl1 = combine (movel_glob,scl)
    val mscl2 = filter (is_applicable board o fst) mscl1
  in
    select_in_distrib mscl2
  end

fun is_end board = null (#deck board) orelse #bombs board >= 3
fun norm_score board = Real.fromInt (#score board) / 10.0

fun tnn_game tnn =
  let fun loop acc board =
    if is_end board then (rev acc, #score board) else 
    let val move = choose_move tnn board in
      loop ((board,move) :: acc) (apply_move move board)
    end   
  in
    loop [] (random_startboard ())
  end

(* -------------------------------------------------------------------------
   Guess player's hand
   ------------------------------------------------------------------------- *)

fun all_outputs n = 
  let 
    val emptyv = Vector.fromList (List.tabulate (n,fn _ => 0.0))
    fun f k = vector_to_list (Vector.update (emptyv,k,1.0)) 
  in
    List.tabulate (n,f)
  end

val cardl_ext = nocard :: List.concat (map (fn x => [(1,x),(2,x)]) colorl)

val cardoutput_list = combine (cardl_ext,all_outputs (length cardl_ext))

fun hide_from n hand = 
  let fun f (i,card) = if i < n then card else nocard in
    Vector.mapi f hand
  end

fun p1_guess_ex {p1turn,hand1,hand2,clues1,clues2,clues,
  score,bombs,deck,disc,pile} n =
  let 
    val nntm = mk_hand clues1op clues1
      (* list_mk_comb (concatop, 
      [
       mk_hand hand2op hand2,
       mk_hand clues2op clues2,
       mk_hand hand1op (hide_from n hand1),
       mk_hand clues1op clues1,
       list_mk_binop infoop (map mk_isucn [clues,score,bombs]),
       mk_hand pileop pile
      ]) *)
    val card = Vector.sub (hand1,n)
    val output = assoc card cardoutput_list
  in
    (nntm,output)
  end

fun p2_guess_ex {p1turn,hand1,hand2,clues1,clues2,clues,
  score,bombs,deck,disc,pile} n =
  let 
    val nntm = mk_hand clues1op clues2
    (* list_mk_comb (concatop, 
      [
       mk_hand hand1op hand1,
       mk_hand clues1op clues1,
       mk_hand hand2op (hide_from n hand2),
       mk_hand clues2op clues2,
       list_mk_binop infoop (map mk_isucn [clues,score,bombs]),
       mk_hand pileop pile
      ]) *)
    val card = Vector.sub (hand2,n)
    val output = assoc card cardoutput_list
  in
    (nntm,output)
  end

fun extract_guess board =
  if #p1turn board 
  then List.tabulate (5,p1_guess_ex board) 
  else List.tabulate (5,p2_guess_ex board)

(* -------------------------------------------------------------------------
   Selection of a random hand
   ------------------------------------------------------------------------- *)

fun card_match clue card =
  (fst clue = 0 orelse fst clue = fst card) andalso
  (snd clue = NoColor orelse snd clue = snd card)

fun hand_match clues hand =
  Vector.all I (
    Vector.mapi (fn (i,x) => card_match (Vector.sub (clues,i)) x) hand)

fun select_card f board ((tnn,n),hand) =
  let
    val nntm = 
      if #p1turn board
      then fst (p1_guess_ex (update_hand1 board hand) n)
      else fst (p2_guess_ex (update_hand2 board hand) n)
    val distrib = combine (cardl_ext,infer_tnn tnn nntm)
    val card = f distrib
    val newhand = Vector.update (hand,n,card)
  in
    newhand 
  end

fun select_hand f tnnl board =
  foldl (select_card f board) nohand (number_snd 0 tnnl)

fun guess_hand tnnl board = 
  let 
    val cluev = if #p1turn board then #clues1 board else #clues2 board
    fun loop n =
      let val h = select_hand select_in_distrib tnnl board in
        if n <= 0 orelse hand_match cluev h
        then h
        else loop (n-1)
      end 
    val disc = shuffle (#disc board)
    val hand = loop 5
  in
    if #p1turn board
    then update_disc (update_hand1 board hand) disc
    else update_disc (update_hand2 board hand) disc
  end
  
(* -------------------------------------------------------------------------
   Testing accuracy with respect to ground truth
   ------------------------------------------------------------------------- *)

fun has_noclues (board:board) = 
  if #p1turn board 
  then #clues1 board = nohand 
  else #clues2 board = nohand

fun is_accurate tnnl (board:board) = 
  let 
    val cluev = if #p1turn board then #clues1 board else #clues2 board
    val besthand = select_hand best_in_distrib tnnl board
  in
    hand_match cluev besthand
  end

fun accuracy tnnl boardl = 
  int_div  (length (filter (is_accurate tnnl) boardl)) (length boardl)


(* -------------------------------------------------------------------------
   One step look-ahead
   ------------------------------------------------------------------------- *)

val exploration_coeff = ref 2.0

fun value_choice vistot ((move,polv),(sum,vis)) =
  let
    val exploitation = sum / (vis + 1.0)
    val exploration  = (polv * Math.sqrt vistot) / (vis + 1.0)
  in
    (move, exploitation + (!exploration_coeff) * exploration)
  end

fun proba_norm l =
  let val sum = sum_real l in
    if sum <= 0.0001 then raise ERR "proba_norm" "" else
    map (fn x => x / sum) l
  end

fun init_distrib dhtnn board =
  let
    val (reward,p) = infer_dhtnn dhtnn (nntm_of_board board)
    val distrib = combine (movel_glob, proba_norm p)
    fun f x = (x,(0.0,0.0))
  in
    ((reward,1.0), map f distrib)
  end
 
fun lookahead_once (dhtnn,tnnl) board ((sumtot,vistot),distrib) =
  let 
    val distrib1 = map (value_choice vistot) distrib
    val distrib2 = filter (is_applicable board o fst) distrib1
    val move = best_in_distrib distrib2
    val board1 = guess_hand tnnl board
    val board2 = apply_move move board1
    val reward = 
      if is_end board2 
      then norm_score board2
      else fst (infer_dhtnn dhtnn (nntm_of_board board2))
    fun f ((m,polv),(sum,vis)) =
      if m = move 
      then ((m,polv), (sum + reward, vis + 1.0))
      else ((m,polv), (sum, vis))
  in
    ((sumtot + reward, vistot + 1.0), map f distrib)
  end

fun lookahead_loop nsim (dhtnn,tnnl) board distrib =
  if nsim <= 0 then distrib else
  let val newdistrib = lookahead_once (dhtnn,tnnl) board distrib in
    lookahead_loop (nsim -1) (dhtnn,tnnl) board newdistrib
  end

fun widexl_file (wid,job) = wid_dir wid ^ "/exl" ^ its job

fun lookahead (nsim,dhtnn,tnnl) board =
  let
    val distrib_init = init_distrib dhtnn board
    val ((sumtot,vistot), distrib) = 
      lookahead_loop nsim (dhtnn,tnnl) board distrib_init
    val newe = sumtot / vistot
    val newp = map (fn x => (snd (snd x) / (vistot - 1.0))) distrib
  in
    (nntm_of_board board,[newe],newp)
  end

fun lookahead_boardl (nsim,dhtnn,tnnl) (wid,job) boardl =
  let val exl = map (lookahead (nsim,dhtnn,tnnl)) boardl in
    write_dhex (widexl_file (wid,job)) exl
  end

(* -------------------------------------------------------------------------
   External parallelization: helper functions
   ------------------------------------------------------------------------- *)

fun bts b = if b then "true" else "false"
fun stb s = if s = "true" then true else
            if s = "false" then false else
            raise ERR "stb" ""

fun boardl_file () = !parallel_dir ^ "/boardl"

fun string_of_board {p1turn,hand1,hand2,clues1,clues2,clues,
  score,bombs,deck,disc,pile} =
  String.concatWith "," [
    bts p1turn,
    string_of_hand hand1,
    string_of_hand hand2,
    string_of_hand clues1,
    string_of_hand clues2,
    its clues, its score, its bombs,
    String.concatWith " " (map string_of_card deck),
    String.concatWith " " (map string_of_card disc),
    string_of_hand pile
    ]
  
fun write_boardll boardll =
  writel (boardl_file ()) (map string_of_board (List.concat boardll))   
  
fun board_of_string s = 
  case String.fields (fn x => x = #",") s of
    [a,b,c,d,e,f,g,h,i,j,k] =>
    {
    p1turn = stb a,
    hand1 = hand_of_string b,
    hand2 = hand_of_string c,
    clues1 = hand_of_string d,
    clues2 = hand_of_string e,
    clues = string_to_int f,
    score = string_to_int g,
    bombs = string_to_int h,
    deck = map card_of_string (String.tokens Char.isSpace i),
    disc = map card_of_string (String.tokens Char.isSpace j),
    pile = hand_of_string k
    }
  | _ => raise ERR "board_of_string" ""

fun read_boardll () = 
  mk_batch_full 100 (map board_of_string (readl (boardl_file ())))

(* load "mleHanabi"; open mleHanabi;
val boardl1 = [random_startboard (),random_startboard ()];
write_boardl boardl1;
val boardl2 = read_boardl ();
boardl1 = boardl2;

*)


fun dhtnn_file () = !parallel_dir ^ "/dhtnn"
fun tnnl_file () = 
  map (fn x => !parallel_dir ^ "/tnn" ^ x) (List.tabulate (5,its))



fun read_state_s () =
  String.concatWith "\n"
  [
  "let",
  "  val dhtnn = mlTreeNeuralNetwork.read_dhtnn (mleHanabi.dhtnn_file ())",
  "  val tnnl = map (mlTreeNeuralNetwork.read_tnn) (mleHanabi.tnnl_file ())",
  "in",
  "  (" ^ its (!nsim_glob) ^ ",dhtnn,tnnl)",
  "end"
  ]

fun read_result_extern (wid,job) =
  let val dhex = read_dhex (widexl_file (wid,job)) in
    remove_file (widexl_file (wid,job)); dhex
  end

(* -------------------------------------------------------------------------
   External parallelization: main call
   ------------------------------------------------------------------------- *)

val ncore_explore = ref 8

fun explore_parallel (dhtnn,tnnl) boardll =
  let
    fun write_state () = 
      (
      write_dhtnn (dhtnn_file ()) dhtnn;
      app (uncurry write_tnn) (combine (tnnl_file (),tnnl))
      )
    val write_argl = write_boardll
    val state_s = read_state_s ()
    val argl_s = "mleHanabi.read_boardll ()"
    val f_s = "mleHanabi.lookahead_boardl"
    fun code_of wid = standard_code_of (state_s,argl_s,f_s) wid
  in
    parmap_queue_extern (!ncore_explore) code_of (write_state, write_argl)
    read_result_extern boardll
  end

(* -------------------------------------------------------------------------
   Reinforcement learning loop
   ------------------------------------------------------------------------- *)


val dim_glob = ref 8
val ncore_train = ref 8
val bsize_glob = ref 32
val lr_glob = ref 0.02
val nepoch_glob = ref 20
val ngame_glob = ref 4000

fun train_tnn ncore exl =
  let
    val tt = (exl,first_n 100 exl)
    val outn = length (snd (hd exl))
    val tnn = random_tnn (!dim_glob,outn) operl
    val schedule = [(!nepoch_glob,!lr_glob)]
  in
    prepare_train_tnn (ncore,!bsize_glob) tnn tt schedule
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
   "nsim_glob: " ^ its (!nsim_glob),
   "ngame_glob: " ^ its (!ngame_glob)])
  ) 

fun rl_loop_aux (n,nmax) dhtnn =
  if n >= nmax then dhtnn else
  let
    val _ = summary "Eval"
    val (gamel,t) = 
      add_time List.tabulate (!ngame_glob, fn _ => tnn_game dhtnn)
    val scl = map (Real.fromInt o snd) gamel
    val _ = summary ("Eval time: " ^ rts t)
    val _ = summary ("Eval score: " ^ rts (average_real scl))
    val _ = summary "Guess"
    val boardl = List.concat (map (map fst o fst) gamel)
    val boardll = mk_batch_full 100 boardl
    val exll = list_combine (map extract_guess boardl)
    val _ = summary 
      ("Guess examples:" ^ String.concatWith " " (map (its o length) exll))
    val (tnnl,t) = add_time (smlParallel.parmap_batch 5 (train_tnn 1)) exll
    val _ = summary ("Guess network: " ^ rts t)
    val _ = summary "Lookahead"
    val (exl,t) = add_time (explore_parallel (dhtnn,tnnl)) boardll
    val _ = summary ("Lookahead examples: " ^ its (length exl))
    val _ = summary ("Lookahead time: " ^ rts t)
    val randdhtnn = random_dhtnn (!dim_glob,length movel_glob) operl
    val (newdhtnn,t) = add_time 
      (train_dhtnn_schedule 4 randdhtnn (!bsize_glob) 
      (List.concat exl)) [(!nepoch_glob,!lr_glob)]
    val _ = summary ("Lookahead network: " ^ rts t)
  in
    rl_loop_aux (n+1,nmax) newdhtnn
  end

fun rl_loop nmax = 
  let val randdhtnn = random_dhtnn (!dim_glob,length movel_glob) operl in
    summary_parameters ();
    rl_loop_aux (0,nmax) randdhtnn
  end


(* 
load "mleHanabi"; open mleHanabi;
load "aiLib"; open aiLib;
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;

summary_file := "hanabi_run15";
dim_glob := 8;
nepoch_glob := 100;
bsize_glob := 16;
lr_glob := 0.02;
ngame_glob := 1000;
ncore_explore := 50;
nsim_glob := 1600;

val dhtnn = rl_loop 20;
*)

end (* struct *)
