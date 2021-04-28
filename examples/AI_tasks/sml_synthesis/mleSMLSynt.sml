(* ========================================================================= *)
(* FILE          : mleSMLSynt.sml                                            *)
(* DESCRIPTION   : SML program synthesis                                     *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2021                                                      *)
(* ========================================================================= *)

structure mleSMLSynt :> mleSMLSynt =
struct

open HolKernel Abbrev boolLib aiLib smlParallel psMCTS
  mlNeuralNetwork mlTreeNeuralNetwork mlTacticData mleSMLLib

val ERR = mk_HOL_ERR "mleSMLSynt"
val selfdir = HOLDIR ^ "/examples/AI_tasks"
fun nov x = string_to_int (tl_string x)

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = (int list * int) list * int list list
fun string_of_board board = "board"
fun board_compare ((_,a),(_,b)) = 
  list_compare (list_compare Int.compare) (a,b)
fun status_of (board as (iol,valuel)) = case valuel of
   [a] => if list_compare Int.compare (a, map snd iol) = EQUAL then Win else
          Undecided
  | _ => Undecided

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

type move = instr
val movel = all_instr 4 
fun string_of_move m = #1 m
fun move_compare (m1,m2) = String.compare (#1 m1, #1 m2)

fun available_movel (iol,state) =
  let 
    val staten = length state
    val vn = (length o fst o hd) iol
    fun test (name,arity,_) = arity <= staten andalso 
      if String.isPrefix "v" name then nov name < vn else true
  in
    filter test movel
  end
  
fun apply_move move (iol,state) =
  (iol, exec_instr (map fst iol) move state)

(* -------------------------------------------------------------------------
   Game
   ------------------------------------------------------------------------- *)

val game : (board,move) game =
  {
  status_of = Profile.profile "status_of" status_of,
  available_movel = Profile.profile "available_movel" available_movel,
  apply_move = 
    let fun f x y = Profile.profile "apply_move" (apply_move x) y
    in f end
  ,
  string_of_board = string_of_board,
  string_of_move = string_of_move,
  board_compare = board_compare,
  move_compare = move_compare,
  movel = movel
  }

(* 
load "mleSMLSynt"; open mleSMLSynt;
load "mleSMLLib"; open mleSMLLib;
load "psMTCS"; open psMCTS;
load "aiLib"; open aiLib;
load "Profile";

val mctsparam =
  {explo_coeff = 2.0,
   noise = false, noise_coeff = 0.25, noise_gen = random_real,
   nsim = SOME 100000 : int option, time = NONE: real option};

val mctsobj = {game = game, mctsparam = mctsparam,
  player =  psMCTS.uniform_player game};

val inputl = all_input 2 10;
fun targetf [x,y] = x*x + y*y | targetf _ = raise Match;
val iol = map_assoc targetf inputl;
val tree = starting_tree mctsobj (iol,[]);
Profile.reset_all ();
val (_,t) = add_time (mcts mctsobj) tree;
Profile.results ();
tree;

val terml = 
  filter (not o contain_mvar) 
    (map (close_qt o snd o #board o snd) (dlist newtree));

fun is_mvar x = is_var x andalso "M" = fst (dest_var x) andalso type_of x <> ``:'a list``;
fun contain_mvar tm = can (find_term is_mvar) tm;
val nodel = filter (fn (id,x) => not (contain_mvar (#2 (#board x)))) 
  (dlist newtree);


length nodel;
val nodel2 = filter (fn (id,x) => #stati x = Lose) nodel;
length nodel2;
val tml = map (fn (id,x) => (snd o #board) x) nodel2;
val tml2 = filter (fn x => term_size x >= 5 andalso term_size x <= 18 andalso
   term_size ((rand o rand o rator) x) <= 1) tml;


val qt = ``rule (del x0 (x0::l0) l0) [] :: M``;
val nodel3 = filter (fn x => term_eq ((snd o #board o snd) x) qt) (dlist newtree);


val terml = mk_term_set (map (fn (id,x) => (snd o #board) x) nodel);

val nodel = filter (fn (id,x) => #stati x = Lose) (dlist newtree);
val nodewinl = trace_win newtree [];
val terml = map (snd o #board) nodewinl;

val nodel = filter (fn (id,x) => 
  contain_mvar (#3 (#board x)) andalso 
  #stati x = Lose) 
  (dlist newtree);

val nodel = filter (fn (id,x) => not (pretest_qt (#3 (#board x))))
  (dlist newtree);


fun is_looping 
  delete (a,b,c) <= delete (a,b,c)
case delete (a,[b,c],y) of
  delete (x1,l1,l2) <= delete (x1,l2,l1)
clause can (no match) (loop)
*)

(*
(* -------------------------------------------------------------------------
   Parallelization
   ------------------------------------------------------------------------- *)

fun write_boardl file boardl =  export_terml (file ^ "_qt") boardl
fun read_boardl file = import_terml (file ^ "_qt")
val gameio = {write_boardl = write_boardl, read_boardl = read_boardl}

(* -------------------------------------------------------------------------
   Targets
   ------------------------------------------------------------------------- *)

val targetdir = selfdir ^ "/SML_target"

fun create_targetl l =
  let
    val (train,test) = part_pct (10.0/11.0) (shuffle l)
    val _ = export_data (train,test)
    fun f (headnf,combin) = (V1, headnf, 2 * combin_size combin)
  in
    (dict_sort fullboard_compare (map f train),
     dict_sort fullboard_compare (map f test))
  end

fun export_targetl name targetl =
  let val _ = mkDir_err targetdir in
    write_boardl (targetdir ^ "/" ^ name) targetl
  end

fun import_targetl name = read_boardl (targetdir ^ "/" ^ name)

fun mk_targetd l1 =
  let
    val l2 = number_snd 0 l1
    val l3 = map (fn (x,i) => (x,(i,[]))) l2
  in
    dnew board_compare l3
  end

(* -------------------------------------------------------------------------
   Neural network representation of the board
   ------------------------------------------------------------------------- *)

val head_eval = mk_var ("head_eval", ``:'a list -> 'a``)
val head_poli = mk_var ("head_poli", ``:'a list -> 'a``)
fun tag_heval x = mk_comb (head_eval,x)
fun tag_hpoli x = mk_comb (head_poli,x)

fun tob1 tm = [tag_heval tm, tag_hpoli tm]

fun pretob boardtnno = case boardtnno of
    NONE => tob1
  | SOME (t,tnn) => tob1

(* -------------------------------------------------------------------------
   Player
   ------------------------------------------------------------------------- *)

val schedule =
  [{ncore = 4, verbose = true, learning_rate = 0.02,
    batch_size = 16, nepoch = 10}]

val dim = 16
fun dim_head_poli n = [dim,n]
val tnndim = map_assoc (dim_std (1,dim)) (operl @ mvarl) @
  [(head_eval,[dim,dim,1]),(head_poli,[dim,dim,length movel])]

val dplayer = {pretob = pretob, tnndim = tnndim, schedule = schedule}

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

val rlparam =
  {expname = "mleSMLSynt", exwindow = 200000,
   ncore = 30, ntarget = 200, nsim = 32000, decay = 1.0}

val rlobj : (board,move) rlobj =
  {rlparam = rlparam, game = game, gameio = gameio, dplayer = dplayer,
   infobs = fn _ => ()}

val extsearch = mk_extsearch "mleSMLSynt.extsearch" rlobj
*)




end (* struct *)
