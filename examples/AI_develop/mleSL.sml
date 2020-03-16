(* ========================================================================= *)
(* FILE          : mleSL.sml                                                 *)
(* DESCRIPTION   : Supervised learning as a reinforcement learning game      *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2020                                                      *)
(* ========================================================================= *)

structure mleSL :> mleSL =
struct

open HolKernel Abbrev boolLib aiLib smlParallel psMCTS psTermGen
  mlNeuralNetwork mlTreeNeuralNetwork

val ERR = mk_HOL_ERR "mleSL"
val selfdir = HOLDIR ^ "/examples/AI_develop"

(* -------------------------------------------------------------------------
   Fixed dataset and initialization
   ------------------------------------------------------------------------- *)

val vx = mk_var ("x",alpha)
val vy = mk_var ("y",alpha)
val vz = mk_var ("z",alpha)
val vf = ``f:'a->'a->'a``
val vg = ``g:'a -> 'a``
val vhead = mk_var ("head_", ``:'a -> 'a``)
val varl = [vx,vy,vz,vf,vg]

(* examples *)
fun contain_x tm = can (find_term (fn x => term_eq x vx)) tm;
fun mk_dataset n =
  let
    val pxl = mk_term_set (random_terml varl (n,alpha) 1000);
    val (px,pnotx) = partition contain_x pxl
  in
    (first_n 20 (shuffle px), first_n 20 (shuffle pnotx))
  end
val (l1,l2) = split (List.tabulate (20, fn n => mk_dataset (n + 1)))
val (l1',l2') = (List.concat l1, List.concat l2)
val (pos,neg) = 
  (map_assoc (fn x => [1.0]) l1', map_assoc (fn x => [0.0]) l2')
val train = map ( fn (a,b) => [(mk_comb (vhead,a),b)] ) (shuffle (pos @ neg))
val _ = print_endline (stats_tnnex train)
val prebatch = prepare_tnnex train

(* initialization *)
val bsizestart = 16
val boardstart =
  let 
    val trainparam =
      {ncore = 1, verbose = true,
       learning_rate = 0.02, batch_size = bsizestart, nepoch = 1}
    val randtnn = random_tnn_std (1,16) (vhead :: varl); 
    val batchl = mk_batch bsizestart prebatch
    val (newtnn,loss) = train_tnn_epoch_nopar trainparam [] randtnn batchl
  in
    (newtnn,[(loss,bsizestart)])
  end

(* -------------------------------------------------------------------------
   Board: tnn + list of losses
   ------------------------------------------------------------------------- *)

type board = tnn * (real * int) list 
fun string_of_board (_,rl) = 
  String.concatWith " " (map (rts o fst) rl) ^ "\n" ^
  String.concatWith " " (map (its o snd) rl) ^ "\n"

fun board_compare ((_,rl1),(_,rl2)) = 
  list_compare Int.compare (map snd rl1, map snd rl2)
fun status_of (_,rl) = Undecided

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

datatype move = Incr | Decr | Still
val movel = [Incr,Decr,Still]

fun string_of_move move = case move of
    Incr => "Incr"
  | Decr => "Decr"
  | Still => "Still"

fun move_compare (m1,m2) =
  String.compare (string_of_move m1, string_of_move m2)

fun calc_newbsize move bsize = case move of
    Incr => let val r = Real.round (Real.fromInt bsize * 1.1) in
              if r = bsize then r + 1 else r
            end
  | Decr => let val r = Real.round (Real.fromInt bsize * 0.90909) in
              if r = bsize then r - 1 else r
            end
  | _ => bsize

fun apply_move move (tnn,rl) =
  let 
    val bsize1 = snd (hd rl)
    val bsize2 = calc_newbsize move bsize1
    val bsize3 = if bsize2 <= 1 then 1 else bsize2
    val bsize4 = if bsize3 >= 512 then 512 else bsize3
    val trainparam =
      {ncore = 1, verbose = true,
       learning_rate = 0.02, batch_size = bsize4, nepoch = 1}
    val batchl = mk_batch bsize4 prebatch
    val (newtnn,loss) = train_tnn_epoch_nopar trainparam [] tnn batchl
    (* val _ = print_endline (its bsize4 ^ " " ^ rts loss) *)
    val newrl = (loss,bsize4) :: rl
  in
    (newtnn,newrl)
  end

fun available_movel (_,rl) = movel

(* -------------------------------------------------------------------------
   Game
   ------------------------------------------------------------------------- *)

val game : (board,move) game =
  {
  status_of = status_of,
  available_movel = available_movel,
  apply_move = apply_move,
  string_of_board = string_of_board,
  string_of_move = string_of_move,
  board_compare = board_compare,
  move_compare = move_compare,
  movel = movel
  }

(* -------------------------------------------------------------------------
   Player
   ------------------------------------------------------------------------- *)

fun loss_player (tnn,rl) =
  (1.0 - fst (hd rl), map (fn x => (x,1.0)) (available_movel (tnn,rl)))

(* -------------------------------------------------------------------------
   MCTS test for manual inspection
   ------------------------------------------------------------------------- *)

(*
load "aiLib"; open aiLib;
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;
load "psMCTS"; open psMCTS;
load "psBigSteps"; open psBigSteps;
load "mleSL"; open mleSL;

val mctsparam =
  {
  timer = NONE,
  nsim = SOME 160,
  stopatwin_flag = false,
  decay = 1.0,
  explo_coeff = 2.0,
  noise_all = false,
  noise_root = false,
  noise_coeff = 0.25,
  noise_gen = random_real,
  noconfl = false,
  avoidlose = false
  };

val mctsobj = {game = game, mctsparam = mctsparam, player = loss_player};
val tree = psMCTS.starttree_of mctsobj boardstart;
val (newtree,_) = mcts mctsobj tree;
val idl = mostexplored_path newtree [];
val nodel = map (fn x => dfind x newtree) idl;

val bsobj : (board,move) psBigSteps.bsobj =
  {
  verbose = true,
  temp_flag = false,
  preplayer = fn _ => loss_player,
  game = game,
  mctsparam = mctsparam
  };
val (a,b,c) = run_bigsteps bsobj boardstart;


*)

end (* struct *)
