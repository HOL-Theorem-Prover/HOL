(* ========================================================================= *)
(* FILE          : mleSL.sml                                                 *)
(* DESCRIPTION   : Supervised learning as a reinforcement learning game      *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2020                                                      *)
(* ========================================================================= *)

structure mleSL :> mleSL =
struct

open HolKernel Abbrev boolLib aiLib smlParallel psMCTS psTermGen
  mlNeuralNetwork mlTreeNeuralNetwork mlTacticData
  mlReinforce mleCombinLib

val ERR = mk_HOL_ERR "mleSL"
val selfdir = HOLDIR ^ "/examples/AI_develop"

(* -------------------------------------------------------------------------
   Fixed dataset and initialization
   ------------------------------------------------------------------------- *)

val vx = mk_var ("x",alpha);
val vy = mk_var ("y",alpha);load "aiLib"; open aiLib;
val vz = mk_var ("z",alpha);
val vf = ``f:'a->'a->'a``;
val vg = ``g:'a -> 'a``;
val vhead = mk_var ("head_", ``:'a -> 'a``);
val varl = [vx,vy,vz,vf,vg];

(* examples *)
fun contain_x tm = can (find_term (fn x => term_eq x vx)) tm;
fun mk_dataset n =
  let
    val pxl = mk_term_set (random_terml varl (n,alpha) 1000);
    val (px,pnotx) = partition contain_x pxl
  in
    (first_n 100 (shuffle px), first_n 100 (shuffle pnotx))
  end
val (l1,l2) = split (List.tabulate (20, fn n => mk_dataset (n + 1)))
val (l1',l2') = (List.concat l1, List.concat l2)
val (pos,neg) = 
  (map_assoc (fn x => [1.0]) l1', map_assoc (fn x => [0.0]) l2')
val train = map ( fn (a,b) => [(mk_comb (vhead,a),b)] ) (shuffle (pos @ neg))
val prebatch = prepare_tnnex train

val bsizestart = 16
val (tnnstart,rlstart) =
  let 
    val trainparam =
      {ncore = 1, verbose = true,
       learning_rate = 0.02, batch_size = bsize_start, nepoch = 1}
    val (newtnn,loss) = train_tnn_epoch_nopar trainparam [] tnn batchl
  in
    (newtnn,[(bsizestart,loss)])
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
fun status_of _ = Undecided

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
    Incr => let val r = Real.round (Real.fromInt (bsize * 1.1)) in
              if r = bsize then r + 1 else r
            end
  | Decr => let val r = Real.round (Real.fromInt (bsize * 0.90909)) in
              if r = bsize then r - 1 else r
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
    val newrl = first_n 32 ((loss,bsize4) :: rl)
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

fun loss_player game (tnn,rl) =
  (1.0 - fst (hd rl), map (fn x => (x,1.0)) (#available_movel game board))


(*
load "aiLib"; open aiLib;
load "mlReinforce"; open mlReinforce;
load "mleCombinLib"; open mleCombinLib;
load "mleSL"; open mleSL;

val (dfull,ntry) = gen_headnf 2200 (dempty combin_compare);
val (train,test) = create_targetl (dlist dfull); length train; length test;
val _ = (export_targetl "train" train; export_targetl "test" test);

val targetl = import_targetl "train";
val r = rl_start (rlobj,extsearch) (mk_targetd targetl);

val targetd = retrieve_targetd rlobj 83;
val _ = rl_restart 83 (rlobj,extsearch) targetd;
*)

(* -------------------------------------------------------------------------
   MCTS test for manual inspection
   ------------------------------------------------------------------------- *)

(*
load "aiLib"; open aiLib;
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;
load "mleCombinLib"; open mleCombinLib;
load "mleSL"; open mleSL;
load "mlReinforce"; open mlReinforce;

val mctsparam =
  {
  timer = SOME 60.0,
  nsim = NONE,
  stopatwin_flag = true,
  decay = 1.0,
  explo_coeff = 2.0,
  noise_all = false,
  noise_root = false,
  noise_coeff = 0.25,
  noise_gen = random_real,
  noconfl = false,
  avoidlose = false
  };

val game = #game rlobj;
val mctsobj = {game = game, mctsparam = mctsparam,
  player =  psMCTS.random_player (#game rlobj)};

val headnf = A(V2,(list_mk_A[V1,V2,V3]));
val target = (V1,headnf,100);
val tree = psMCTS.starttree_of mctsobj target;
val (newtree,_) = mcts mctsobj tree;
val nodel = trace_win (#status_of game) newtree [];
*)

(* -------------------------------------------------------------------------
   Final testing
   ------------------------------------------------------------------------- *)

(*
load "aiLib"; open aiLib;
load "smlParallel"; open smlParallel;
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;
load "mleSL"; open mleSL;

val dir1 = HOLDIR ^ "/examples/AI_tasks/combin_results";
val _ = mkDir_err dir1;
fun store_result dir (a,i) =
  #write_result ft_extsearch_uniform (dir ^ "/" ^ its i) a;

(*** Test ***)
val dataset = "test";
val pretargetl = import_targetl dataset;
val targetl = map (fn (a,b,_) => (a,b,1000000)) pretargetl;
length targetl;
(* uniform *)
val (l1',t) =
  add_time (parmap_queue_extern 20 ft_extsearch_uniform ()) targetl;
val winb = filter I (map #1 l1'); length winb;
val dir2 = dir1 ^ "/" ^ dataset ^ "_uniform";
val _ = mkDir_err dir2; app (store_result dir2) (number_snd 0 l1');
(* tnn *)
val tnn = mlReinforce.retrieve_tnn rlobj 318;
val (l2',t) = add_time (parmap_queue_extern 20 fttnn_extsearch tnn) targetl;
val winb = filter I (map #1 l2'); length winb;
val dir2 = dir1 ^ "/" ^ dataset ^ "_tnn";
val _ = mkDir_err dir2; app (store_result dir2) (number_snd 0 l2');

(*** Train ***)
val dataset = "train";
val pretargetl = import_targetl dataset;
val targetl = map (fn (a,b,_) => (a,b,1000000)) pretargetl;
length targetl;
(* uniform *)
val (l1,t) = add_time (parmap_queue_extern 20 ft_extsearch_uniform ()) targetl;
val winb = filter I (map #1 l1); length winb;
val dir2 = dir1 ^ "/" ^ dataset ^ "_uniform";
val _ = mkDir_err dir2; app (store_result dir2) (number_snd 0 l1);
(* tnn *)
val tnn = mlReinforce.retrieve_tnn rlobj 318;
val (l2,t) = add_time (parmap_queue_extern 20 fttnn_extsearch tnn) targetl;
val winb = filter I (map #1 l2); length winb;
val dir2 = dir1 ^ "/" ^ dataset ^ "_tnn";
val _ = mkDir_err dir2; app (store_result dir2) (number_snd 0 l2);
*)

(* -------------------------------------------------------------------------
   Final testing statistics
   ------------------------------------------------------------------------- *)

(*
load "aiLib"; open aiLib;
load "mleCombinLib"; open mleCombinLib;
load "mleSL"; open mleSL;

val dir2 = HOLDIR ^ "/examples/AI_tasks/combin_results/test_tnn_nolimit";
fun g i = #read_result ft_extsearch_uniform (dir2 ^ "/" ^ its i);
val l1 = List.tabulate (200,g);
val dir2 = HOLDIR ^ "/examples/AI_tasks/combin_results/train_tnn";
fun g i = #read_result ft_extsearch_uniform (dir2 ^ "/" ^ its i);
val l2 = List.tabulate (2000,g);

val (l3,l3') = partition #1 (l1 @ l2);
val nsim_tnn = average_int (map #2 l3'); 
last (dict_sort Int.compare (map #2 l3'));

val l4 = map (valOf o #3) l3;
val l5 = map (fn (a,b,c) => (ignore_metavar a,b)) l4;
val l6 = map_assoc (combin_size o fst) l5;
val l7 = dict_sort compare_imax l6;
val ((a,b),c) = hd l7;
combin_to_string a; 
combin_to_string b;

val l5 = map (fn (a,b,c) => ignore_metavar a) l4;
val l6 = map combin_to_cterm l5;
fun all_subtm t = find_terms (fn x => type_of x = alpha) t;
val l7 = List.concat (map all_subtm l6);
val l8 = dlist (count_dict (dempty Term.compare) l7);
val l9 = dict_sort compare_imax l8;
val l10 = map_fst (combin_to_string o cterm_to_combin) 
    (first_n 100 l9);

val d = dnew combin_compare (map (fn (a,b,c) => (b, ignore_metavar a)) l4);
val combin = dfind (list_mk_A [V1,V3,V2]) d;

val longest = 
  let fun cmp (a,b) = Int.compare (#2 b, #2 a) in
    dict_sort cmp l3
  end;

val (a,b,c) = valOf (#3 (hd longest));
combin_to_string (ignore_metavar a); 
combin_to_string  b;


val monol = List.concat (map numSyntax.strip_plus l5);
val monofreq = dlist (count_dict (dempty Term.compare) monol);
val monostats = dict_sort compare_imax monofreq;

val dir2 = HOLDIR ^ "/examples/AI_tasks/combin_results/test_uniform";
fun g i = #read_result ft_extsearch_uniform (dir2 ^ "/" ^ its i);
val l1 = List.tabulate (200,g);
val dir2 = HOLDIR ^ "/examples/AI_tasks/combin_results/train_uniform";
fun g i = #read_result ft_extsearch_uniform (dir2 ^ "/" ^ its i);
val l2 = List.tabulate (2000,g);

val (l3,l3') = partition #1 (l1 @ l2);
val nsim_uniform = average_int (map #2 l3');
*)

(* -------------------------------------------------------------------------
   Training graph
   ------------------------------------------------------------------------- *)

(*
load "aiLib"; open aiLib;
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;
load "mleCombinLib"; open mleCombinLib;
load "mleSL"; open mleSL;
load "mlReinforce"; open mlReinforce;

val targetd = retrieve_targetd rlobj 100;

val targetdl = List.tabulate (319, 
  fn x => mlReinforce.retrieve_targetd rlobj (x+1));
val l1 = map dlist targetdl;
val l2 = map (map (snd o snd)) l1;

fun btr b = if b then 1.0 else 0.0 

fun expectancy_one bl = 
  if null bl then 0.0 else average_real (map btr (first_n 5 bl))
fun expectancy bll = sum_real (map expectancy_one bll);
val expectl = map expectancy l2;

fun exists_one bl = btr (exists I bl);
fun existssol bll = sum_real (map exists_one bll);
val esoll = map existssol l2;

val graph = number_fst 0 (combine (expectl,esoll));
fun graph_to_string (i,(r1,r2)) = its i ^ " " ^ rts r1 ^ " " ^ rts r2;
writel "combin_graph" ("gen exp sol" :: map graph_to_string graph);

*)



end (* struct *)
