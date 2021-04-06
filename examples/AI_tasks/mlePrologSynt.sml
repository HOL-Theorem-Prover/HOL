(* ========================================================================= *)
(* FILE          : mlePrologSynt.sml                                         *)
(* DESCRIPTION   : Specification of term synthesis on combinator datatype    *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2020                                                      *)
(* ========================================================================= *)

structure mlePrologSynt :> mlePrologSynt =
struct

open HolKernel Abbrev boolLib aiLib smlParallel psMCTS psTermGen
  mlNeuralNetwork mlTreeNeuralNetwork mlTacticData
  mlReinforce mlePrologLib

val ERR = mk_HOL_ERR "mlePrologSynt"
val selfdir = HOLDIR ^ "/examples/AI_tasks"

(* -------------------------------------------------------------------------
   Metavar
   ------------------------------------------------------------------------- *)

fun is_mvar x = is_var x andalso "M" = fst (dest_var x)
fun contain_mvar tm = can (find_term is_mvar) tm
fun first_mvar tm = find_term is_mvar tm
fun mk_mvar ty = mk_var ("M",ty)

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = (term * term) list * term
fun string_of_board board = tts (snd board)
val board_compare = snd_compare Term.compare

fun status_of (board as (ex,qt)) =
  if not (contain_mvar qt) 
    then if test_board board then Win else Lose
  else 
    if term_size qt > 31 then Lose else Undecided

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

type move = (term,term) subst

fun mk_subst oper =
  let 
    val (domtyl,imty) = strip_type (type_of oper) 
    val res = list_mk_comb (oper, map mk_mvar domtyl)
  in
    [{redex = mk_mvar imty, residue = res}]
  end

val movel = map mk_subst operl

fun string_of_move m = tts (#residue (hd m))
fun move_compare (m1,m2) = Term.compare (#residue (hd m1),#residue (hd m2))
  
fun apply_move (tree,id) move (ex,qt) =
  ((ex, subst_occs [[1]] move qt), tree)

fun available_movel (_,qt) =
  let val mvar = first_mvar qt in
    filter (fn x => term_eq (#redex (hd x)) mvar) movel  
  end

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

(* 
load "mlePrologSynt"; open mlePrologSynt;
load "mlePrologLib"; open mlePrologLib;
load "psMTCS"; open psMCTS;
load "aiLib"; open aiLib;

val mctsparam =
  {
  timer = SOME 300.0,
  nsim = NONE : int option,
  stopatwin_flag = true,
  decay = 1.0,
  explo_coeff = 2.0,
  noise_all = false,
  noise_root = false,
  noise_coeff = 0.25,
  noise_gen = random_real,
  noconfl = false,
  avoidlose = false,
  evalwin = false
  };

val mctsobj = {game = game, mctsparam = mctsparam,
  player =  psMCTS.random_player game};

val ex = all_ex prog0 (3,4);
val startqt = mk_var ("M",``:'a list``);
val tree = starttree_of mctsobj (ex,startqt);
val (a,(newtree,b)) = mcts mctsobj tree;
val nodel = trace_win (#status_of game) newtree [];


fun is_mvar x = is_var x andalso "M" = fst (dest_var x)
fun contain_mvar tm = can (find_term is_mvar) tm;
val nodel = filter (fn (id,x) => not (contain_mvar (snd (#board x)))) (dlist newtree);
val nodel2 = filter (fn (id,x) => term_size (snd (#board x)) = 29) nodel;
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

val targetdir = selfdir ^ "/prolog_target"

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
  {expname = "mlePrologSynt", exwindow = 200000,
   ncore = 30, ntarget = 200, nsim = 32000, decay = 1.0}

val rlobj : (board,move) rlobj =
  {rlparam = rlparam, game = game, gameio = gameio, dplayer = dplayer,
   infobs = fn _ => ()}

val extsearch = mk_extsearch "mlePrologSynt.extsearch" rlobj
*)

(* -------------------------------------------------------------------------
   Final test
   ------------------------------------------------------------------------- *)



(* pool of solved problems *)

(*
val ft_extsearch_uniform =
  ft_mk_extsearch "mleCombinSynt.ft_extsearch_uniform" rlobj
    (uniform_player game)

val fttnn_extsearch =
  fttnn_mk_extsearch "mleCombinSynt.fttnn_extsearch" rlobj

val fttnnbs_extsearch =
  fttnnbs_mk_extsearch "mleCombinSynt.fttnnbs_extsearch" rlobj
*)

(*
load "aiLib"; open aiLib;
load "mlReinforce"; open mlReinforce;
load "mleCombinLib"; open mleCombinLib;
load "mleCombinSynt"; open mleCombinSynt;

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
load "mleCombinSynt"; open mleCombinSynt;
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
  avoidlose = false,
  evalwin = false
  };

val game = #game rlobj;
val mctsobj = {game = game, mctsparam = mctsparam,
  player =  psMCTS.random_player (#game rlobj)};

val headnf = A(V2,(list_mk_A[V1,V2,V3]));
val target = (V1,headnf,100);
val tree = psMCTS.starttree_of mctsobj target;
val (_,(newtree,_)) = mcts mctsobj tree;
val nodel = trace_win (#status_of game) newtree [];
*)

(* -------------------------------------------------------------------------
   Final testing
   ------------------------------------------------------------------------- *)

(*
load "aiLib"; open aiLib;
load "smlParallel"; open smlParallel;
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;
load "mleCombinSynt"; open mleCombinSynt;

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
load "mleCombinSynt"; open mleCombinSynt;

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
load "mleCombinSynt"; open mleCombinSynt;
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
