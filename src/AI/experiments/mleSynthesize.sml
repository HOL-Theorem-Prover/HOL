(* ========================================================================= *)
(* FILE          : mleSynthesize.sml                                         *)
(* DESCRIPTION   : Specification of a term copying game                      *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mleSynthesize :> mleSynthesize =
struct

open HolKernel Abbrev boolLib aiLib psMCTS psTermGen 
  mlTreeNeuralNetwork mlTacticData smlParallel

val ERR = mk_HOL_ERR "mleSynthesize"

(* -------------------------------------------------------------------------
   Board
   ------------------------------------------------------------------------- *)

type board = ((term * int) * term)

val active_var = ``active_var:num``;

fun mk_startsit tm = 
  (true,((tm,mleArithData.eval_numtm tm),active_var))
fun dest_startsit (_,((tm,_),_)) = tm

fun is_ground tm = not (tmem active_var (free_vars_lr tm))

val operl = [(active_var,0)] @ operl_of ``SUC 0 + 0 = 0 * 0``
fun nntm_of_sit (_,((ctm,_),tm)) = mk_eq (ctm,tm)

fun status_of (_,((ctm,n),tm)) = 
  let val ntm = mk_sucn n in
    if term_eq ntm tm then Win
    else if is_ground tm orelse term_size tm > 2 * n then Lose
    else Undecided
  end
 
(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

type move = (term * int)
val movel = operl_of ``SUC 0``
val move_compare = cpl_compare Term.compare Int.compare

fun action_oper (oper,n) tm =
  let
    val res = list_mk_comb (oper, List.tabulate (n, fn _ => active_var)) 
    val sub = [{redex = active_var, residue = res}]
  in
    subst_occs [[1]] sub tm
  end

fun apply_move move (_,(ctmn,tm)) = (true, (ctmn, action_oper move tm))

fun mk_targetl level ntarget = 
  let 
    val tml = mlTacticData.import_terml 
      (HOLDIR ^ "/src/AI/experiments/data200_train_evalsorted")
    val tmll = map shuffle (first_n level (mk_batch 400 tml))
    val tml2 = List.concat (list_combine tmll)
  in  
    map mk_startsit (first_n ntarget tml2)
  end

fun filter_sit sit = (fn l => l) (* filter moves *)

fun string_of_move (tm,_) = tts tm

fun write_targetl targetl = 
  let val tml = map dest_startsit targetl in 
    export_terml (!parallel_dir ^ "/targetl") tml
  end

fun read_targetl () =
  let val tml = import_terml (!parallel_dir ^ "/targetl") in
    map mk_startsit tml
  end  

fun max_bigsteps target = 2 * term_size (dest_startsit target) + 1

(* -------------------------------------------------------------------------
   Interface
   ------------------------------------------------------------------------- *)

val gamespec : (board,move) mlReinforce.gamespec =
  {
  movel = movel,
  move_compare = move_compare,
  status_of = status_of,
  filter_sit = filter_sit,
  apply_move = apply_move,
  operl = operl,
  nntm_of_sit = nntm_of_sit,
  mk_targetl = mk_targetl,
  write_targetl = write_targetl,
  read_targetl = read_targetl,
  string_of_move = string_of_move,
  opens = "mleSynthesize",
  max_bigsteps = max_bigsteps
  }

(* 
load "mlReinforce"; open mlReinforce;
load "mleSynthesize"; open mleSynthesize;
load "mleArithData"; open mleArithData;

val tml = mlTacticData.import_terml 
  (HOLDIR ^ "/src/AI/experiments/data200_train_evalsorted");
val tmll = map (list_imax o map eval_numtm) (mk_batch 400 tml);
*)


(* statistics
load "mleArithData"; open mleArithData;
load "mlTacticData"; open mlTacticData;
load "aiLib"; open aiLib;

fun write_graph file (s1,s2) l =
  writel file ((s1 ^ " " ^ s2) :: map (fn (a,b) => its a ^ " " ^ its b) l);
fun synt_stats file =
  let
    val l0 = import_terml file
    val l1 = map (fn x => (x,eval_numtm x)) l0;
    val l1' = filter (fn x => snd x <= 100) l1; 
    val _  = print_endline (its (length l1'));
    val l2 = dlist (dregroup Int.compare (map swap l1'));
  in
    map_snd length l2 
  end;

val data_in = HOLDIR ^ "/src/AI/experiments";
val data_out = "/home/thibault/prague-server/papers/2019-05-NIPS/data";

val stats1 = synt_stats (data_in ^ "/data200_train");
write_graph (data_out ^ "/synt_train") ("csize","total") stats1;
val stats2 = synt_stats (data_in ^ "/data200_valid");
write_graph (data_out ^ "/synt_valid") ("csize","total") stats2;
val stats3 = synt_stats (data_in ^ "/data200_test");
write_graph (data_out ^ "/synt_test") ("csize","total") stats3;
val stats4 = synt_stats (data_in ^ "/data200_big");
write_graph (data_out ^ "/synt_big") ("csize","total") stats4;

10933, 9669, 9030, 22048
*)


(* basic test
load "mlReinforce"; open mlReinforce;
load "mleSynthesize"; open mleSynthesize;

val file = 
HOLDIR ^ "/src/AI/machine_learning/eval/may21_synthesize_gen3_dhtnn";
val dhtnn = mlTreeNeuralNetwork.read_dhtnn file;
nsim_glob := 1600;
explore_test gamespec final_dhtnn (mk_startsit ``SUC 0 * SUC 0``);
*)

(* starting examples
load "mlReinforce"; open mlReinforce;
load "mleSynthesize"; open mleSynthesize;
load "mleArithData"; open mleArithData;
load "mlTacticData"; open mlTacticData;
open aiLib;

val traintml = import_terml (HOLDIR ^ "/src/AI/experiments/data200_train");
val trainpl1 = map (fn x => (x, eval_numtm x)) traintml;
val trainpl1' = filter (fn x => snd x <= 100) trainpl1;
val trainpl2 = dict_sort compare_imin trainpl1';
export_terml (HOLDIR ^ "/src/AI/experiments/data200_train_evalsorted") 
  (map fst trainpl2);

val validtml = import_terml (HOLDIR ^ "/src/AI/experiments/data200_valid");
val validpl1 = map (fn x => (x, eval_numtm x)) validtml;
val validpl1' = filter (fn x => snd x <= 100) validpl1;
val validpl2 = dict_sort compare_imin validpl1';
export_terml (HOLDIR ^ "/src/AI/experiments/data200_valid_evalsorted") 
  (map fst validpl2);
*)


(* reinforcement learning loop
load "mlReinforce"; open mlReinforce;
load "mleSynthesize"; open mleSynthesize;
open smlParallel;

logfile_glob := "synthesize_run2";
parallel_dir := HOLDIR ^ "/src/AI/sml_inspection/parallel_" ^ (!logfile_glob);
ncore_mcts_glob := 8;
ncore_train_glob := 4;

ntarget_compete := 400;
ntarget_explore := 400;
exwindow_glob := 40000;
uniqex_flag := false;
dim_glob := 12;
lr_glob := 0.02;
batchsize_glob := 16;
decay_glob := 0.99;
level_glob := 1;

nsim_glob := 1600;
nepoch_glob := 100;
ngen_glob := 100;

val (final_epex,final_dhtnn) = start_rl_loop gamespec;
*)





end (* struct *)
