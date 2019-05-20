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
    else if term_size tm > 2 * term_size ntm orelse is_ground tm then Lose
    else Undecided
  end
 
(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

type move = (term * int)
val movel = operl_of ``SUC 0 + 0 * 0``
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
  in  
    map mk_startsit (first_n (level * 400) tml) 
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
  opens = "mleSynthesize"
  }

(* 
load "mlReinforce"; open mlReinforce;
load "mleSynthesize"; open mleSynthesize;

val dhtnn = random_dhtnn_gamespec gamespec;
psMCTS.exploration_coeff := 2.0;
nsim_glob := 100000;
explore_test gamespec dhtnn (mk_startsit ``SUC 0 * SUC 0``);
*)

(* starting examples
load "mlReinforce"; open mlReinforce;
load "mleSynthesize"; open mleSynthesize;
load "mleArithData"; open mleArithData;
load "mlTacticData"; open mlTacticData;
open aiLib;

val traintml = import_terml (HOLDIR ^ "/src/AI/experiments/data200_train");
val trainpl1 = mapfilter (fn x => (x, eval_numtm x)) traintml;
val trainpl2 = dict_sort compare_imin trainpl1;
export_terml (HOLDIR ^ "/src/AI/experiments/data200_train_evalsorted") 
  (map fst trainpl2);

val validtml = import_terml (HOLDIR ^ "/src/AI/experiments/data200_valid");
val validpl1 = mapfilter (fn x => (x, eval_numtm x)) validtml;
val validpl2 = dict_sort compare_imin validpl1;
export_terml (HOLDIR ^ "/src/AI/experiments/data200_valid_evalsorted") 
  (map fst validpl2);
*)


(*
load "mlReinforce"; open mlReinforce;
load "mleSynthesize"; open mleSynthesize;
open smlParallel;

logfile_glob := "may20_synthesize_test";
parallel_dir := 
  HOLDIR ^ "/src/AI/sml_inspection/parallel_" ^ (!logfile_glob);
ncore_mcts_glob := 4;
ncore_train_glob := 2;
ngen_glob := 20;
ntarget_compete := 100;
ntarget_explore := 100;
exwindow_glob := 40000;
uniqex_flag := false;
dim_glob := 6;
batchsize_glob := 16;
nepoch_glob := 20;
lr_glob := 0.1;
nsim_glob := 1600;
decay_glob := 0.99;
level_glob := 1;
psMCTS.exploration_coeff := 2.0; (* need to reflect to workers *)

val epex = rl_startex gamespec;
mlTreeNeuralNetwork.write_dhex 
  (HOLDIR ^ "/src/AI/experiments/mleSynthesize_startex") epex;
*)

(* Synthesize experiment
app load ["mlTune","mleSynthesize"];
open aiLib smlParallel mlTreeNeuralNetwork mlTune mleSynthesize;

val epex = read_dhex 
  (HOLDIR ^ "/src/AI/experiments/mleSynthesize_startex");
fun init () = write_dhex ((!parallel_dir) ^ "/epex") epex;

load "mlReinforce"; open mlReinforce;
dim_glob := 16;
val dl = [16];
val nl = [10];
val bl = [16];
val ll = [10];
val yl = [2];
fun codel_of wid = 
  dhtune_codel_of mleSynthesize.gamespec (dl,nl,bl,ll,yl) 1 wid;
val paraml = grid_param (dl,nl,bl,ll,yl);

val ncore = 1;
val (final1,t) = add_time 
  (parmap_queue_extern ncore codel_of (init,dhtune_collect_result)) paraml;

*)





end (* struct *)
