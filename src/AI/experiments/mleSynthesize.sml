(* ========================================================================= *)
(* FILE          : mleSynthesize.sml                                         *)
(* DESCRIPTION   : Specification of a term synthesis game                    *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mleSynthesize :> mleSynthesize =
struct

open HolKernel Abbrev boolLib aiLib smlParallel psMCTS psTermGen
  mlTreeNeuralNetwork mlTacticData mlReinforce mleLib mleArithData

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

val synt_operl = [(active_var,0)] @ operl_of ``SUC 0 + 0 = 0 * 0``
fun nntm_of_sit (_,((ctm,_),tm)) = mk_eq (ctm,tm)

fun status_of (_,((ctm,n),tm)) =
  let val ntm = mk_sucn n in
    if term_eq ntm tm then Win
    else if is_ground tm orelse term_size tm > 2 * n + 1 then Lose
    else Undecided
  end

(* -------------------------------------------------------------------------
   Move
   ------------------------------------------------------------------------- *)

type move = (term * int)
val movel = operl_of ``SUC 0``;
val move_compare = cpl_compare Term.compare Int.compare

fun action_oper (oper,n) tm =
  let
    val res = list_mk_comb (oper, List.tabulate (n, fn _ => active_var))
    val sub = [{redex = active_var, residue = res}]
  in
    subst_occs [[1]] sub tm
  end

fun apply_move move (_,(ctmn,tm)) = (true, (ctmn, action_oper move tm))


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
   Level
   ------------------------------------------------------------------------- *)

fun create_train_evalsorted () =
  let
    val filein = dataarith_dir ^ "/train"
    val fileout = dataarith_dir ^ "/train_evalsorted"
    val l1 = import_terml filein ;
    val l2 = map (fn x => (x, eval_numtm x)) l1
    val l3 = filter (fn x => snd x <= 100) l2
    val l4 = dict_sort compare_imin l3
  in
    export_terml fileout (map fst l4)
  end

fun mk_targetl level ntarget =
  let
    val tml = mlTacticData.import_terml (dataarith_dir ^ "/train_evalsorted")
    val tmll = map shuffle (first_n level (mk_batch 400 tml))
    val tml2 = List.concat (list_combine tmll)
  in
    map mk_startsit (first_n ntarget tml2)
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
  operl = synt_operl,
  nntm_of_sit = nntm_of_sit,
  mk_targetl = mk_targetl,
  write_targetl = write_targetl,
  read_targetl = read_targetl,
  string_of_move = string_of_move,
  opens = "mleSynthesize",
  max_bigsteps = max_bigsteps
  }

(* -------------------------------------------------------------------------
   Statistics
   ------------------------------------------------------------------------- *)

fun maxeval_atgen () =
  let
    val tml = mlTacticData.import_terml (dataarith_dir ^ "/train_evalsorted")
  in
    map (list_imax o map eval_numtm) (mk_batch 400 tml)
  end

fun stats_eval file =
  let
    val l0 = import_terml file
    val l1 = map (fn x => (x,eval_numtm x)) l0;
    val l1' = filter (fn x => snd x <= 100) l1;
    val _  = print_endline (its (length l1'));
    val l2 = dlist (dregroup Int.compare (map swap l1'));
  in
    map_snd length l2
  end

(* -------------------------------------------------------------------------
   Basic exploration
   ------------------------------------------------------------------------- *)

fun explore_gamespec tm =
  let val dhtnn = random_dhtnn_gamespec gamespec in
    explore_test gamespec dhtnn (mk_startsit tm)
  end

(* -------------------------------------------------------------------------
   Reinforcement learning loop with fixed parameters
   ------------------------------------------------------------------------- *)

fun reinforce_fixed runname ngen =
  (
  logfile_glob := runname;
  parallel_dir := HOLDIR ^ "/src/AI/sml_inspection/parallel_" ^
  (!logfile_glob);
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
  ngen_glob := ngen;
  start_rl_loop gamespec
  )

(* -------------------------------------------------------------------------
   Final evaluation
   ------------------------------------------------------------------------- *)

fun final_eval dhtnn_name (a,b) testbase =
  let
    val eval_dir = HOLDIR ^ "/src/AI/machine_learning/eval"
    val file = eval_dir ^ "/" ^ dhtnn_name
    val dhtnn = mlTreeNeuralNetwork.read_dhtnn file
    val l1 = import_terml (dataarith_dir ^ "/" ^ testbase)
    val l2 = map (fn tm => (tm,eval_numtm tm)) l1
    val l3 = filter (fn x => snd x >= a andalso snd x <= b) l2
    val nwin = compete_one gamespec dhtnn (map mk_startsit (map fst l3))
    val ntot = length l3
  in
    ((nwin,ntot), int_div nwin ntot)
  end

(*
load "mleSynthesize"; open mleSynthesize;
load "mlReinforce"; open mlReinforce;
ncore_mcts_glob := 40;
val dhtnn_name = "synthesize_run3_gen42_dhtnn";
fun eval nsim =
  (
  nsim_glob := nsim;
    (
    final_eval dhtnn_name (0,16) "test",
    final_eval dhtnn_name (16,32) "test",
    final_eval dhtnn_name (0,16) "big",
    final_eval dhtnn_name (16,32) "big"
    )
  );
val rltest = eval 1;
val rl = map eval [1,16,160,1600];
*)

end (* struct *)
