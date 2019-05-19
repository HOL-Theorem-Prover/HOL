(* ========================================================================= *)
(* FILE          : mlTune.sml                                                *)
(* DESCRIPTION   : Auto-tune for machine learning parameters and examples    *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mlTune :> mlTune =
struct

open HolKernel Abbrev boolLib aiLib mlTreeNeuralNetwork smlParallel

val ERR = mk_HOL_ERR "mlTune"

(* -------------------------------------------------------------------------
   Tuning parameters
   ------------------------------------------------------------------------- *)

type ml_param = 
  {dim: int, nepoch: int, 
   batchsize: int, learningrate: real, momentum: real}

fun grid_param (dl,nl,bl,ll,ml) = 
  let 
    val l1 = cartesian_productl [dl,nl,bl,ll,ml]
    val l2 = map quintuple_of_list l1
    fun f (d,n,b,l,m) = {dim=d,nepoch=n,batchsize=b,
      learningrate=int_div 1 l, momentum=int_div m 10}
  in
    map f l2
  end

fun write_param_results file prl =
  let fun f ({batchsize,dim,learningrate,momentum,nepoch},r) =
    rts r ^
    ", batchsize " ^ its batchsize ^
    ", dim " ^ its dim ^
    ", learningrate " ^ rts learningrate ^
    ", momentum " ^ rts momentum  ^ 
    ", nepoch " ^ its nepoch 
  in
    writel file (map f prl)
  end

(* -------------------------------------------------------------------------
   I/O
   ------------------------------------------------------------------------- *)

fun param_file (wid,job) =
  (!parallel_dir ^ "/" ^ its wid ^ "/param" ^ its job)

fun accuracy_file (wid,job) =
  (!parallel_dir ^ "/" ^ its wid ^ "/accuracy" ^ its job)


fun write_param file {dim,nepoch,batchsize,learningrate,momentum} =
  let 
    val sl = 
    [its dim, its nepoch, its batchsize, rts learningrate, rts momentum]
  in
    writel file sl
  end
fun read_param file =
  let val (d,n,b,l,m) = quintuple_of_list (readl file) in
    {dim = string_to_int d, 
     nepoch = string_to_int n, 
     batchsize = string_to_int b, 
     learningrate= valOf (Real.fromString l), 
     momentum = valOf (Real.fromString m)}
  end

fun write_accuracy file r = writel file [rts r]
fun read_accuracy file = valOf (Real.fromString (hd (readl file)))

(* -------------------------------------------------------------------------
   Train with parameters
   ------------------------------------------------------------------------- *)

fun train_tnn_param (wid,job) ncore operl (train,test) 
  (param as {dim,nepoch,batchsize,learningrate,momentum})=
  let 
    val randtnn = random_tnn (dim,4) operl
    val schedule = [(nepoch, learningrate /  (Real.fromInt batchsize))]
    val tnn = prepare_train_tnn (ncore,batchsize) randtnn (train,test) schedule
    val r = accuracy_set tnn test
    val fileparam = param_file (wid,job)
    val fileaccuracy = accuracy_file (wid,job)
  in
    write_param fileparam param;
    write_accuracy fileaccuracy r;
    writel_atomic (widout_file wid) ["done"]
  end

(* -------------------------------------------------------------------------
   External parallelization   
   ------------------------------------------------------------------------- *)

fun tune_codel_of ncore_loc wid = 
  [
   "open mlTreeNeuralNetwork mlTune smlParallel;",
   "(* generating f *)",
   "val dir = " ^ quote (!parallel_dir) ^ ";",
   "val ncore = " ^ its ncore_loc ^ ";",
   "val operl = read_operl (dir ^ \"/operl\");",
   "val (train,test) = ",
   "  (read_tnnex (dir ^ \"/train\"), read_tnnex (dir ^ \"/test\"));",
   "fun f (wid,job) param =", 
   "  train_tnn_param (wid,job) ncore operl (train,test) param;",
   "(* generating jobs *)",
   "val dl = [16,8];",
   "val nl = [100,200];",
   "val bl = [16,128];",
   "val ll = [10,100];",
   "val ml = [0,9];",
   "val l = grid_param (dl,nl,bl,ll,ml);",
   "worker_start " ^ (its wid) ^ " (f,l);"
  ]
;  

fun tune_collect_result (wid,job) = 
  (read_param (param_file (wid,job)), read_accuracy (accuracy_file (wid,job)))

(*
load "smlParallel"; load "mlTune"; load "mleCompute"; 
open mlTreeNeuralNetwork mlTune aiLib smlParallel mleCompute;

val trainfile = (!parallel_dir) ^ "/train";
val testfile = (!parallel_dir) ^ "/test";
val operlfile = (!parallel_dir) ^ "/operl";
val operl = mk_fast_set oper_compare (operl_of ``I 0 + SUC 0 * 0``);

val (trainex,validex) = create_allex 200;

fun init () =
  (
  write_tnnex trainfile trainex;
  write_tnnex testfile validex;
  write_operl operlfile operl
  )
;

fun codel_of wid = tune_codel_of 1 wid;

val dl = [16,8];
val nl = [100,200];
val bl = [16,128];
val ll = [10,100];
val ml = [0,9];
val paraml = grid_param (dl,nl,bl,ll,ml);

val ncore = 32;
val (final1,t) = add_time 
  (parmap_queue_extern ncore codel_of (init,tune_collect_result)) paraml;

val final2 = dict_sort compare_rmax final1;
write_param_results 
  (HOLDIR ^ "/src/AI/experiments/mleCompute_param_results") final2;
*)




end (* struct *)
