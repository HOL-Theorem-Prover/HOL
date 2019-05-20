(* ========================================================================= *)
(* FILE          : mlTune.sml                                                *)
(* DESCRIPTION   : Auto-tune for machine learning parameters and examples    *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mlTune :> mlTune =
struct

open HolKernel Abbrev boolLib aiLib mlTreeNeuralNetwork 
  mlReinforce smlParallel

val ERR = mk_HOL_ERR "mlTune"

(* -------------------------------------------------------------------------
   Tuning parameters
   ------------------------------------------------------------------------- *)

type ml_param = 
  {dim: int, nepoch: int, batchsize: int, learningrate: real, nlayers: int}

fun grid_param (dl,nl,bl,ll,yl) = 
  let 
    val l1 = cartesian_productl [dl,nl,bl,ll,yl]
    val l2 = map quintuple_of_list l1
    fun f (d,n,b,l,y) = 
      {dim=d,nepoch=n,batchsize=b,learningrate=int_div 1 l,nlayers=y}
  in
    map f l2
  end

fun write_param_results file prl =
  let fun f ({batchsize,dim,learningrate,nepoch,nlayers},(r1,r2)) =
    "test " ^ rts r2 ^
    ", train" ^ rts r1 ^
    ", batchsize " ^ its batchsize ^
    ", dim " ^ its dim ^
    ", learningrate " ^ rts learningrate ^
    ", nepoch " ^ its nepoch ^
    ", nlayers " ^ its nlayers
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

fun dhtnnout_file (wid,job) =
  (!parallel_dir ^ "/" ^ its wid ^ "/dhtnnout" ^ its job)


fun write_param file {dim,nepoch,batchsize,learningrate,nlayers} =
  let 
    val sl = 
    [its dim, its nepoch, its batchsize, rts learningrate, its nlayers]
  in
    writel file sl
  end

fun read_param file =
  let val (d,n,b,l,y) = quintuple_of_list (readl file) in
    {dim = string_to_int d, 
     nepoch = string_to_int n, 
     batchsize = string_to_int b, 
     learningrate= valOf (Real.fromString l), 
     nlayers = string_to_int y}
  end

fun write_accuracy file (r1,r2) = writel file [rts r1,rts r2]
fun read_accuracy file = 
  let val l = readl file in 
    case l of
      [a,b] => (valOf (Real.fromString a), valOf (Real.fromString b))
    | _ => raise ERR "read_accuracy" ""
  end

(* -------------------------------------------------------------------------
   Train with parameters
   ------------------------------------------------------------------------- *)

fun train_tnn_param (wid,job) ncore operl (train,test) 
  (param as {dim,nepoch,batchsize,learningrate,nlayers})=
  let 
    val _ = mlTreeNeuralNetwork.nlayers_glob := nlayers
    val randtnn = random_tnn (dim,4) operl
    val schedule = [(nepoch, learningrate /  (Real.fromInt batchsize))]
    val tnn = prepare_train_tnn (ncore,batchsize) randtnn (train,test) schedule
    val r1 = accuracy_set tnn train
    val r2 = accuracy_set tnn test
    val fileparam = param_file (wid,job)
    val fileaccuracy = accuracy_file (wid,job)
  in
    write_param fileparam param;
    write_accuracy fileaccuracy (r1,r2);
    writel_atomic (widout_file wid) ["done"]
  end

fun intlist_to_string l = "[" ^ String.concatWith "," (map its l) ^ "]"

fun tune_codel_of (dl,nl,bl,ll,yl) ncore_loc wid = 
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
   "val dl = " ^ intlist_to_string dl ^ ";",
   "val nl = " ^ intlist_to_string nl ^ ";",
   "val bl = " ^ intlist_to_string bl ^ ";",
   "val ll = " ^ intlist_to_string ll ^ ";",
   "val yl = " ^ intlist_to_string yl ^ ";",
   "val l = grid_param (dl,nl,bl,ll,yl);",
   "worker_start " ^ (its wid) ^ " (f,l);"
  ]
;  

fun tune_collect_result (wid,job) = 
  (read_param (param_file (wid,job)), 
   read_accuracy (accuracy_file (wid,job)))

(* -------------------------------------------------------------------------
   Train externally dhtnn with parameters
   ------------------------------------------------------------------------- *)

fun train_dhtnn_param (wid,job) ncore gamespec epex 
  (param as {dim,nepoch,batchsize,learningrate,nlayers})=
  let 
    val _ = mlTreeNeuralNetwork.nlayers_glob := nlayers
    val _ = dim_glob := dim
    val dhtnn_org = random_dhtnn_gamespec gamespec
    val schedule = [(nepoch, learningrate /  (Real.fromInt batchsize))]
    val _ = print_endline "before train_dhtnn_schedule"
    val dhtnn = train_dhtnn_schedule ncore dhtnn_org batchsize epex schedule
    val fileparam = param_file (wid,job)
    val filedhtnn = dhtnnout_file (wid,job)
  in
    write_param fileparam param;
    write_dhtnn filedhtnn dhtnn;
    writel_atomic (widout_file wid) ["done"]
  end

fun dhtune_codel_of gamespec (dl,nl,bl,ll,yl) ncore_loc wid = 
  [
   "open mlTreeNeuralNetwork mlTune smlParallel;",
   "open " ^ #opens gamespec ^ ";",
   "(* generating f *)",
   "val dir = " ^ quote (!parallel_dir) ^ ";",
   "val ncore = " ^ its ncore_loc ^ ";",
   "val epex = read_dhex (dir ^ \"/epex\")",
   "fun f (wid,job) param =", 
   "  train_dhtnn_param (wid,job) ncore gamespec epex param;",
   "(* generating jobs *)",
   "val dl = " ^ intlist_to_string dl ^ ";",
   "val nl = " ^ intlist_to_string nl ^ ";",
   "val bl = " ^ intlist_to_string bl ^ ";",
   "val ll = " ^ intlist_to_string ll ^ ";",
   "val yl = " ^ intlist_to_string yl ^ ";",
   "val l = grid_param (dl,nl,bl,ll,yl);",
   "worker_start " ^ (its wid) ^ " (f,l);"
  ]
;  

fun dhtune_collect_result (wid,job) = 
  (read_param (param_file (wid,job)), 
   read_dhtnn (dhtnnout_file (wid,job)))


end (* struct *)
