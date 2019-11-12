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
   Grid parameters
   ------------------------------------------------------------------------- *)

type ml_param =
  {dim: int, nepoch: int, batchsize: int, learningrate: real, nlayer: int}

fun grid_param (dl,nl,bl,ll,yl) =
  let
    val l1 = cartesian_productl [dl,nl,bl,ll,yl]
    val l2 = map quintuple_of_list l1
    fun f (d,n,b,l,y) =
      {dim=d,nepoch=n,batchsize=b,learningrate=int_div 1 l,nlayer=y}
  in
    map f l2
  end

type set_param =
  (int * int) *
  ((term * real list) list * (term * real list) list * (term * int) list)

(* -------------------------------------------------------------------------
   Training function
   ------------------------------------------------------------------------- *)

fun train_tnn_param ((ncore,dimout),(train,test,operl))
  (param as {dim,nepoch,batchsize,learningrate,nlayer})=
  let
    val tnn_param =
      {
      dimin = dim, dimout = dimout,
      nlayer_headnn = nlayer, nlayer_oper = nlayer, 
      operl = operl
      }
    val randtnn = random_tnn tnn_param
    val train_param =
      {
      batch_size = batchsize,
      learning_rate = learningrate, 
      ncore = ncore, 
      nepoch = nepoch,
      verbose = true
      }
    val schedule = [train_param]
    val (tnn,t) = add_time (train_tnn schedule randtnn) (train,test)
    val r1 = tnn_accuracy tnn train
    val r2 = tnn_accuracy tnn test
  in
    (r1,r2,t)
  end

(* -------------------------------------------------------------------------
   External parallelization
   ------------------------------------------------------------------------- *)

fun write_param file ((ncore,dimout),(train,test,operl)) =
  (
  writel (file ^ "_ncoredimout") (map its [ncore,dimout]);
  write_tnnex (file ^ "_train") train;
  write_tnnex (file ^ "_test") test;
  write_operl (file ^ "_operl") operl
  )
fun read_param file =
  (
  pair_of_list (map string_to_int (readl (file ^ "_ncoredimout"))),
  (read_tnnex (file ^ "_train"),
  read_tnnex (file ^ "_test"),
  read_operl (file ^ "_operl"))
  )

fun write_argl file prl =
  let fun f {batchsize,dim,learningrate,nepoch,nlayer} =
    String.concatWith " "
    [its batchsize, its dim, rts learningrate, its nepoch, its nlayer]
  in
    writel file (map f prl)
  end
fun read_argl file =
  let
    fun f s =
      let val (a,b,c,d,e) = quintuple_of_list (String.tokens Char.isSpace s) in
        {
        batchsize = string_to_int a,
        dim = string_to_int b,
        learningrate = valOf (Real.fromString c),
        nepoch = string_to_int d,
        nlayer = string_to_int e
        }
      end
  in
    map f (readl file)
  end

fun write_result file (r1,r2,t) = writel file (map rts [r1,r2,t])
fun read_result file =
  triple_of_list (map (valOf o Real.fromString) (readl file))

val extspec : (set_param, ml_param, real * real * real) extspec  =
  {
  self = "mlTune.extspec",
  parallel_dir = default_parallel_dir ^ "_tune_tnn",
  reflect_globals = fn () => "()",
  function = train_tnn_param,
  write_param = write_param,
  read_param = read_param,
  write_argl = write_argl,
  read_argl = read_argl,
  write_result = write_result,
  read_result = read_result
  }

(* -------------------------------------------------------------------------
   Save results of all experiments
   ------------------------------------------------------------------------- *)

fun write_summary file prl =
  let fun f ({batchsize,dim,learningrate,nepoch,nlayer},(r1,r2,t)) =
    "train " ^ rts r1 ^
    ", test " ^ rts r2 ^
    ", time " ^ rts t ^
    ", batchsize " ^ its batchsize ^
    ", dim " ^ its dim ^
    ", learningrate " ^ rts learningrate ^
    ", nepoch " ^ its nepoch ^
    ", nlayer " ^ its nlayer
  in
    writel file (map f prl)
  end

(*
load "mlTune"; open mlTune;
load "smlParallel"; open smlParallel;
val prl = parmap_queue_extern 10 extspec fixedparam paraml;
write_summary "my_file" prll;
*)

(* -------------------------------------------------------------------------
   Train different dhtnn arichtectures in parallel
   ------------------------------------------------------------------------- *)

fun train_dhtnn_fun () (exl, schedule, dhtnn_param) =
  let
    val randdhtnn = random_dhtnn tnn_param
    val tob = dfind tob_id tob_dict
    val exl' = map (fn (a,b,c) => (tob a, b, c)) exl
    val (dhtnn,t) = add_time (train_dhttnn schedule randtnn) exl
  in
    print_endline ("Training time : " ^ rts t);
    dhtnn
  end

fun write_noparam file (_:unit) = ()
fun read_noparam file = ()

fun write_dhtnn_argl file (exl, schedule, dhtnn_param) =
  (
  write_dhex (file ^ "_exl");
  write_schedule (file ^ "_schedule") schedule;
  write_dhtnn_param (file ^ "_dhtnn_param") dhtnn_param
  )
fun read_dhtnn_argl file =
  let
    val exl = read_dhex exl
    

(* 
  todo: 
  get rid of the send arguments to everyone at the beginning 
*)


fun read_argl file =
  let
    fun f s =
      let val (a,b,c,d,e) = quintuple_of_list (String.tokens Char.isSpace s) in
        {
        batchsize = string_to_int a,
        dim = string_to_int b,
        learningrate = valOf (Real.fromString c),
        nepoch = string_to_int d,
        nlayer = string_to_int e
        }
      end
  in
    map f (readl file)
  end

val train_dhtnn_extspec =
  {
  self = "train_dhtnn_extspec",
  parallel_dir = default_parallel_dir ^ "__train_dhtnn",
  reflect_globals = fn () => "()",
  function = train_dhtnn_fun,
  write_param = write_noparam,
  read_param = read_noparam,
  write_argl = write_exl,
  read_argl = read_exl,
  write_result = write_dhtnn,
  read_result = read_dhtnn
  }






end (* struct *)
