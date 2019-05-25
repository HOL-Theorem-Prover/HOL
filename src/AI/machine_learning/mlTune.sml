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

(* -------------------------------------------------------------------------
   I/O
   ------------------------------------------------------------------------- *)

fun paraml_file () = (!parallel_dir ^ "/paraml")

fun accuracy_file (wid,job) =
  (!parallel_dir ^ "/" ^ its wid ^ "/accuracy" ^ its job)

(* -------------------------------------------------------------------------
   Distributing state to workers
   ------------------------------------------------------------------------- *)

fun write_state (trainex,testex,operl) =  
  (
  write_tnnex (!parallel_dir ^ "/train") trainex;
  write_tnnex (!parallel_dir ^ "/test") testex;
  write_operl (!parallel_dir ^ "/operl") operl
  )

fun read_state () =
  (
  read_tnnex (!parallel_dir ^ "/train"),
  read_tnnex (!parallel_dir ^ "/test"),
  read_operl (!parallel_dir ^ "/operl")
  )

(* -------------------------------------------------------------------------
   Distributing argument list to workers
   ------------------------------------------------------------------------- *)

fun write_paraml prl =
  let fun f {batchsize,dim,learningrate,nepoch,nlayer} =
    String.concatWith " "
    [its batchsize, its dim, rts learningrate, its nepoch, its nlayer]
  in
    writel (paraml_file ()) (map f prl)
  end

fun read_paraml () =
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
    map f (readl (paraml_file ()))
  end

(* -------------------------------------------------------------------------
   Report of the result by workers
   ------------------------------------------------------------------------- *)

fun write_accuracy file (r1,r2,t) = writel file [rts r1,rts r2,rts t]
fun read_accuracy file =
  let val l = readl file in
    case l of
      [a,b,c] => (valOf (Real.fromString a), valOf (Real.fromString b),
                  valOf (Real.fromString c))
    | _ => raise ERR "read_accuracy" ""
  end

(* -------------------------------------------------------------------------
   Save results of all experiments
   ------------------------------------------------------------------------- *)

fun write_param_results file prl =
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

(* -------------------------------------------------------------------------
   Train with parameters
   ------------------------------------------------------------------------- *)

fun train_tnn_extern ((ncore,dimout),(train,test,operl)) (wid,job)  
  (param as {dim,nepoch,batchsize,learningrate,nlayer})=
  let
    val _ = mlTreeNeuralNetwork.nlayer_glob := nlayer
    val randtnn = random_tnn (dim,dimout) operl
    val schedule = [(nepoch, learningrate /  (Real.fromInt batchsize))]
    val (tnn,t) = add_time 
      (prepare_train_tnn (ncore,batchsize) randtnn (train,test)) schedule
    val r1 = accuracy_set tnn train
    val r2 = accuracy_set tnn test
  in
    write_accuracy (accuracy_file (wid,job)) (r1,r2,t)
  end

fun mk_state_s (ncore,dimout) = 
  "((" ^ its ncore ^ "," ^ its dimout ^ "), mlTune.read_state ())"


fun train_tnn_parallel ncore ((ncore_loc,dimout),(train,test,operl)) paraml =
  let
    fun write_state_loc () = write_state (train,test,operl)
    val state_s = mk_state_s (ncore_loc,dimout)
    val argl_s = "mlTune.read_paraml ()"
    val f_s = "mlTune.train_tnn_extern"
    fun code_of wid = standard_code_of (state_s,argl_s,f_s) wid
    fun read_result widjob = read_accuracy (accuracy_file widjob)
    val _ = app print_endline (code_of 0)
    
  in
    parmap_queue_extern ncore code_of (write_state_loc, write_paraml) 
    read_result paraml
  end






end (* struct *)
