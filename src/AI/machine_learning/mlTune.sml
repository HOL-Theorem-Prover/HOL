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
    val _ = mlTreeNeuralNetwork.nlayer_glob := nlayer
    val randtnn = random_tnn (dim,dimout) operl
    val schedule = [(nepoch, learningrate /  (Real.fromInt batchsize))]
    val (tnn,t) = add_time
      (train_tnn (ncore,batchsize) randtnn (train,test)) schedule
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

val extspec : (set_param, ml_param, real * real * real) smlParallel.extspec  =
  {
  self = "mlTune.extspec",
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
*)

end (* struct *)
