(* ========================================================================= *)
(* FILE          : mleCompute.sml                                            *)
(* DESCRIPTION   : Direct computation on terms using tree neural network     *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mleCompute :> mleCompute =
struct

open HolKernel Abbrev boolLib aiLib psTermGen smlParallel mlTreeNeuralNetwork
mlTacticData mlTune mleLib mleArithData

val ERR = mk_HOL_ERR "mleCompute"

val compute_dir = HOLDIR ^ "/src/AI/experiments/data_compute"

(* -------------------------------------------------------------------------
   Constructing examples
   ------------------------------------------------------------------------- *)

fun compute_exout tml = map_assoc (bin_rep 4 o eval_numtm) tml

(* -------------------------------------------------------------------------
   Associated tnn
   ------------------------------------------------------------------------- *)

val operl = mk_fast_set oper_compare (operl_of ``0 + SUC 0 * 0``)

(* -------------------------------------------------------------------------
   Training with a fixed set of parameters
   ------------------------------------------------------------------------- *)

fun train_fixed basename exl =
  let
    val dim = 12
    val randtnn = random_tnn (dim,4) operl
    val bsize = 16
    val schedule = [(100, 0.02 / (Real.fromInt bsize))]
    val ncore = 4
    val tnn = prepare_train_tnn (ncore,bsize) randtnn (exl,[]) schedule
    val _ = mkDir_err compute_dir
  in
    write_tnn (compute_dir ^ "/" ^ basename) tnn;
    tnn
  end

(*
load "mleCompute"; open mleCompute;
load "mleArithData"; open mleArithData;
val tml = mlTacticData.import_terml (dataarith_dir ^ "/train");
val exl = compute_exout tml;
val tnn = train_fixed "test" exl;
val tm = random_elem tml;
infer_tnn tnn tm;
*)

(* ------------------------------------------------------------------------
   Accuracy of the tree neural network on arithmetical datasets
   ------------------------------------------------------------------------ *)

fun accuracy_fixed tnn =
  let
    val filel = map (fn x => dataarith_dir ^ "/" ^ x)
      ["train","valid","test","big"]
    val tmll = map mlTacticData.import_terml filel
    val exl = map compute_exout tmll
  in
    quadruple_of_list (map (accuracy_set tnn) exl)
  end


end (* struct *)
