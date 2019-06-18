(* ========================================================================= *)
(* FILE          : mlPrune.sml                                               *)
(* DESCRIPTION   : Tree neural network                                       *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mlPrune :> mlPrune =
struct

open HolKernel boolLib Abbrev aiLib mlMatrix mlNeuralNetwork smlParallel

val ERR = mk_HOL_ERR "mlPrune"
val debugdir = HOLDIR ^ "/src/AI/machine_learning/debug"
fun debug s = debug_in_dir debugdir "mlPrune" s


end (* struct *)
