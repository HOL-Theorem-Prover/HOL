(* ========================================================================= *)
(* FILE          : mleArith.sml                                              *)
(* DESCRIPTION   : Arithmetical expression evaluation using TNN              *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mleArith :> mleArith =
struct

open HolKernel Abbrev boolLib aiLib psTermGen smlParallel
mlTreeNeuralNetwork mleArithData

val ERR = mk_HOL_ERR "mleArith"
val arithdir = HOLDIR ^ "/examples/AI_TNN/data_arith"

(* -------------------------------------------------------------------------
   Syntax
   ------------------------------------------------------------------------- *)

val operl = [``0``,``$+``,``$*``,``SUC``];
val head_bin4 = mk_var ("head_bin4",``:num -> num``)
fun mk_head x = mk_comb (head_bin4, x)

(* -------------------------------------------------------------------------
   Examples
   ------------------------------------------------------------------------- *)

fun prepare_ex exl = map (fn (a,b) => [(mk_head a, bin_rep 4 b)]) exl

(* -------------------------------------------------------------------------
   Training
   ------------------------------------------------------------------------- *)

val tnndim = map_assoc (dim_std (2,14)) operl @ [(head_bin4,[14,4])]
val schedule =
  [{ncore = 1, verbose = true, learning_rate = 0.02,
    batch_size = 8, nepoch = 50}] @
  [{ncore = 1, verbose = true, learning_rate = 0.02,
    batch_size = 16, nepoch = 50}]  @
  [{ncore = 1, verbose = true, learning_rate = 0.02,
    batch_size = 32, nepoch = 50}] @
  [{ncore = 1, verbose = true, learning_rate = 0.02,
    batch_size = 64, nepoch = 50}]

fun train_fixed () =
  let
    val exl = prepare_ex (import_arithdata "train")
    val tnn = train_tnn schedule (random_tnn tnndim) (exl,[])
  in
    write_tnn (arithdir ^ "/tnn") tnn; tnn
  end

(* ------------------------------------------------------------------------
   Testing
   ------------------------------------------------------------------------ *)

fun test_fixed tnn =
  let val exl = map (prepare_ex o import_arithdata) ["train","valid","test"] in
    map (tnn_accuracy tnn) exl
  end

(*
load "mleArith"; open mleArith;
val tnn = train_fixed ();
val r = test_fixed tnn;
*)

end (* struct *)
