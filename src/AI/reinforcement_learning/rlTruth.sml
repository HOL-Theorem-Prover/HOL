(* ========================================================================= *)
(* FILE          : rlTruth.sml                                               *)
(* DESCRIPTION   : Estimating of the truth of a formula                      *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure rlTruth :> rlTruth =
struct

(*
  load "mlTreeNeuralNetwork"; load "rlLib"; load "psTermGen";
  load "mlNearestNeighbor"; load "psTermGen";
*)

open HolKernel Abbrev boolLib aiLib rlLib psTermGen

val ERR = mk_HOL_ERR "rlMiniEx"

(* -------------------------------------------------------------------------
   Ground arithmetic
   ------------------------------------------------------------------------- *)

fun eval_ground tm = (string_to_int o term_to_string o rhs o concl o EVAL) tm

fun mk_ttset_ground (maxsize,maxvalue) ntarget =
  let
    val cset = [``0``,``$+``,``SUC``,``$*``]
    val tml0 = gen_term_size maxsize (``:num``,cset)
    val tml1 = mapfilter (fn x => (eval_ground x,x)) tml0
    val tmld = dregroup Int.compare tml1
    val nl = List.tabulate (maxvalue + 1, I)
    fun random_true _ =
      let val tml = dfind (random_elem nl) tmld in
        (mk_eq (random_elem tml, random_elem tml), [1.0])
      end
    fun random_false _ =
      let
        val (n1,n2) = pair_of_list (first_n 2 (shuffle nl))
        val tml1 = dfind n1 tmld
        val tml2 = dfind n2 tmld
      in
        (mk_eq (random_elem tml1, random_elem tml2), [0.0])
      end
  in
    (
    List.tabulate (ntarget div 2, random_true) @
    List.tabulate (ntarget div 2, random_false),
    List.tabulate (ntarget div 2, random_true) @
    List.tabulate (ntarget div 2, random_false)
    )
  end

fun mk_true_arith_eq (maxsize,maxvalue) ntarget =
  let
    val cset = [``0``,``$+``,``SUC``,``$*``]
    val tml0 = gen_term_size maxsize (``:num``,cset)
    val tml1 = mapfilter (fn x => (eval_ground x,x)) tml0
    val tmld = dregroup Int.compare tml1
    val nl = List.tabulate (maxvalue + 1, I)
    fun random_true _ =
      let val tml = dfind (random_elem nl) tmld in
        mk_eq (random_elem tml, random_elem tml)
      end
  in
    List.tabulate (ntarget, random_true)
  end


end (* struct *)

(*
app load ["rlTruth", "aiLib", "rlLib", "mlTreeNeuralNetwork", "psTermGen"];
open rlTruth aiLib rlLib mlTreeNeuralNetwork psTermGen;

val maxsize = 9; val maxvalue = 4; val ntarget = 40000;
val (trainset,testset) = mk_ttset_ground (maxsize,maxvalue) ntarget;

val operl = mk_fast_set oper_compare (operl_of_term ``0 + SUC 0 * 0 = 0``);
val randtnn = random_tnn (4,1) operl;

val bsize = 64;
val schedule = [(100,0.1)];
adaptive_flag := false; (* to be tested *)
val tnn = prepare_train_tnn randtnn bsize (trainset,testset) schedule;

val tm = mk_eq (mk_mult (mk_sucn 2, mk_sucn 2), mk_sucn 4);
infer_tnn tnn tm; (* todo: scale this learning to arbitrary large terms *)

(*
select a distribution of a uniform distribution
for each epoch? easy/middle/hard examples.
*)

(* could be in rlLib
  fun int_to_numtm =
  fun numtm_to_suctm =
    let
      val tml = [``0``,``1``,``2``,``3``,``4``,``5``,``6``,``7``,``8``,``9``]
      val
  test class of the polynomial by looking at this table
  fun instx i tm = subst [{redex = ``x:num``, residue = i}] tm;

  fun graph_of tm = map (eval_ground o C instx tm) inputl
*)

(*
fun f_accuracy f testset =
  let fun correct (tm,expectv) =
    let val v = f tm in if expectv > 0.5 then v > 0.5 else v < 0.5 end
  in
    int_div (length (filter correct testset)) (length testset)
  end

fun tnn_accuracy tnn testset = f_accuracy (eval_tnn tnn) testset
fun knn_accuracy knn testset = f_accuracy (infer_knn knn) testset
*)
*)




