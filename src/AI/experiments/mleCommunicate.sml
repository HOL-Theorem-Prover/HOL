(* ========================================================================= *)
(* FILE          : mleCommunicate.sml                                        *)
(* DESCRIPTION   : Direct computation on terms using tree neural network     *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2019                                                      *)
(* ========================================================================= *)

structure mleCommunicate :> mleCommunicate =
struct

open HolKernel Abbrev boolLib aiLib psTermGen smlParallel mlNeuralNetwork
mlTacticData mleLib

val ERR = mk_HOL_ERR "mleCommunicate"

type nnc = mlNeuralNetwork.nn * mlNeuralNetwork.nn

(* -------------------------------------------------------------------------
   Training two neural networks with one discrete communication layer
   ------------------------------------------------------------------------- *)

fun discretize v = Vector.map (fn x => if x > 0.0 then 1.0 else ~1.0) v

fun all_discrete_inv n = map Vector.fromList
  (cartesian_productl (List.tabulate (n, fn _ => [1.0,~1.0])))

fun same_sign v1 v2 = (Vector.map Real.sign v1 = Vector.map Real.sign v2)

fun randomv_but v =
  let val v' = discretize (Vector.map (fn _ => 2.0 * random_real () - 1.0) v) in
    if same_sign v v' then randomv_but v else v'
  end

fun neg_discretize v = Vector.map (fn x => if x < 0.0 then 1.0 else ~1.0) v

fun train_nnc_one (nn1,nn2) (inputv,expectv) =
  let
    val fpdatal1 = fp_nn nn1 inputv
    val interv = discretize (#outnv (last fpdatal1))
    val fpdatal2 = fp_nn nn2 interv
    val bpdatal2 = bp_nn fpdatal2 expectv
    val outputv = #outnv (last fpdatal2)
    val ev = 
      if same_sign outputv expectv then interv else randomv_but interv
    val bpdatal1 = bp_nn fpdatal1 ev
  in
    (bpdatal1,bpdatal2)
  end;

fun train_nnc_batch (nn1,nn2) batch =
  let
    val (bpdatall1, bpdatall2) = split (map (train_nnc_one (nn1,nn2)) batch)
    val dwl1 = sum_dwll (map (map #dw) bpdatall1)
    val dwl2 = sum_dwll (map (map #dw) bpdatall2)
    val loss1 = average_loss bpdatall1
    val loss2 = average_loss bpdatall2
  in
    ((update_nn nn1 dwl1, update_nn nn2 dwl2),(loss1,loss2))
  end

fun train_nnc_epoch (nepoch,bsize) (l1,l2) nnc batchl = case batchl of
    [] => (print_endline (
             pad 4 " " (its nepoch) ^ " " ^
             pretty_real (average_real l1) ^ " " ^ 
             pretty_real (average_real l2));  
           nnc)
  | batch :: m =>
    let val (newnnc,(a1,a2)) = train_nnc_batch nnc batch in
      train_nnc_epoch (nepoch,bsize) (a1 :: l1, a2 :: l2) newnnc m 
    end

fun train_nnc (nepoch,bsize) nnc exl =
  if nepoch <= 0 then nnc else 
  let 
    val batchl = mk_batch bsize (shuffle exl)
    val newnnc = train_nnc_epoch (nepoch,bsize) ([],[]) nnc batchl
  in
    train_nnc (nepoch-1, bsize) newnnc exl
  end

fun infer_nnc (nn1,nn2) v = (infer_nn nn2 o discretize o infer_nn nn1) v

fun accuracy_nnc nnc exl =
  let
    val l1 = map (discretize o infer_nnc nnc) (map fst exl)
    val l2 = filter (uncurry same_sign) (combine (l1, map snd exl))
  in
    int_div (length l2) (length l1)
  end


(*
load "mlNeuralNetwork"; open mlNeuralNetwork;
load "aiLib"; open aiLib;
load "mleCommunicate"; open mleCommunicate;

fun is_odd v = length (filter (fn x => x > 0.0) (vector_to_list v)) mod 2 = 1
fun is_big v = 
  length (filter (fn x => x > 0.0) (vector_to_list v)) >
  length (filter (fn x => x < 0.0) (vector_to_list v))

fun f v = if is_odd v then Vector.fromList [1.0] else Vector.fromList [~1.0]
fun g v = if is_odd v then Vector.fromList [1.0] else Vector.fromList [~1.0]

val dim = 8;
val invl = all_discrete_inv dim;
val exl = map (fn x => (x,f x)) invl;
val nn1 = random_nn (tanh,dtanh) [dim,dim,dim];
val nn2 = random_nn (tanh,dtanh) [dim,dim,1];

learningrate_glob := 0.001;
val nnc = train_nnc (5000,1) (nn1,nn2) exl;
val r = accuracy_nnc nnc exl;
val l2 = map_assoc (discretize o infer_nn (snd nnc)) (all_discrete_inv 8);
val l1 = map_assoc (discretize o infer_nn (fst nnc)) invl;
val ltot = map_assoc (discretize o infer_nnc nnc) invl;

val l3 = map_assoc (discretize o infer_nn (fst nnc2)) invl;
val nn1trained = train_nn 1 100 nn1 16 exl;
val l4 = map_assoc (discretize o infer_nn nn1trained) invl;
val accuracy = int_div (length l4) (length invl);

(* idea: multiple nn, miror nn, collaborative nn (ie xor function) *) *)



end (* struct *)
