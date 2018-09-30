(* ========================================================================== *)
(* FILE          : tttNN.sml                                                  *)
(* DESCRIPTION   : Neural network training                                    *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University          *)
(* DATE          : 2018                                                       *)
(* ========================================================================== *)

structure tttNN :> tttNN =
struct

open HolKernel boolLib Abbrev tttTools tttMatrix

val ERR = mk_HOL_ERR "tttNN"


(*----------------------------------------------------------------------------
 * Activation functions. Derivatives use the function itself.
 *----------------------------------------------------------------------------*)

(* Math.tanh *)
fun dtanh x = 1.0 - (x:real) * x (* 1 - (tanh x) * (tanh x) *)

(*----------------------------------------------------------------------------
 * Layer
 *----------------------------------------------------------------------------*)

type layer =
  {a  : real -> real, 
   da : real -> real,
   w  : real vector vector} 

type fpdata =
  {layer : layer,
   inv   : real vector,
   outv  : real vector,
   outnv : real vector}  

(*----------------------------------------------------------------------------
  Forward propagration (fp) with memory of the steps
  ----------------------------------------------------------------------------*)

fun fp_layer (layer : layer) inv =
  let 
    val outv = mat_mult (#w layer) inv
    val outnv = Vector.map (#a layer) outv 
  in
    {layer = layer, inv = inv, outv = outv, outnv = outnv}  
  end
  
fun fp_nn nn v = case nn of
    [] => []
  | (layer : layer) :: m =>  
    let val fpdata = fp_layer layer v in
      fpdata :: fp_nn m (#outnv fpdata)
    end

fun apply_nn nn v = 
  let val fpdatal = rev (fp_nn nn v) in 
    #outnv (hd fpdatal)
  end

(*---------------------------------------------------------------------------
  Backward propagation (bp)
  Takes the data from the forward pass, computes the loss and weight updates
  by gradient descent.
  --------------------------------------------------------------------------- *) 


fun bp_layer eta (fpdata : fpdata) dnode_out =
  let 
    (* activation function *)
    val dnode_da = (* trick undone *)
      let val dav = Vector.map (#da (#layer fpdata)) (#outnv fpdata) in
        mult_rvect dav dnode_out
      end
    (* matrix multiplication *)
    fun dw_f eta i j = 
      eta * Vector.sub (#inv fpdata,j) * Vector.sub (dnode_da,i)
    val mat_delta = mat_tabulate (dw_f eta) (mat_dim (#w (#layer fpdata)))
    val dnode_in = mat_mult (mat_transpose mat_delta) dnode_da
  in
    (mat_delta, dnode_in)
  end

fun bp_nn_aux eta rev_nn_data dnode_out = 
  case rev_nn_data of
    [] => []
  | fpdata :: m =>
    let val (bp_mat,dnode_in) = bp_layer eta fpdata dnode_out in
      bp_mat :: bp_nn_aux eta m dnode_in
    end

fun calc_loss v =
  let fun square x = (x:real) * x in average_rvect (Vector.map square v) end

fun bp_nn eta nn_data expectv =
  let 
    val rev_nn_data = rev nn_data 
    val fpdata = hd rev_nn_data 
    val resultv = #outnv fpdata
    val dnode = diff_rvect expectv resultv
    val loss = calc_loss dnode
  in
    (loss, rev (bp_nn_aux eta rev_nn_data dnode))
  end

(*---------------------------------------------------------------------------
  Average the updates over a batch.
  --------------------------------------------------------------------------- *)
  
fun fpbp_nn eta nn (inputv,expectv) =
  let val (nn_data : fpdata list) = fp_nn nn inputv in
    bp_nn eta nn_data (expectv : real vector)
  end

fun regroup_by_layers nndwl = case nndwl of
    [] => raise ERR "regroup_by_layers" ""
  | [] :: cont => []
  | (a :: m) :: cont => map hd nndwl :: regroup_by_layers (map tl nndwl)

fun average_dwl dwl = 
  let fun f i j = average_real (map (fn w => mat_sub w i j) dwl) in
    mat_tabulate f (mat_dim (hd dwl))
  end

fun average_nndwl nndwl = map average_dwl (regroup_by_layers nndwl)

fun average_batch eta nn batch = 
  let 
    val l = map (fpbp_nn eta nn) batch
    val (lossl, nndwl) = split l
    val loss = average_real lossl
    val nn_delta = average_nndwl nndwl
  in
    (loss, nn_delta)
  end

(*---------------------------------------------------------------------------
  Applying the udpates with momentum and decay.
  --------------------------------------------------------------------------- *)

val lambda = 0.01
val momentum = 0.9

fun update_layer decay (layer,(wu,prev_wu)) = 
  {
  a = #a layer, da = #da layer, w = 
  let 
    val m1 = mat_smult (1.0 - momentum) wu 
    val m2 = mat_smult momentum prev_wu
    val m3 = mat_add m1 m2 
  in
    mat_smult decay (mat_add (#w layer) m3)
  end
  }

(*---------------------------------------------------------------------------
  Training for one batch.
  --------------------------------------------------------------------------- *)

fun train_batch pnn_delta eta batch nn =
  let 
    val decay = 1.0 - (lambda * eta)
    val (loss, nn_delta) = average_batch eta nn batch 
    val pnn_delta_aux = case pnn_delta of 
      NONE => nn_delta
    | SOME x => x
    val lw = combine (nn, combine (nn_delta, pnn_delta_aux))
    val new_nn = map (update_layer decay) lw
  in
    (* print_endline ("loss: " ^ Real.toString loss); *)
    (loss, new_nn, nn_delta)
  end

(*---------------------------------------------------------------------------
  Training for one epoch.
  --------------------------------------------------------------------------- *)

fun train_epoch_aux eta pnn_delta lossl nn batchl  = case batchl of
    [] => 
    (
    print_endline ("loss: " ^ Real.toString (average_real lossl));
    nn
    ) 
  | batch :: m => 
    let val (loss, new_nn, nn_delta) = train_batch pnn_delta eta batch nn in
      train_epoch_aux eta (SOME nn_delta) (loss :: lossl) new_nn m 
    end

fun train_epoch eta nn batchl = train_epoch_aux eta NONE [] nn batchl

(*---------------------------------------------------------------------------
  Utilities.
  --------------------------------------------------------------------------- *)

fun random_nn depth dim = 
  let fun f i = {a = Math.tanh, da = dtanh, w = mat_random dim} in
    List.tabulate (depth,f)
  end

fun mk_batch_aux size acc res l =
  if length acc >= size 
  then mk_batch_aux size [] (acc :: res) l
  else case l of
      [] => res
    | a :: m => mk_batch_aux size (a :: acc) res m

fun mk_batch size l = mk_batch_aux size [] [] l

fun train_nepoch n eta nn size training_set = 
  if n <= 0 then nn else
  let 
    val batchl = mk_batch size training_set
    val new_nn = train_epoch eta nn batchl 
  in
    train_nepoch (n - 1) eta new_nn size training_set
  end

(*---------------------------------------------------------------------------
  Testing

load "tttNN";
open tttTools tttMatrix tttNN;

fun id x = (x:real)
fun did (x:real) = 1.0
fun dtanh x = 1.0 - (x:real) * x;
fun relu x = Real.max (x, 0.01 * x)
fun drelu x = if x > 0.0 then 1.0 else 0.01

fun random_nm diml = 
  let fun f dim = {a = relu, da = drelu, w = tttMatrix.mat_random dim} in
    map f diml
  end



val training_set =
  let 
    fun f _ = Vector.tabulate (2, fn _ => random_real () * 0.8 + 0.1)
    val l = List.tabulate (10000, f) 
  in
    map (fn x => (x, x)) l
  end
;
val eta = 0.001;
val nn = train_nepoch 1000 eta starting_nn 100 training_set;

  --------------------------------------------------------------------------- *)

(*---------------------------------------------------------------------------
  Examples:

Learning the identity function.

val starting_nn = random_nm [(2,2)];

val training_set =
  let 
    fun f _ = Vector.tabulate (2, fn _ => random_real () * 0.8 + 0.1)
    val l = List.tabulate (10000, f) 
  in
    map (fn x => (x, x)) l
  end
;
val eta = 0.001;
val nn = train_nepoch 1000 eta starting_nn 100 training_set;

  --------------------------------------------------------------------------- *)


(*---------------------------------------------------------------------------
  todo

batch norm 
add bias 
CNN.
add residualnetworks
remove relu from last layer.

  --------------------------------------------------------------------------- *)




end (* struct *)
