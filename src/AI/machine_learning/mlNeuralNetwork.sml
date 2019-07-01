(* ========================================================================= *)
(* FILE          : mlNeuralNetwork.sml                                       *)
(* DESCRIPTION   : Feed forward neural network                               *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure mlNeuralNetwork :> mlNeuralNetwork =
struct

open HolKernel Abbrev boolLib aiLib mlMatrix

val ERR = mk_HOL_ERR "mlNeuralNetwork"
val debugdir = HOLDIR ^ "/src/AI/machine_learning/debug"
fun debug s = debug_in_dir debugdir "mlNeuralNetwork" s

(* -------------------------------------------------------------------------
   Parameters
   ------------------------------------------------------------------------- *)

val learningrate_glob = ref 0.01

(* -------------------------------------------------------------------------
   Activation and derivatives (with a smart trick)
   ------------------------------------------------------------------------- *)

fun tanh x = Math.tanh x
fun dtanh x = 1.0 - (x:real) * x (* 1 - (tanh x) * (tanh x) *)
fun relu x  = if x > 0.0 then x else 0.0
fun drelu x = if x < 0.000000000001 then 0.0 else 1.0
fun leakyrelu x  = if x > 0.0 then x else 0.01 * x
fun dleakyrelu x = if x <= 0.0 then 0.01 else 1.0
fun id (x:real) = x:real
fun did (x:real) = 1.0

(* -------------------------------------------------------------------------
   Types
   ------------------------------------------------------------------------- *)

type layer = {a : real -> real, da : real -> real, w : real vector vector}
type nn = layer list

type fpdata =
  {layer : layer, inv : real vector, outv : real vector, outnv : real vector}

type bpdata =
  {doutnv: real vector, doutv: real vector, dinv: real vector,
   dw: real vector vector}

(*---------------------------------------------------------------------------
  Initialization
  ---------------------------------------------------------------------------*)

fun diml_aux insize sizel = case sizel of
    [] => []
  | outsize :: m => (outsize, insize) :: diml_aux outsize m

fun diml_of sizel = case sizel of
    [] => []
  | a :: m => diml_aux a m

fun random_nn (a1,da1) (a2,da2) sizel =
  let
    val l = diml_of sizel
    fun f x = {a = a1, da = da1, w = mat_random x}
    fun g x = {a = a2, da = da2, w = mat_random x}
  in
    map f (butlast l) @ [g (last l)]
  end

(*---------------------------------------------------------------------------
  Forward propagation (fp) with memory of the steps
  ---------------------------------------------------------------------------*)

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

(*--------------------------------------------------------------------------
  Backward propagation (bp)
  Takes the data from the forward pass, computes the loss and weight updates
  by gradient descent. Input is j. Output is i. Matrix is Mij.
  -------------------------------------------------------------------------- *)

fun bp_layer (fpdata:fpdata) doutnv =
  let
    val doutv =
      (* should use (#outv fpdata) if you want to use the derivative *)
      let val dav = Vector.map (#da (#layer fpdata)) (#outnv fpdata) in
        mult_rvect dav doutnv
      end
    val w        = #w (#layer fpdata)
    fun dw_f i j = Vector.sub (#inv fpdata,j) * Vector.sub (doutv,i)
    val dw       = mat_tabulate dw_f (mat_dim w)
    val dinv     = mat_mult (mat_transpose w) doutv
  in
   {doutnv = doutnv,
    doutv = doutv,
    dinv = dinv,
    dw = dw}
  end

fun bp_nn_aux rev_fpdatal doutnv =
  case rev_fpdatal of
    [] => []
  | fpdata :: m =>
    let val bpdata = bp_layer fpdata doutnv in
      bpdata :: bp_nn_aux m (#dinv bpdata)
    end

fun bp_nn_wocost fpdatal doutnv = rev (bp_nn_aux (rev fpdatal) doutnv)

fun bp_nn fpdatal expectv =
  let
    val rev_fpdatal = rev fpdatal
    val outnv = #outnv (hd rev_fpdatal)
    val doutnv = diff_rvect expectv outnv
  in
    rev (bp_nn_aux rev_fpdatal doutnv)
  end

(* -------------------------------------------------------------------------
   Average the updates over a batch.
   ------------------------------------------------------------------------- *)

fun train_nn_one nn (inputv,expectv) =
  let val fpdatal = fp_nn nn inputv in
    bp_nn fpdatal expectv
  end

fun transpose_ll ll = case ll of
    [] :: _ => []
  | _ => map hd ll :: transpose_ll (map tl ll)

fun sum_dwll dwll = case dwll of
     [dwl] => dwl
   | _ => map matl_add (transpose_ll dwll)

fun smult_dwl k dwl = map (mat_smult k) dwl


(* -------------------------------------------------------------------------
   Loss
   ------------------------------------------------------------------------- *)

fun mean_square_error v =
  let fun square x = (x:real) * x in
    Math.sqrt (average_rvect (Vector.map square v))
  end

fun bp_loss bpdatal = mean_square_error (#doutnv (last bpdatal))

fun average_loss bpdatall = average_real (map bp_loss bpdatall)

(* -------------------------------------------------------------------------
   Weight udpate
   ------------------------------------------------------------------------- *)

fun clip (a,b) m =
  let fun f x = if x < a then a else (if x > b then b else x) in
    mat_map f m
  end

fun update_layer (layer, layerwu) =
  let
    val w0 = mat_smult (!learningrate_glob) layerwu
    val w1 = mat_add (#w layer) w0
    val w2 = clip (~4.0,4.0) w1
  in
    {a = #a layer, da = #da layer, w = w2}
  end

fun update_nn nn wu = map update_layer (combine (nn,wu))

fun random_wu nn = 
  let 
    val wl = map #w nn
    fun f w = mat_map (fn _ => random_real () - 0.5) w
  in
    map f wl
  end

fun random_update_nn nn = update_nn nn (random_wu nn)

(* -------------------------------------------------------------------------
   Training schedule
   ------------------------------------------------------------------------- *)

fun train_nn_batch batch nn =
  let
    val bpdatall = map (train_nn_one nn) batch
    val dwll     = map (map #dw) bpdatall
    val dwl      = sum_dwll dwll
    val newnn    = update_nn nn dwl
  in
    (newnn, average_loss bpdatall)
  end

fun train_nn_epoch_aux lossl nn batchl  = case batchl of
    [] => (print_endline ("loss: " ^ Real.toString (average_real lossl));
           nn)
  | batch :: m =>
    let val (newnn,loss) = train_nn_batch batch nn in
      train_nn_epoch_aux (loss :: lossl) newnn m
    end

fun train_nn_epoch nn batchl = train_nn_epoch_aux [] nn batchl

fun train_nn_nepoch n nn size trainset =
  if n <= 0 then nn else
  let
    val batchl = mk_batch size (shuffle trainset)
    val new_nn = train_nn_epoch nn batchl
  in
    train_nn_nepoch (n - 1) new_nn size trainset
  end

(* -------------------------------------------------------------------------
   Printing
   ------------------------------------------------------------------------- *)

fun string_of_wl wl =
  let
    val diml = map (mat_dim) wl
    fun f (a,b) = its a ^ "," ^ its b
  in
    String.concatWith " " (map f diml) ^ "\n" ^
    String.concatWith "\n\n" (map string_of_mat wl)
  end

fun string_of_nn nn =
  let
    val diml = map (mat_dim o #w) nn
    fun f (a,b) = its a ^ "," ^ its b
  in
    String.concatWith " " (map f diml) ^ "\n" ^
    String.concatWith "\n\n" (map (string_of_mat o #w) nn)
  end

fun split_nl nl l = case nl of
    [] => raise ERR "split_nl" ""
  | [a] => if length l = a then [l] else raise ERR "split_nl" ""
  | a :: m =>
    let val (l1,l2) = part_n a l in
      l1 :: split_nl m l2
    end

fun read_wl_sl sl =
  let
    val nl = map fst (read_diml (hd sl))
    val matsl = split_nl nl (tl sl)
  in
    map read_mat_sl matsl
  end

fun read_nn_sl sl =
  let
    val nl = map fst (read_diml (hd sl))
    val matsl = split_nl nl (tl sl)
    val matl =  map read_mat_sl matsl
    fun f m = {a = tanh, da = dtanh, w = m}
  in
    map f matl
  end
  handle Empty => raise ERR "read_nn_sl" ""

(*
load "mlNeuralNetwork"; load "aiLib"; open mlMatrix mlNeuralNetwork aiLib;
val dir = HOLDIR ^ "/src/AI";
val nn1 = random_nn (tanh,dtanh) (tanh,dtanh) [4,3,2,1];
val file = dir ^ "/test";
writel file [string_of_nn nn1];
val sl = readl file;
val nn2 = read_nn_sl sl;
*)

end (* struct *)

(*---------------------------------------------------------------------------
load "mlNeuralNetwork";
open mlTools mlMatrix mlNeuralNetwork;
val starting_nn = random_nn (tanh,dtanh) (tanh,dtanh) [2,5,2];

fun rev_vector v =
  let val vn = Vector.length v in
    Vector.tabulate (vn, fn i => Vector.sub (v,vn - i - 1))
  end


val training_set =
  let
    fun f _ = Vector.tabulate (2, fn _ => random_real () - 0.5)
    val l = List.tabulate (100000, f)
  in
    map (fn x => (x, rev_vector x)) l
  end
;

learningrate_glob := 0.001;
momentum := 0.0;
decay := 1.0;

val nn = train_nn_nepoch 1000 starting_nn 100 training_set;

  --------------------------------------------------------------------------- *)
