(* ========================================================================= *)
(* FILE          : mlNeuralNetwork.sml                                       *)
(* DESCRIPTION   : Feed forward neural network                               *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure mlNeuralNetwork :> mlNeuralNetwork =
struct

open HolKernel Abbrev boolLib aiLib mlMatrix smlParallel

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

(* -------------------------------------------------------------------------
   I/O
   ------------------------------------------------------------------------- *)

fun reall_to_string rl =
  String.concatWith " " (map (IEEEReal.toString o Real.toDecimal) rl)

fun string_to_reall rls =
  map (valOf o Real.fromDecimal o valOf o IEEEReal.fromString)
    (String.tokens Char.isSpace rls)

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

fun write_nn file nn = writel file [string_of_nn nn]

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

fun read_nn file = read_nn_sl (readl file)

fun string_of_v v = reall_to_string (vector_to_list v)
fun string_of_vv (v1,v2) = string_of_v v1 ^ "," ^ string_of_v v2

fun write_ex file argl = 
  writel file (map string_of_vv (only_hd argl))

fun vv_of_string s = 
  let val (a,b) = pair_of_list (String.tokens (fn x => x = #",") s) in
    (Vector.fromList (string_to_reall a), 
     Vector.fromList (string_to_reall b))
  end

fun read_ex file = [map vv_of_string (readl file)]

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
      (* should use (#outv fpdata) to use the derivative *)
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

fun train_nn_one nn (inputv,expectv) = bp_nn (fp_nn nn inputv) expectv

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

fun train_nn_subbatch nn subbatch =
  let
    val bpdatall = map (train_nn_one nn) subbatch
    val dwll = map (map #dw) bpdatall
    val dwl = sum_dwll dwll
  in
    (dwl, average_loss bpdatall)
  end

fun write_result file (dwl,loss) =
  (
  writel (file ^ "_dwl") [string_of_wl dwl];
  writel (file ^ "_loss") [rts loss]
  ) 

fun read_result file =
  (
  read_wl_sl (readl (file ^ "_dwl")),
  (valOf o Real.fromString o hd) (readl (file ^ "_loss"))
  )

val ext_flag = ref false

val extspec : (nn, (vect * vect) list, (mat list * real)) extspec =
  {
  self = "mlNeuralNetwork.extspec",
  reflect_globals = fn () => "()",
  function = train_nn_subbatch,
  write_param = write_nn,
  read_param = read_nn,
  write_argl = write_ex,
  read_argl = read_ex,
  write_result = write_result,
  read_result = read_result
  }

fun train_nn_batch ncore nn batch =
  let
    val subbatchl = cut_n ncore batch
    val (dwll,lossl) = split (
      if !ext_flag 
      then parmap_exact_extern ncore extspec nn subbatchl
      else parmap_exact ncore (train_nn_subbatch nn) subbatchl
      )
    val dwl = sum_dwll dwll
    val newnn = update_nn nn dwl
  in
    (newnn, average_real lossl)
  end

fun train_nn_epoch_aux ncore lossl nn batchl  = case batchl of
    [] => (print_endline ("loss: " ^ Real.toString (average_real lossl));
           nn)
  | batch :: m =>
    let val (newnn,loss) = train_nn_batch ncore nn batch in
      train_nn_epoch_aux ncore (loss :: lossl) newnn m
    end

fun train_nn_epoch ncore nn batchl = 
  train_nn_epoch_aux ncore [] nn batchl

fun train_nn ncore n nn size trainset =
  if n <= 0 then nn else
  let
    val _ = print (" " ^ its n ^ " ")
    val batchl = mk_batch size (shuffle trainset)
    val new_nn = train_nn_epoch ncore nn batchl
  in
    train_nn ncore (n - 1) new_nn size trainset
  end

end (* struct *)

(*
load "mlNeuralNetwork";
open aiLib mlMatrix mlNeuralNetwork;

val dim = 20;
val nex = 12800;
val nepoch = 1;
val bsize = 12800;
val starting_nn = random_nn (tanh,dtanh) (tanh,dtanh) [dim,dim,dim];
learningrate_glob := 0.02;

fun rev_vector v =
  let val vn = Vector.length v in
    Vector.tabulate (vn, fn i => Vector.sub (v,vn - i - 1))
  end
;
val set =
  let
    fun f _ = Vector.tabulate (dim, fn _ => random_real () - 0.5)
    val l = List.tabulate (nex, f)
  in
    map (fn x => (x, rev_vector x)) l
  end
;

val ncore = 4;
val (_,t) = add_time (train_nn ncore nepoch starting_nn bsize) set;

load "smlParallel"; open smlParallel;
ext_flag := true;
parallel_dir := "/dev/shm/thibault";
val threadl = boss_start_exact ncore extspec;
val (_,t) = add_time (train_nn ncore nepoch starting_nn bsize) set;
boss_stop_exact threadl;
ext_flag := false;


 *)
