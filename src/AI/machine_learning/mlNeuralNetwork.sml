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

(* inv includes biais *)
type fpdata = {layer : layer, inv : vect, outv : vect, outnv : vect}
type bpdata = {doutnv : vect, doutv : vect, dinv : vect, dw : mat}

(*---------------------------------------------------------------------------
  Initialization
  ---------------------------------------------------------------------------*)

fun diml_aux insize sizel = case sizel of
    [] => []
  | outsize :: m => (outsize, insize) :: diml_aux outsize m

fun diml_of sizel = case sizel of
    [] => []
  | a :: m => diml_aux a m

fun random_nn (a,da) sizel =
  let
    val l = diml_of sizel
    fun biais_dim (i,j) = (i,j+1)
    fun f x = {a = a, da = da, w = mat_random (biais_dim x)}
  in
    map f l
  end

(* -------------------------------------------------------------------------
   input/output
   ------------------------------------------------------------------------- *)

fun reall_to_string rl = String.concatWith " " (map rts rl)

fun string_to_reall rls =
  map (valOf o Real.fromString) (String.tokens Char.isSpace rls)

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

fun string_of_ex (l1,l2) = reall_to_string l1 ^ "," ^ reall_to_string l2
fun write_exl file exl = writel file (map string_of_ex exl)

fun ex_of_string s =
  let val (a,b) = pair_of_list (String.tokens (fn x => x = #",") s) in
    (string_to_reall a, string_to_reall b)
  end
fun read_exl file = map ex_of_string (readl file)

(* -------------------------------------------------------------------------
   Biais
   ------------------------------------------------------------------------- *)

val biais = Vector.fromList [1.0]
fun add_biais v = Vector.concat [biais,v]
fun rm_biais v = Vector.fromList (tl (vector_to_list v))

(* -------------------------------------------------------------------------
  Forward propagation (fp) with memory of the steps
  -------------------------------------------------------------------------- *)

fun fp_layer (layer : layer) inv =
  let
    val new_inv = add_biais inv
    val outv = mat_mult (#w layer) new_inv
    val outnv = Vector.map (#a layer) outv
  in
    {layer = layer, inv = new_inv, outv = outv, outnv = outnv}
  end

fun fp_nn nn v = case nn of
    [] => []
  | layer :: m =>
    let val fpdata = fp_layer layer v in fpdata :: fp_nn m (#outnv fpdata) end

(* -------------------------------------------------------------------------
   Backward propagation (bp)
   Takes the data from the forward pass, computes the loss and weight updates
   by gradient descent. Input is j. Output is i. Matrix is Mij.
   ------------------------------------------------------------------------- *)

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
    val dinv     = rm_biais (mat_mult (mat_transpose w) doutv)
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
   Update weights and calculate loss
   ------------------------------------------------------------------------- *)

fun train_nn_one nn (inputv,expectv) = bp_nn (fp_nn nn inputv) expectv

fun transpose_ll ll = case ll of
    [] :: _ => []
  | _ => map hd ll :: transpose_ll (map tl ll)

fun sum_dwll dwll = case dwll of
     [dwl] => dwl
   | _ => map matl_add (transpose_ll dwll)

fun smult_dwl k dwl = map (mat_smult k) dwl

fun mean_square_error v =
  let fun square x = (x:real) * x in
    Math.sqrt (average_rvect (Vector.map square v))
  end

fun bp_loss bpdatal = mean_square_error (#doutnv (last bpdatal))

fun average_loss bpdatall = average_real (map bp_loss bpdatall)

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

(* -------------------------------------------------------------------------
   Statistics
   ------------------------------------------------------------------------- *)

fun sr r = pad 5 "0" (rts_round 3 r)

fun stats_exl exl = 
  let 
    val ll = list_combine (map snd exl) 
    fun f l = 
      print_endline (sr (average_real l ) ^ " " ^ sr (absolute_deviation l)) 
  in
    print_endline "mean deviation";
    app f ll
  end

(* -------------------------------------------------------------------------
   Training
   ------------------------------------------------------------------------- *)

fun train_nn_subbatch nn (subbatch : (vect * vect) list) =
  let
    val bpdatall = map (train_nn_one nn) subbatch
    val dwll = map (map #dw) bpdatall
    val dwl = sum_dwll dwll
  in
    (dwl, average_loss bpdatall)
  end

fun train_nn_batch ncore nn batch =
  let
    val (dwll,lossl) =
      split (parmap_exact ncore (train_nn_subbatch nn) (cut_n ncore batch))
    val dwl = sum_dwll dwll
    val newnn = update_nn nn dwl
  in
    (newnn, average_real lossl)
  end

fun train_nn_epoch ncore lossl nn batchl  = case batchl of
    [] => (nn, average_real lossl)
  | batch :: m =>
    let val (newnn,loss) = train_nn_batch ncore nn batch in
      train_nn_epoch ncore (loss :: lossl) newnn m
    end

fun train_nn_aux ncore nepoch nn bsize exl =
  if nepoch <= 0 then nn else
  let
    val batchl = mk_batch bsize (shuffle exl)
    val (new_nn,loss) = train_nn_epoch ncore [] nn batchl
    val _ = print_endline (its nepoch ^ " " ^ Real.toString loss)
  in
    train_nn_aux ncore (nepoch - 1) new_nn bsize exl
  end

(* -------------------------------------------------------------------------
   Interface:
   - Scaling from [0,1] to [-1,1] to match activation functions range.
   - Converting lists to vectors
   ------------------------------------------------------------------------- *)

fun scale_real x = x * 2.0 - 1.0
fun descale_real x = (x + 1.0) * 0.5
fun scale_in l = Vector.fromList (map scale_real l)
fun scale_out l = Vector.fromList (map scale_real l)
fun descale_out v = map descale_real (vector_to_list v)
fun scale_ex (l1,l2) = (scale_in l1, scale_out l2)

fun train_nn ncore nepoch nn bsize exl =
  let
    val _ = stats_exl exl
    val newexl = map scale_ex exl
  in      
    train_nn_aux ncore nepoch nn bsize newexl
  end

fun infer_nn nn l = (descale_out o #outnv o last o (fp_nn nn) o scale_in) l

end (* struct *)

(* -------------------------------------------------------------------------
   Identity example
   ------------------------------------------------------------------------- *)

(*
load "mlNeuralNetwork"; open mlNeuralNetwork;
load "aiLib"; open aiLib;
load "smlParallel"; open smlParallel;

fun gen_idex dim =
  let
    fun f dim = List.tabulate (dim, fn _ => random_real () - 0.5)
    val x = Vector.fromList (f dim) in (x,x)
  end

val dim = 10;
val bsize = 16;
val nepoch = 100;
val ncore = 1;
val exl = List.tabulate (1000, fn _ => gen_idex dim);
val nn = random_nn (tanh,dtanh) [dim,2* dim,dim];
val (newnn,t) = add_time (train_nn ncore nepoch nn bsize) exl;
val inv = fst (gen_idex dim);
val outv = infer_nn newnn inv;
*)


