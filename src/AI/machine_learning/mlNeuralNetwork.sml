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
   Activation and derivatives (with an optimization)
   ------------------------------------------------------------------------- *)

fun idactiv (x:real) = x:real
fun didactiv (x:real) = 1.0
fun tanh x = Math.tanh x
fun dtanh fx = 1.0 - fx * fx

(* -------------------------------------------------------------------------
   Types
   ------------------------------------------------------------------------- *)

type layer = {a : real -> real, da : real -> real, w : real vector vector}
type nn = layer list
type trainparam =
  {ncore: int, verbose: bool,
   learning_rate: real, batch_size: int, nepoch: int}

fun string_of_trainparam {ncore,verbose,learning_rate,batch_size,nepoch} =
  its ncore ^ " " ^ bts verbose ^ " " ^ rts learning_rate ^ " " ^
  its batch_size ^ " " ^ its nepoch

fun trainparam_of_string s =
  let val (a,b,c,d,e) = quintuple_of_list (String.tokens Char.isSpace s) in
    {
    ncore = string_to_int a,
    verbose = string_to_bool b,
    learning_rate = (valOf o Real.fromString) c,
    batch_size = string_to_int d,
    nepoch = string_to_int e
    }
  end

type schedule = trainparam list

fun write_schedule file schedule =
  writel file (map string_of_trainparam schedule)
fun read_schedule file =
  map trainparam_of_string (readl file)

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

fun dimin_nn nn = ((snd o mat_dim o #w o hd) nn) - 1
fun dimout_nn nn = (fst o mat_dim o #w o last) nn

fun random_nn (a,da) sizel =
  let
    val l = diml_of sizel
    fun biais_dim (i,j) = (i,j+1)
    fun f x = {a = a, da = da, w = mat_random (biais_dim x)}
  in
    map f l
  end

(* -------------------------------------------------------------------------
   I/O (assumes tanh activation functions)
   ------------------------------------------------------------------------- *)

local open HOLsexp in
fun enc_nn nn = list_encode enc_mat (map #w nn)
fun dec_nn sexp =
  let
    val matl = valOf (list_decode dec_mat sexp)
      handle Option => raise ERR "dec_nn" ""
    fun f m = {a = tanh, da = dtanh, w = m}
  in
    SOME (map f matl)
  end
end

fun write_nn file nn = write_data enc_nn file nn
fun read_nn file = read_data dec_nn file

fun string_of_ex (l1,l2) = reall_to_string l1 ^ "," ^ reall_to_string l2
fun ex_of_string s =
  let val (a,b) = pair_of_list (String.tokens (fn x => x = #",") s) in
    (string_to_reall a, string_to_reall b)
  end

fun write_exl file exl = writel file (map string_of_ex exl)
fun read_exl file = map ex_of_string (readl file)

(* -------------------------------------------------------------------------
   Biais
   ------------------------------------------------------------------------- *)

val biais = Vector.fromList [1.0]
fun add_biais v = Vector.concat [biais,v]
fun rm_biais v = 
  Vector.tabulate (Vector.length v - 1, fn i => Vector.sub (v,i+1)) 

(* -------------------------------------------------------------------------
  Forward propagation (fp) with memory of the steps
  -------------------------------------------------------------------------- *)

fun mat_dims m =
  let val (a,b) = mat_dim m in "(" ^ its a ^ "," ^ its b ^ ")" end
fun vect_dims v = its (Vector.length v + 1)

fun fp_layer (layer : layer) inv =
  let
    val new_inv = add_biais inv
    val outv = mat_mult (#w layer) new_inv
    val outnv = Vector.map (#a layer) outv
  in
    {layer = layer, inv = new_inv, outv = outv, outnv = outnv}
  end
  handle Subscript =>
    raise ERR "fp_layer" ("dimension: mat-" ^
                          mat_dims (#w layer) ^ " vect-" ^ vect_dims inv)

fun fp_nn nn v = case nn of
    [] => []
  | layer :: m =>
    let val fpdata = fp_layer layer v in fpdata :: fp_nn m (#outnv fpdata) end

(* -------------------------------------------------------------------------
   Backward propagation (bp)
   Takes the data from the forward pass, computes the loss and weight updates
   by gradient descent.
   Input has size j. Output has size i. Matrix has i lines and j columns.
   ------------------------------------------------------------------------- *)

fun mult_rvect_da da v1 v2 =
  let fun f i =  da (Vector.sub (v1,i)) * Vector.sub (v2,i) in
    Vector.tabulate (Vector.length v1, f)
  end


fun bp_layer (fpdata:fpdata) doutnv =
  let
    (* optimization trick *)
    val doutv = mult_rvect_da (#da (#layer fpdata)) (#outnv fpdata) doutnv
    val w        = #w (#layer fpdata)
    fun dw_f i j = Vector.sub (#inv fpdata,j) * Vector.sub (doutv,i)
    val dw       = mat_tabulate dw_f (mat_dim w)
    val dinv     = rm_biais (mat_mult (mat_transpose w) doutv)
  in
   {doutnv = doutnv, doutv = doutv, dinv = dinv, dw = dw}
  end

fun bp_nn_aux rev_fpdatal doutnv =
  case rev_fpdatal of
    [] => []
  | fpdata :: m =>
    let val bpdata = bp_layer fpdata doutnv in
      bpdata :: bp_nn_aux m (#dinv bpdata)
    end

fun bp_nn_doutnv fpdatal doutnv = rev (bp_nn_aux (rev fpdatal) doutnv)

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

fun clip_float (a,b) x = 
  if x < a then a else (if x > b then b else x)

fun mat_add_weight lr m w =
  let 
    fun f i j = clip_float (~4.0,4.0) (mat_sub m i j + lr * mat_sub w i j) 
  in
    mat_tabulate f (mat_dim m)
  end

fun update_layer param (layer, layerwu) =
  let
    val lr = #learning_rate param / Real.fromInt (#batch_size param)
  in
    {a = #a layer, da = #da layer, 
     w = mat_add_weight lr (#w layer) layerwu}
  end

fun update_nn param nn wu = map (update_layer param) (combine (nn,wu))

(* -------------------------------------------------------------------------
   Statistics
   ------------------------------------------------------------------------- *)

fun sr r = pad 7 "0" (rts_round 5 r)

fun stats_exl exl =
  let
    val ll = list_combine (map snd exl)
    fun f l =
      print_endline (sr (average_real l ) ^ " " ^ sr (absolute_deviation l))
  in
    print_endline "mean deviation"; app f ll; print_endline ""
  end

(* -------------------------------------------------------------------------
   Training
   ------------------------------------------------------------------------- *)

fun train_nn_batch param pf nn batch =
  let
    val bpdatall = pf (train_nn_one nn) batch
    val dwll = map (map #dw) bpdatall
    val dwl = sum_dwll dwll
    val newnn = update_nn param nn dwl
  in
    (newnn, average_loss bpdatall)
  end

fun train_nn_epoch param pf lossl nn batchl  = case batchl of
    [] => (nn, average_real lossl)
  | batch :: m =>
    let val (newnn,loss) = train_nn_batch param pf nn batch in
      train_nn_epoch param pf (loss :: lossl) newnn m
    end

fun train_nn_nepoch param pf i nn exl =
  if i >= #nepoch param then nn else
  let
    val batchl = mk_batch (#batch_size param) (shuffle exl)
    val (new_nn,loss) = train_nn_epoch param pf [] nn batchl
    val _ =
      if #verbose param then print_endline (its i ^ " " ^ sr loss) else ()
  in
    train_nn_nepoch param pf (i+1) new_nn exl
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

fun train_nn param nn exl =
  let
    val (pf,close_threadl) = parmap_gen (#ncore param)
    val _ = if #verbose param then stats_exl exl else ()
    val newexl = map scale_ex exl
    val r = train_nn_nepoch param pf 0 nn newexl
  in
    close_threadl (); r
  end

fun infer_nn nn l = (descale_out o #outnv o last o (fp_nn nn) o scale_in) l


end (* struct *)

(* -------------------------------------------------------------------------
   Identity example
   ------------------------------------------------------------------------- *)

(*
load "mlNeuralNetwork"; open mlNeuralNetwork;
load "aiLib"; open aiLib;

(* examples *)
fun gen_idex dim =
  let fun f () = List.tabulate (dim, fn _ => random_real ()) in
    let val x = f () in (x,x) end
  end
;
val dim = 10;
val exl = List.tabulate (1000, fn _ => gen_idex dim);

(* training *)
val nn = random_nn (tanh,dtanh) [dim,4*dim,4*dim,dim];
val param : trainparam =
  {ncore = 1, verbose = true,
   learning_rate = 0.02, batch_size = 16, nepoch = 100}
;
val (newnn,t) = add_time (train_nn param nn) exl;

(* testing *)
val inv = fst (gen_idex dim);
val outv = infer_nn newnn inv;
*)


