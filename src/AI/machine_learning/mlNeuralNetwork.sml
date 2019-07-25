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
   Cheating experiments
   ------------------------------------------------------------------------- *)

val cheat_flag = ref false
val cheat_nex = ref 64
val cheat_dim = ref 20

fun rev_vector v =
  let val vn = Vector.length v in
    Vector.tabulate (vn, fn i => Vector.sub (v,vn - i - 1))
  end

fun random_set nex =
  let
    fun f _ = Vector.tabulate (!cheat_dim, fn _ => random_real () - 0.5)
    val l = List.tabulate (nex, f)
  in
    map (fn x => (x, rev_vector x)) l
  end


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

fun write_nn file nn = 
  if !cheat_flag then () else (writel file o map string_of_nn) [nn]

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

val nn_cheat = random_nn (tanh,dtanh) (tanh,dtanh) 
    (List.tabulate (20,fn _ => !cheat_dim))

fun read_nn file = 
  if !cheat_flag 
  then nn_cheat
  else read_nn_sl (readl file)

fun string_of_v v = reall_to_string (vector_to_list v)
fun string_of_vv (v1,v2) = string_of_v v1 ^ "," ^ string_of_v v2

fun write_ex file argl = 
  if !cheat_flag then () else 
    (writel file o map string_of_vv) (only_hd argl)

fun vv_of_string s = 
  let val (a,b) = pair_of_list (String.tokens (fn x => x = #",") s) in
    (Vector.fromList (string_to_reall a), 
     Vector.fromList (string_to_reall b))
  end

fun read_ex file = 
  if !cheat_flag 
  then [random_set (!cheat_nex)]
  else [map vv_of_string (readl file)]

(*---------------------------------------------------------------------------
  Biais
  ---------------------------------------------------------------------------*)

val biais = Vector.fromList [1.0]
fun add_biais v = Vector.concat [biais,v]
fun rm_biais v = Vector.fromList (tl (vector_to_list v))

(*---------------------------------------------------------------------------
  Forward propagation (fp) with memory of the steps
  ---------------------------------------------------------------------------*)

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

fun infer_nn nn v = #outnv (last (fp_nn nn v))

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

fun profile_w s f a b = Profile.profile s (f a) b

fun train_nn_subbatch nn subbatch =
  let
    val bpdatall = map (train_nn_one nn) subbatch
    val dwll = map (map #dw) bpdatall
    val dwl = sum_dwll dwll
  in
    (dwl, average_loss bpdatall)
  end

fun write_result file (dwl,loss) =
  if !cheat_flag then () else
    (writel (file ^ "_dwl") [string_of_wl dwl];
     writel (file ^ "_loss") [rts loss]) 

val dwl_cheat = map #w (random_nn (tanh,dtanh) (tanh,dtanh)
    (List.tabulate (20,fn _ => !cheat_dim)))

fun read_result file =
  if !cheat_flag
  then (dwl_cheat, 0.0)
  else 
    ((read_wl_sl o readl) (file ^ "_dwl"),
    (valOf o Real.fromString o hd o readl) (file ^ "_loss"))

val ext_flag = ref false

fun bts b = if b then "true" else "false"

val extspec : (nn, (vect * vect) list, (mat list * real)) extspec =
  {
  self = "mlNeuralNetwork.extspec",
  reflect_globals = 
    fn () => "(mlNeuralNetwork.cheat_nex := " ^ its (!cheat_nex) ^ ";" ^
              "mlNeuralNetwork.cheat_dim := " ^ its (!cheat_dim) ^ ";" ^
              "mlNeuralNetwork.cheat_flag := " ^ bts (!cheat_flag) ^ ")",
  function = profile_w "train_nn_subbatch" train_nn_subbatch,
  write_param = profile_w "write_nn" write_nn,
  read_param = Profile.profile "read_nn" read_nn,
  write_argl = profile_w "write_ex" write_ex,
  read_argl = Profile.profile "read_ex" read_ex,
  write_result = profile_w "write_result" write_result,
  read_result = Profile.profile "read_result" read_result
  }

fun train_nn_batch ncore nn batch =
  let
    val subbatchl = cut_n ncore batch
    val (dwll,lossl) = split (
      Profile.profile "par"
      (if !ext_flag 
      then parmap_exact_extern ncore extspec nn
      else if ncore = 1
           then map (train_nn_subbatch nn) 
           else parmap_exact ncore (train_nn_subbatch nn)
      ) subbatchl)
    val dwl = Profile.profile "sum" sum_dwll dwll
    val newnn = Profile.profile "upd" (update_nn nn) dwl
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
load "mlNeuralNetwork"; open mlNeuralNetwork;
load "smlParallel"; open smlParallel;
open aiLib;

val v1 = Vector.fromList [1.0,~1.0];
val v2 = Vector.fromList [~1.0,1.0];

val exl = [(v1,v1),(v2,v2)];

fun maxv (v:real vector) = 
  if Vector.sub (v,0) > Vector.sub (v,1) then v1 else v2;

fun negv (v:real vector) = 
  if Vector.sub (v,0) > Vector.sub (v,1) then v2 else v1;

fun is_accurate (v: real vector) (v' : real vector) =
  (Vector.sub (v,0) > Vector.sub (v,1) andalso
    Vector.sub (v',0) > Vector.sub (v',1))
  orelse
  (Vector.sub (v,0) < Vector.sub (v,1) andalso
    Vector.sub (v',0) < Vector.sub (v',1))


fun train_nn2nn_one (nn1,nn2) (inputv,expectv) =
  let 
    val fpdatal1 = fp_nn nn1 (add_biais inputv)
    val interv = maxv (#outnv (last fpdatal1))
    val fpdatal2 = fp_nn nn2 (add_biais interv)
    val bpdatal2 = bp_nn fpdatal2 expectv
    val outputv = #outnv (last fpdatal2)
    val ev = if is_accurate outputv expectv then interv else negv interv
    val bpdatal1 = bp_nn fpdatal1 ev
  in
    (bpdatal1,bpdatal2)
  end;

fun train_nn2nn_two (nn1,nn2) =
  let
    val (bpdatall1, bpdatall2) = split (map (train_nn2nn_one (nn1,nn2)) exl)
    val dwll1 = map (map #dw) bpdatall1
    val dwl1 = sum_dwll dwll1
    val dwll2 = map (map #dw) bpdatall2
    val dwl2 = sum_dwll dwll2
    val loss1 = average_loss bpdatall1
    val loss2 = average_loss bpdatall2
    val _ = print_endline (rts loss1 ^ " " ^ rts loss2)
  in
    (update_nn nn1 dwl1, update_nn nn2 dwl2)
  end

fun train_nn2nn n nnc =
  if n <= 0 then nnc else
  let
    val _ = print (" " ^ its n ^ " ")
    val new_nnc = train_nn2nn_two nnc
  in
    train_nn2nn (n - 1) new_nnc
  end

fun infer_nnc (nn1,nn2) v = 
  (infer_nn nn2 o add_biais o maxv o infer_nn nn1 o add_biais) v;

val nn1 = random_nn (tanh,dtanh) (tanh,dtanh) [3,10,2];
val nn2 = random_nn (tanh,dtanh) (tanh,dtanh) [3,10,2];
val nnc = train_nn2nn 1000 (nn1,nn2);
map (infer_nn (fst nnc)) (map (add_biais o fst) exl);

map (infer_nnc nnc) (map fst exl);
map (infer_nnc (nn1,nn2)) (map fst exl);




learningrate_glob := 0.02;
val dim = 20;
val nex = 1024;
val nepoch = 5;
val bsize = 16;
val nn = random_nn (tanh,dtanh) (tanh,dtanh) 
  (List.tabulate (20,fn _ => dim));
val set = random_set nex;

val ncore = 1; reset_all (); ext_flag := false; cheat_flag := false;
val (_,t) = add_time (train_nn ncore nepoch nn bsize) set;
results ();

val ncore = 1; reset_all (); ext_flag := false; cheat_flag := false;
val (_,t) = add_time (parmap_exact 4 (train_nn ncore nepoch nn bsize)) [set,set,set,set];
results ();



val ncore = 2;
reset_all ();
ext_flag := true;
cheat_flag := true;
cheat_dim := dim;
cheat_nex := bsize div ncore;
print_endline (its (!cheat_nex));
print_endline (its (!cheat_dim));
parallel_dir := "/dev/shm/thibault";
val threadl = boss_start_exact ncore extspec;
val (_,t1) = add_time (train_nn ncore nepoch nn bsize) set;
boss_stop_exact threadl;
ext_flag := false;
results ();
*)

(* I/O test 
val (_,t1) = add_time (#write_argl extspec "test") [set];
val (_,t2) = add_time (#read_argl extspec) "test";
val (_,t3) = add_time (#write_param extspec "test") nn;
val (_,t4) = add_time (#read_param extspec) "test";
val l1 = List.tabulate (20000, fn _ => random_real ());
val (l2,t) = add_time (map rts) l1;
val (_,t) = add_time (writel "test") l2
val (l3,t) = add_time (map (valOf o Real.fromString)) l2;
val (l4,t) = add_time (map (fn x => Real.round (x * 10000000.0))) l1;
val (l5,t) = add_time (map its) l4;
val (l6,t) = add_time (map string_to_int) l5;
*)
