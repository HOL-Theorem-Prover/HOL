(* ========================================================================= *)
(* FILE          : mlTreeNeuralNetwork.sml                                   *)
(* DESCRIPTION   : Tree neural network                                       *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure mlTreeNeuralNetwork :> mlTreeNeuralNetwork =
struct

open HolKernel boolLib Abbrev aiLib mlMatrix mlNeuralNetwork

val ERR = mk_HOL_ERR "mlTreeNeuralNetwork"
val debugdir = HOLDIR ^ "/src/AI/machine_learning/debug"
fun debug s = debug_in_dir debugdir "mlTreeNeuralNetwork" s

(* -------------------------------------------------------------------------
   Type
   ------------------------------------------------------------------------- *)

type vect = real vector
type mat = real vector vector
type opdict = ((term * int),nn) Redblackmap.dict
type tnn =
  {opdict: opdict, headnn: nn, dimin: int, dimout: int}
type dhtnn =
  {opdict: opdict, headeval: nn, headpoli: nn, dimin: int, dimout: int}

(* -------------------------------------------------------------------------
   Random tree neural network
   ------------------------------------------------------------------------- *)

fun const_nn dim activ arity =
  if arity = 0
  then random_nn activ activ [1,dim]
  else random_nn activ activ [arity * dim + 1, dim, dim]

val oper_compare = cpl_compare Term.compare Int.compare

fun random_opdict dimin cal =
  let val l = map_assoc (fn (_,a) => const_nn dimin (tanh,dtanh) a) cal in
    dnew oper_compare l
  end

fun random_headnn (dimin,dimout) =
  random_nn (tanh,dtanh) (tanh,dtanh) [dimin+1,dimin,dimout]

fun random_tnn (dimin,dimout) operl =
  {
  opdict = random_opdict dimin operl,
  headnn = random_headnn (dimin,dimout),
  dimin = dimin,
  dimout = dimout
  }

fun random_dhtnn (dimin,dimout) operl =
  {
  opdict = random_opdict dimin operl,
  headeval = random_headnn (dimin,1),
  headpoli = random_headnn (dimin,dimout),
  dimin = dimin,
  dimout = dimout
  }

(* -------------------------------------------------------------------------
   Printing
   ------------------------------------------------------------------------- *)

fun string_of_oper (f,n) = (tts f ^ "," ^ its n)

fun string_of_opdictone ((oper,a),nn) =
  tts oper ^ " " ^ its a ^ "\n\n" ^ string_of_nn nn

fun string_of_opdict opdict =
  String.concatWith "\n\n\n" (map string_of_opdictone (dlist opdict))

fun string_of_tnn {opdict,headnn,dimin,dimout} =
  "head\n\n" ^ string_of_nn headnn ^ "\n\n\n" ^ string_of_opdict opdict

fun string_of_trainset trainset =
  let fun f (tm,rl) =
    tts tm ^ ": " ^ String.concatWith " " (map (rts o (approx 4)) rl)
  in
    String.concatWith "\n" (map f trainset)
  end

(* -------------------------------------------------------------------------
   Normalization/Denormalization
   ------------------------------------------------------------------------- *)

fun order_subtm tm =
  let
    fun f x =
      let val (_,argl) = strip_comb x in
        (x, mk_fast_set Term.compare argl) :: List.concat (map f argl)
      end
    fun cmp (a,b) = Term.compare (fst a, fst b)
    fun g x = mk_fast_set cmp (f x)
  in
    topo_sort Term.compare (g tm)
  end

fun norm_vect v = Vector.map (fn x => 2.0 * (x - 0.5)) v
fun denorm_vect v = Vector.map (fn x => 0.5 * x + 0.5) v

fun add_bias v = Vector.concat [Vector.fromList [1.0], v]

(* -------------------------------------------------------------------------
   Forward propagation
   ------------------------------------------------------------------------- *)

fun fp_opdict opdict fpdict tml = case tml of
    []      => fpdict
  | tm :: m =>
    let
      val (f,argl) = strip_comb tm
      val nn = dfind (f,length argl) opdict
        handle NotFound =>
          raise ERR "fp_tnn" (string_of_oper (f,length argl))
      val invl = map (fn x => #outnv (last (dfind x fpdict))) argl
      val inv = Vector.concat (Vector.fromList [1.0] :: invl)
      val fpdatal = fp_nn nn inv
    in
      fp_opdict opdict (dadd tm fpdatal fpdict) m
    end

fun fp_tnn (opdict,headnn) tml =
  let
    val fpdict = fp_opdict opdict (dempty Term.compare) tml
    val invl = [#outnv (last (dfind (last tml) fpdict))]
    val inv = Vector.concat (Vector.fromList [1.0] :: invl)
    val fpdatal = fp_nn headnn inv
  in
    (fpdict, fpdatal)
  end

(* -------------------------------------------------------------------------
   Backward propagation
   ------------------------------------------------------------------------- *)

fun bp_tnn_aux dim doutnvdict fpdict bpdict revtml = case revtml of
    []      => bpdict
  | tm :: m =>
    let
      val (oper,argl) = strip_comb tm
      val doutnvl = dfind tm doutnvdict
      fun f doutnv =
        let
          val fpdatal     = dfind tm fpdict
          val bpdatal     = bp_nn_wocost fpdatal doutnv
          val operbpdatal = ((oper,length argl),bpdatal)
          val dinv        = vector_to_list (#dinv (hd bpdatal))
          val dinvl       = map Vector.fromList (mk_batch dim (tl dinv))
        in
          (operbpdatal, combine (argl,dinvl))
          handle HOL_ERR _ => raise ERR "bp_tnn" ""
        end
      val rl            = map f doutnvl
      val operbpdatall  = map fst rl
      val tmdinvl       = List.concat (map snd rl)
      val newdoutnvdict = dappendl tmdinvl doutnvdict
      val newbpdict     = dappendl operbpdatall bpdict
    in
      bp_tnn_aux dim newdoutnvdict fpdict newbpdict m
    end

fun bp_tnn dim (fpdict,fpdatal) (tml,expectv) =
  let
    val outnv      = #outnv (last fpdatal)
    val doutnv     = diff_rvect expectv outnv
    val bpdatal    = bp_nn_wocost fpdatal doutnv
    val newdoutnv  =
      (Vector.fromList o tl o vector_to_list o #dinv o hd) bpdatal
    val doutnvdict = dappend (last tml,newdoutnv) (dempty Term.compare)
    val bpdict     = dempty oper_compare
  in
    (bp_tnn_aux dim doutnvdict fpdict bpdict (rev tml), bpdatal)
  end

(* -------------------------------------------------------------------------
   Inference
   ------------------------------------------------------------------------- *)

fun infer_tnn (tnn: tnn) tm =
  let
    val tnn' = (#opdict tnn, #headnn tnn)
    val (_,fpdatal) = fp_tnn tnn' (order_subtm tm)
  in
    vector_to_list (denorm_vect (#outnv (last fpdatal)))
  end

(* -------------------------------------------------------------------------
   Training a tnn for one epoch
   ------------------------------------------------------------------------- *)

fun train_tnn_one tnn (tml,expectv) =
  let
    val tnn' = (#opdict tnn, #headnn tnn)
    val dim = #dimin tnn
    val (fpdict,fpdatal) = fp_tnn tnn' tml
  in
    bp_tnn dim (fpdict,fpdatal) (tml,expectv)
  end

fun update_head bsize headnn bpdatall =
  let
    val dwl       = average_bpdatall bsize bpdatall
    val newheadnn = update_nn headnn dwl
    val loss      = average_loss bpdatall
  in
    (newheadnn, loss)
  end

fun string_of_oper (optm,i) = term_to_string optm ^ " " ^ int_to_string i

fun update_opernn bsize opdict (oper,bpdatall) =
  let
    val nn       = dfind oper opdict
      handle NotFound => raise ERR "update_opernn" (string_of_oper oper)
    val dwl      = average_bpdatall bsize bpdatall
    val loss     = average_loss bpdatall
    val newnn    = update_nn nn dwl
  in
    (oper,newnn)
  end

val tto_timer = ref 0.0
val upd_timer1 = ref 0.0
val upd_timer2 = ref 0.0
val upd_timer3 = ref 0.0
val upd_timer4 = ref 0.0

fun train_tnn_batch ncore (tnn as {opdict,headnn,dimin,dimout}) batch =
  let
    val (bpdictl,bpdatall) =
      split (
        total_time tto_timer (parmap ncore (train_tnn_one tnn)) batch
      )
    val bsize = length batch
    val (newheadnn,loss) = total_time upd_timer1 
      (update_head bsize headnn) bpdatall
    val bpdict    = total_time upd_timer2 (dconcat oper_compare) bpdictl
    val newnnl    = total_time upd_timer3 
      (map (update_opernn bsize opdict)) (dlist bpdict)
    val newopdict = total_time upd_timer4 (daddl newnnl) opdict
  in
    ({opdict = newopdict, headnn = newheadnn, dimin = dimin, dimout = dimout},
      loss)
  end

fun train_tnn_epoch_aux ncore lossl tnn batchl = case batchl of
    [] => (tnn, average_real lossl)
  | batch :: m =>
    let val (newtnn,loss) = train_tnn_batch ncore tnn batch in
      train_tnn_epoch_aux ncore (loss :: lossl) newtnn m
    end

fun train_tnn_epoch ncore tnn batchl = 
  train_tnn_epoch_aux ncore [] tnn batchl

fun out_tnn tnn tml =
  let val (_,fpdatal) = fp_tnn (#opdict tnn, #headnn tnn) tml in
    (#outnv (last fpdatal))
  end

fun infer_mse tnn (tml,ev) =
  mean_square_error (diff_rvect ev (out_tnn tnn tml))

(* choose a uniform distribution on the difficulty to create ptrain *)
fun interval (step:real) (a,b) =
  if a + (step / 2.0) > b then [b] else a :: interval step (a + step,b)

fun train_tnn_nepoch (ncore,bsize) n tnn (ptrain,ptest) =
  if n <= 0 then tnn else
  let
    val batchl = (mk_batch bsize o shuffle) ptrain
    val (newtnn,trainloss) = train_tnn_epoch ncore tnn batchl
    val testloss = average_real (map (infer_mse tnn) ptest)
    fun nice r = pad 8 "0" (rts (approx 6 (r / 2.0)))
    val _ = print_endline
      ("train: " ^ nice trainloss ^ " test: " ^ nice testloss)
  in
    train_tnn_nepoch (ncore,bsize) (n - 1) newtnn (ptrain,ptest)
  end

fun train_tnn_schedule_aux (ncore,bsize) tnn (ptrain,ptest) schedule =
  case schedule of
    [] => tnn
  | (nepoch, lrate) :: m =>
    let
      val _ = learning_rate := lrate
      val _ = print_endline ("learning_rate: " ^ rts lrate)
      val newtnn = train_tnn_nepoch (ncore,bsize) nepoch tnn (ptrain,ptest)
    in
      train_tnn_schedule_aux (ncore,bsize) newtnn (ptrain,ptest) m
    end

fun train_tnn_schedule (ncore,bsize) tnn (ptrain,ptest) schedule =
  train_tnn_schedule_aux (ncore,bsize) tnn (ptrain,ptest) schedule

(* -------------------------------------------------------------------------
   Training a double-headed tnn
   ------------------------------------------------------------------------- *)

fun train_dhtnn_batch ncore dhtnn batch1 batch2 =
  let
    val {opdict, headeval, headpoli, dimin, dimout} = dhtnn
    val tnneval = {opdict = opdict, headnn = headeval,
                   dimin = dimin, dimout = 1}
    val tnnpoli = {opdict = opdict, headnn = headpoli,
                   dimin = dimin, dimout = dimout}
    val (bpdictl1,bpdatall1) =
      split (parmap ncore (train_tnn_one tnneval) batch1)
    val (bpdictl2,bpdatall2) =
      split (parmap ncore (train_tnn_one tnnpoli) batch2)
    val bsize = length batch1 + length batch2
    val (newheadeval,loss1) = update_head bsize headeval bpdatall1
    val (newheadpoli,loss2) = update_head bsize headpoli bpdatall2
    val bpdict = dconcat oper_compare (bpdictl1 @ bpdictl2)
    val newnnl = map (update_opernn bsize opdict) (dlist bpdict)
    val newopdict = daddl newnnl opdict
  in
    ({opdict = newopdict, headeval = newheadeval, headpoli = newheadpoli,
     dimin = dimin, dimout = dimout},
     (loss1,loss2))
  end

fun train_dhtnn_epoch_aux ncore (lossl1,lossl2) dhtnn batchl1 batchl2 =
  case (batchl1,batchl2) of
    ([],_) => (dhtnn, (average_real lossl1, average_real lossl2))
  | (_,[]) => (dhtnn, (average_real lossl1, average_real lossl2))
  | (batch1 :: m1, batch2 :: m2) =>
    let val (newdhtnn,(loss1,loss2)) =
      train_dhtnn_batch ncore dhtnn batch1 batch2
    in
      train_dhtnn_epoch_aux ncore (loss1 :: lossl1, loss2 :: lossl2)
      newdhtnn m1 m2
    end

fun train_dhtnn_epoch ncore dhtnn batchl1 batchl2 =
  train_dhtnn_epoch_aux ncore ([],[]) dhtnn batchl1 batchl2

fun train_dhtnn_nepoch ncore n dhtnn size (etrain,ptrain) =
  if n <= 0 then dhtnn else
  let
    val batchl1 = mk_batch size (shuffle etrain)
    val batchl2 = mk_batch size (shuffle ptrain)
    val (newdhtnn,(newloss1,newloss2)) =
      train_dhtnn_epoch ncore dhtnn batchl1 batchl2
    val _ = print_endline
      ("eval_loss: " ^ pad 8 "0" (rts (approx 6 newloss1)) ^ " " ^
       "poli_loss: " ^ pad 8 "0" (rts (approx 6 newloss2)))
  in
    train_dhtnn_nepoch ncore (n - 1) newdhtnn size (etrain,ptrain)
  end

fun train_dhtnn_schedule ncore dhtnn bsize (etrain,ptrain) schedule =
  case schedule of
    [] => dhtnn
  | (nepoch, lrate) :: m =>
    let
      val _ = learning_rate := lrate
      val _ = print_endline ("learning_rate: " ^ rts lrate)
      val newdhtnn = 
        train_dhtnn_nepoch ncore nepoch dhtnn bsize (etrain,ptrain)
    in
      train_dhtnn_schedule ncore newdhtnn bsize (etrain,ptrain) m
    end

(* -------------------------------------------------------------------------
   Preparation of the training set
   ------------------------------------------------------------------------- *)

fun prepare_trainset trainset =
  let fun f (tm,rl) = (order_subtm tm, norm_vect (Vector.fromList rl)) in
    map f trainset
  end

fun trainset_info trainset =
  if null trainset then "empty testset" else
  let
    val l = list_combine (map snd trainset)
    val meanl = map (rts o approx 6 o average_real) l
    val devl = map (rts o approx 6 o standard_deviation) l
  in
    "  length: " ^ int_to_string (length trainset) ^ "\n" ^
    "  mean: " ^ String.concatWith " " meanl ^ "\n" ^
    "  deviation: " ^ String.concatWith " " devl
  end

fun prepare_train_tnn (ncore,bsize) randtnn (trainset,testset) schedule =
  if null trainset then (print_endline "empty trainset"; randtnn) else
  let
    val _ = print_endline ("trainset " ^ trainset_info trainset)
    val _ = print_endline ("testset  " ^ trainset_info testset)
    val bsize    = if length trainset < bsize then 1 else bsize
    val pset = (prepare_trainset trainset, prepare_trainset testset)
    val (tnn, nn_tim) =
      add_time (train_tnn_schedule (ncore,bsize) randtnn pset) schedule
  in
    print_endline ("  NN Time: " ^ rts nn_tim);
    tnn
  end



end (* struct *)
