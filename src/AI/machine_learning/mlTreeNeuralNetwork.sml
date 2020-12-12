(* ========================================================================= *)
(* FILE          : mlTreeNeuralNetwork.sml                                   *)
(* DESCRIPTION   : Tree neural network                                       *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure mlTreeNeuralNetwork :> mlTreeNeuralNetwork =
struct

open HolKernel boolLib Abbrev aiLib mlMatrix mlNeuralNetwork smlParallel
smlParser mlTacticData

val ERR = mk_HOL_ERR "mlTreeNeuralNetwork"
fun msg param s = if #verbose param then print_endline s else ()
fun msg_err fs es = (print_endline (fs ^ ": " ^ es); raise ERR fs es)

(* -------------------------------------------------------------------------
   Tools for computing the dimensions of neural network operators
   ------------------------------------------------------------------------- *)

type tnndim = (term * int list) list

fun operl_of_term tm =
  let
    val (oper,argl) = strip_comb tm
    val arity = length argl
  in
    (oper,arity) :: List.concat (map operl_of_term argl)
  end

val oper_compare = cpl_compare Term.compare Int.compare;

fun dim_std_arity (nlayer,dim) (oper,a) =
  let
    val dim_alt =
      if is_var oper andalso String.isPrefix "head_" (fst (dest_var oper))
      then 1
      else dim
  in
    (if a = 0 then [0] else List.tabulate (nlayer, fn _ => a * dim)) @
    [dim_alt]
  end

fun dim_std (nlayer,dim) oper =
  dim_std_arity (nlayer,dim) (oper,arity_of oper)

(* -------------------------------------------------------------------------
   Initializiation of a random TNN
   ------------------------------------------------------------------------- *)

type tnn = (term,nn) Redblackmap.dict
type tnne = (term,int) Redblackmap.dict * nn vector

fun oper_nn diml = case diml of
    [] => raise ERR "oper_nn" ""
  | a :: m =>
    if a = 0
    then random_nn (idactiv,didactiv) [0,last m]
    else random_nn (tanh,dtanh) diml

fun random_tnn tnndim = dnew Term.compare (map_snd oper_nn tnndim)

fun random_tnn_std (nlayer,dim) operl =
  random_tnn (map_assoc (dim_std (nlayer,dim)) operl)

fun prepare_tnn tnn =
  let 
    val termnnl = dlist tnn 
    val operd = dnew Term.compare (number_snd 0 (map fst termnnl))
    val nnv = Vector.fromList (map snd termnnl)
  in
    (nnv,operd)
  end
  
fun unprepare_tnn (nnv,operd) =
  dnew Term.compare (combine (dkeys operd, vector_to_list nnv))

(* -------------------------------------------------------------------------
   TNN I/O
   ------------------------------------------------------------------------- *)

local open SharingTables HOLsexp in
fun enc_opernn enc_tm = pair_encode (enc_tm, enc_nn)
fun enc_tnn enc_tm = list_encode (enc_opernn enc_tm)
fun dec_opernn dec_tm = pair_decode (dec_tm, dec_nn)
fun dec_tnn dec_tm = list_decode (dec_opernn dec_tm)
end

fun write_tnn file tnn = write_tmdata (enc_tnn, map fst) file (dlist tnn)
fun read_tnn file = dnew Term.compare (read_tmdata dec_tnn file)

local open SharingTables HOLsexp in
fun enc_tnndime enc_tm = pair_encode (enc_tm, list_encode Integer)
fun enc_tnndim enc_tm = list_encode (enc_tnndime enc_tm)
fun dec_tnndime dec_tm = pair_decode (dec_tm, list_decode int_decode)
fun dec_tnndim dec_tm = list_decode (dec_tnndime dec_tm)
end

fun write_tnndim file tnndim = write_tmdata (enc_tnndim, map fst) file tnndim
fun read_tnndim file = read_tmdata dec_tnndim file

(* -------------------------------------------------------------------------
   TNN Examples: I/O
   ------------------------------------------------------------------------- *)

type tnnex = ((term * real list) list) list
type tnnbatch = (term list * (term * mlMatrix.vect) list) list

fun basicex_to_tnnex ex = map (fn (tm,r) => [(tm,[r])]) ex

local open SharingTables HOLsexp in
val enc_real = String o Real.toString
val dec_real = Option.mapPartial Real.fromString o string_decode
fun enc_sample enc_tm = pair_encode (enc_tm, list_encode enc_real)
fun dec_sample dec_tm = pair_decode (dec_tm, list_decode dec_real)
fun enc_tnnex enc_tm = list_encode (list_encode (enc_sample enc_tm))
fun dec_tnnex dec_tm = list_decode (list_decode (dec_sample dec_tm))
fun tml_of_tnnex l = map fst (List.concat l)
end

fun write_tnnex file ex =
  write_tmdata (enc_tnnex, tml_of_tnnex) file ex
fun read_tnnex file =
  read_tmdata dec_tnnex file

(* -------------------------------------------------------------------------
   TNN Examples: ordering subterms and scaling output values
   ------------------------------------------------------------------------- *)

fun order_subtm tml =
  let
    val d = ref (dempty (cpl_compare Int.compare Term.compare))
    fun traverse tm =
      let
        val (oper,argl) = strip_comb tm
        val nl = map traverse argl
        val n = 1 + sum_int nl
      in
        d := dadd (n, tm) () (!d); n
      end
    val subtml = (app (ignore o traverse) tml; dkeys (!d))
  in
    map snd subtml
  end

fun index_graph operd subtml =
  let
    val subtmil = number_snd 0 subtml
    val subtmd = dnew Term.compare subtmil
    fun f (subtm,i) = 
      let val (oper,argl) = strip_comb subtm in
        (i, (dfind oper operd, map (fn x => dfind x subtmd) argl))
      end
  in
    (map f subtmil, subtmd)
  end

fun prepare_tnnex operd tnnex =
  let fun f x = 
    let 
      val tml = map fst x
      val (graph, subtmd) = index_graph operd (order_subtm tml) 
      val ievl =
        let fun g (tm,rl) = (dfind tm subtmd, scale_out rl) in
          map g x
        end
    in
      (graph,ievl)
    end
  in
    map f tnnex
  end

(* -------------------------------------------------------------------------
   Forward propagation
   ------------------------------------------------------------------------- *)

fun empty_fpv n = Vector.tabulate (n, fn _ => [])

fun fp_oper tnn fpv (oper,argl) =
  let
    val nn = Vector.sub (tnn,oper)
    fun nn_out x = #outnv (last (Vector.sub (fpv,x)))
    val invl = map nn_out argl
    val inv = Vector.concat invl
  in
    fp_nn nn inv
  end
  handle Subscript => msg_err "fp_oper" (its oper)

fun fp_tnn_loop tnn fpv graph = case graph of
    []      => fpv
  | (subtm,(oper,argl)) :: m =>
    let 
      val fpdatal = fp_oper tnn fpv (oper,argl) 
      val newfpv = Vector.update (fpv,subtm,fpdatal)
    in
      fp_tnn_loop tnn newfpv m
    end

fun fp_tnn tnn graph = 
  fp_tnn_loop tnn (empty_fpv (length graph)) graph

val fp_tnn_alt = fp_tnn
fun fp_tnn tnn graph = Profile.profile "fp_tnn" (fp_tnn_alt tnn) graph

(* -------------------------------------------------------------------------
   Backward propagation
   ------------------------------------------------------------------------- *)

fun mat_add_cpl (m1,m2) = mat_add m1 m2

fun update_wud ((oper,operdwl), wud) =
  dadd oper (map mat_add_cpl (combine (operdwl, dfind oper wud))) wud
  handle NotFound => 
  dadd oper operdwl wud
 
fun update_gradv ((subtm,doutnv),gradv) =
  Vector.update (gradv, subtm, vect_add (Vector.sub (gradv,subtm)) doutnv)

fun dimout_fpdatal fpdatal = Vector.length (#outnv (last fpdatal))
fun dimout_subtm fpv subtm = dimout_fpdatal (Vector.sub (fpv,subtm))

fun bp_tnn_loop fpv gradv wud revgraph = case revgraph of
    [] => wud
  | (subtm,(oper,argl)) :: m =>
    let
      val diml = map (dimout_subtm fpv) argl
      val grad = Vector.sub (gradv,subtm)
      val fpdatal = Vector.sub (fpv,subtm)
      val bpdatal = bp_nn_doutnv fpdatal grad
      val dinv = vector_to_list (#dinv (hd bpdatal))
      val dinvl = map Vector.fromList (part_group diml dinv)
      val operdwl = map #dw bpdatal  
      val newgradv = foldl update_gradv gradv (combine (argl,dinvl))
      val newwud = update_wud ((oper,operdwl), wud)
    in
      bp_tnn_loop fpv newgradv newwud m
    end

fun zero_vect n = Vector.tabulate (n, fn _ => 0.0)   

fun bp_tnn fpv (graph,ievl) =
  let
    val gradv0 = 
      Vector.tabulate (Vector.length fpv, 
        fn subtm => zero_vect (dimout_subtm fpv subtm))
    fun f (subtm,ev) =
      let
        val fpdatal = Vector.sub (fpv,subtm)
        val doutnv = diff_rvect ev (#outnv (last fpdatal))
      in
        (subtm,doutnv)
      end
    val gradv = foldl update_gradv gradv0 (map f ievl)
  in
    bp_tnn_loop fpv gradv (dempty Int.compare) (rev graph)
  end

val bp_tnn_alt = bp_tnn
fun bp_tnn a b = Profile.profile "bp_tnn" (bp_tnn_alt a) b

(* -------------------------------------------------------------------------
   Inference
   ------------------------------------------------------------------------- *)

fun infer_tnn tnn tml =
  let
    val (ptnn,operd) = prepare_tnn tnn
    val (graph,subtmd) = index_graph operd (order_subtm tml) 
    val fpv = fp_tnn ptnn graph
    fun f x = descale_out (#outnv (last (Vector.sub (fpv,x))))
  in
    map_assoc (f o (fn x => dfind x subtmd)) tml
  end

fun infer_tnn_basic tnn tm =
  singleton_of_list (snd (singleton_of_list (infer_tnn tnn [tm])))


(* -------------------------------------------------------------------------
   Updating weights
   ------------------------------------------------------------------------- *)

fun sum_operdwll (oper,dwll) = sum_dwll dwll
fun regroup_wud wudl =
  foldl update_wud (hd wudl) (List.concat (map dlist (tl wudl)))


fun update_oper param ((oper,dwl),tnn) =
  let
    val nn = Vector.sub (tnn,oper)
    val newnn = update_nn param nn dwl
  in
    Vector.update (tnn,oper,newnn)
  end

fun update_tnn param wud tnn = 
  foldl (update_oper param) tnn (dlist wud)
 
val update_tnn_alt = update_tnn
fun update_tnn a b c = Profile.profile "update_tnn" (update_tnn_alt a b) c


(* -------------------------------------------------------------------------
   Compute of the loss on the test set
   ------------------------------------------------------------------------- *)

fun se_of fpv (i,ev) =
  let
    val fpdatal = Vector.sub (fpv,i)
    val grad = diff_rvect ev (#outnv (last fpdatal))
    val r1 = vector_to_list grad
    val r2 = map (fn x => x * x) r1
  in
    Math.sqrt (average_real r2)
  end

fun mse_of fpv ievl = average_real (map (se_of fpv) ievl)

fun fp_loss tnn (graph,ievl) = mse_of (fp_tnn tnn graph) ievl

(* -------------------------------------------------------------------------
   Training
   ------------------------------------------------------------------------- *)

fun train_tnn_one tnn (graph,ievl) =
  let
    val fpv = fp_tnn tnn graph
    val wud = bp_tnn fpv (graph,ievl)
  in
    (wud, mse_of fpv ievl)
  end

fun train_tnn_subbatch tnn subbatch =
  let val (wudl,lossl) = split (map (train_tnn_one tnn) subbatch) in
    (regroup_wud wudl, lossl)
  end
 
fun train_tnn_batch param pf tnn batch =
  let
    val subbatchl = cut_modulo (#ncore param) batch
    val (wudl,lossll) = split (pf (train_tnn_subbatch tnn) subbatchl)
    val wud = regroup_wud wudl
  in
    (update_tnn param wud tnn, average_real (List.concat lossll))
  end

fun train_tnn_epoch param pf lossl tnn batchl = case batchl of
    [] => (tnn, average_real lossl)
  | batch :: m =>
    let val (newtnn,loss) = train_tnn_batch param pf tnn batch in
      train_tnn_epoch param pf (loss :: lossl) newtnn m
    end

fun train_tnn_epoch_nopar param lossl tnn batchl = case batchl of
    [] => (tnn, average_real lossl)
  | batch :: m =>
    let val (newtnn,loss) = train_tnn_batch param map tnn batch in
      train_tnn_epoch_nopar param (loss :: lossl) newtnn m
    end

fun train_tnn_nepoch param pf i tnn (train,test) =
  if i >= #nepoch param then tnn else
  let
    val batchl = mk_batch (#batch_size param) (shuffle train)
    val _ = if null batchl then msg_err "train_tnn_nepoch" "empty" else ()
    val (newtnn,loss) = train_tnn_epoch param pf [] tnn batchl
    val testloss = if null test then "" else
      (" test: " ^ pretty_real (average_real (map (fp_loss newtnn) test)))
     val _ = msg param (its i ^ " train: " ^ pretty_real loss ^ testloss)
  in
    train_tnn_nepoch param pf (i+1) newtnn (train,test)
  end

fun train_tnn_schedule schedule tnn (train,test) =
  case schedule of
    [] => tnn
  | param :: m =>
    let
      val _ = msg param ("learning rate: " ^ rts (#learning_rate param))
      val _ = msg param ("ncore: " ^ its (#ncore param))
      val (pf,close_threadl) = parmap_gen (#ncore param)
      val newtnn = train_tnn_nepoch param pf 0 tnn (train,test)
      val _ = close_threadl () 
    in
      train_tnn_schedule m newtnn (train,test)
    end

fun stats_head (oper,rll) =
  let
    val s0 = "  objective: " ^ tts oper
    val s1 = "length: " ^ its (length rll)
    val rll' = list_combine rll
    val s2 = "means: " ^
      String.concatWith " " (map (pretty_real o average_real) rll')
    val s3 = "standard deviations: " ^
      String.concatWith " " (map (pretty_real o standard_deviation) rll')
  in
    String.concatWith "\n  " [s0,s1,s2,s3]
  end

fun stats_tnnex ex =
  if null ex then " empty" else
  let
    fun head_of tm = fst (strip_comb tm)
    val d = dregroup Term.compare (map_fst head_of (List.concat ex))
  in
    its (length ex) ^ " examples\n" ^
    String.concatWith "\n" (map stats_head (dlist d))
  end

fun train_tnn schedule randtnn (trainex,testex) =
  let
    val _ = print_endline ("\ntraining set: " ^ stats_tnnex trainex)
    val _ = print_endline ("testing set: " ^ stats_tnnex testex)
    val _ = print_endline ""
    val (ptnn,operd) = prepare_tnn randtnn
    val (ptrainex,ptestex) = 
      (prepare_tnnex operd trainex, prepare_tnnex operd testex)
   val (tnn,t) = add_time (train_tnn_schedule schedule ptnn)
     (ptrainex, ptestex)
  in
    print_endline ("Tree neural network training time: " ^ rts t); 
    unprepare_tnn (tnn,operd)
  end

(* -------------------------------------------------------------------------
   Accuracy
   ------------------------------------------------------------------------- *)

fun is_accurate_one (rl1,rl2) =
  let
    val rl3 = combine (rl1,rl2)
    fun test (x,y) = Real.abs (x - y) < 0.5
  in
    if all test rl3 then true else false
  end

fun is_accurate tnn e =
  let
    val rll1 = map snd (infer_tnn tnn (map fst e))
    val rll2 = map snd e
  in
    all is_accurate_one (combine (rll1,rll2))
  end

fun tnn_accuracy tnn set =
  let val correct = filter (is_accurate tnn) set in
    Real.fromInt (length correct) / Real.fromInt (length set)
  end

(* -------------------------------------------------------------------------
   Object for training different TNN in parallel
   ------------------------------------------------------------------------- *)

fun train_tnn_fun () (ex,schedule,tnndim) =
  let
    val randtnn = random_tnn tnndim
    val (tnn,t) = add_time (train_tnn schedule randtnn) (ex,[])
  in
    print_endline ("Training time : " ^ rts t); tnn
  end

fun write_noparam file (_:unit) = ()
fun read_noparam file = ()

fun write_tnnarg file (ex,schedule,tnndim) =
  (
  write_tnnex (file ^ "_tnnex") ex;
  write_schedule (file ^ "_schedule") schedule;
  write_tnndim (file ^ "_tnndim") tnndim
  )
fun read_tnnarg file =
  let
    val ex = read_tnnex (file ^ "_tnnex")
    val schedule = read_schedule (file ^ "_schedule")
    val tnndim = read_tnndim (file ^ "_tnndim")
  in
    (ex,schedule,tnndim)
  end

val traintnn_extspec =
  {
  self = "mlTreeNeuralNetwork.traintnn_extspec",
  parallel_dir = default_parallel_dir ^ "_train",
  reflect_globals = fn () => "()",
  function = train_tnn_fun,
  write_param = write_noparam,
  read_param = read_noparam,
  write_arg = write_tnnarg,
  read_arg = read_tnnarg,
  write_result = write_tnn,
  read_result = read_tnn
  }


(* -------------------------------------------------------------------------
   Toy example: learning to guess if a term contains the variable "x"
   ------------------------------------------------------------------------- *)

(*
load "aiLib"; open aiLib;
load "psTermGen"; open psTermGen;
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;

(* terms *)
val vx = mk_var ("x",alpha);
val vy = mk_var ("y",alpha);
val vz = mk_var ("z",alpha);
val vf = ``f:'a->'a->'a``;
val vg = ``g:'a -> 'a``;
val vhead = mk_var ("head_", ``:'a -> 'a``);
val varl = [vx,vy,vz,vf,vg];

(* examples *)
fun contain_x tm = can (find_term (fn x => term_eq x vx)) tm;
fun mk_dataset n =
  let
    val pxl = mk_term_set (random_terml varl (n,alpha) 1000);
    val (px,pnotx) = partition contain_x pxl
  in
    (first_n 100 (shuffle px), first_n 100 (shuffle pnotx))
  end
val (l1,l2) = split (List.tabulate (20, fn n => mk_dataset (n + 1)));
val (l1',l2') = (List.concat l1, List.concat l2);
val (pos,neg) = (map_assoc (fn x => [1.0]) l1', map_assoc (fn x => [0.0]) l2');
val ex0 = shuffle (pos @ neg);
val ex1 = map (fn (a,b) => [(mk_comb (vhead,a),b)]) ex0;
val (trainex,testex) = part_pct 0.9 ex1;

(* TNN *)
val nlayer = 1;
val dim = 16;
val randtnn = random_tnn_std (nlayer,dim) (vhead :: varl);

(* training *)
val trainparam =
  {ncore = 1, verbose = true,
   learning_rate = 0.02, batch_size = 16, nepoch = 100};
val schedule = [trainparam];
val tnn = train_tnn schedule randtnn (trainex,testex);

(* testing *)
val acc = tnn_accuracy tnn testex;
*)

end (* struct *)
