(* ========================================================================= *)
(* FILE          : mlTreeNeuralNetwork.sml                                   *)
(* DESCRIPTION   : Tree neural network                                       *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure mlTreeNeuralNetwork :> mlTreeNeuralNetwork =
struct

open HolKernel boolLib Abbrev aiLib mlMatrix mlNeuralNetwork 
smlParallel mlTacticData

val ERR = mk_HOL_ERR "mlTreeNeuralNetwork"
fun msg param s = if #verbose param then print_endline s else ()
fun msg_err fs es = (print_endline (fs ^ ": " ^ es); raise ERR fs es)
  
(* -------------------------------------------------------------------------
   Objects
   ------------------------------------------------------------------------- *)

type vect = real vector
type mat = real vector vector
type tnn = (term,nn) Redblackmap.dict

(* -------------------------------------------------------------------------
   Random tree neural network
   ------------------------------------------------------------------------- *)

fun oper_nn diml = case diml of
    [] => raise ERR "oper_nn" ""
  | a :: m =>
    if a = 0 
    then random_nn (idactiv,didactiv) [0,last m] 
    else random_nn (tanh,dtanh) diml

fun random_tnn operdiml = dnew Term.compare (map_snd oper_nn operdiml)

(* -------------------------------------------------------------------------
   Input/output
   ------------------------------------------------------------------------- *)

fun write_tnn file tnn =
  let 
    val (l1,l2) = split (dlist tnn) 
    fun string_of_tnn tnn =
      let fun f (oper,nn) = string_of_nn nn in
        String.concatWith "\nnnstop\n" (map f (dlist tnn)) 
      end
  in
    export_terml (file ^ "_operl") l1;
    writel (file ^ "_nnl") (map string_of_tnn l2)
  end

fun read_tnn file =
  let
    val l1 = mlTacticData.import_terml (file ^ "_operl")
    fun read_tnn_sl sl = map read_nn_sl (rpt_split_sl "nnstop" sl)
    val l2 = read_tnn_sl (readl (file ^ "_nnl"))
  in
    dnew Term.compare (combine (l1,l2))
  end

(*
load "aiLib"; open aiLib;
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;
val file = HOLDIR ^ "/src/AI/machine_learning/test";


(* extract dimension of nn: *)
val dimin = ((snd o mat_dim o #w o hd) nn) - 1
val dimout = (fst o mat_dim o #w o last) nn
*)

(*


fun write_dhex file epex =
  let
    val file_term = file ^ "_term"
    val file_eval = file ^ "_eval"
    val file_poli = file ^ "_poli"
    val (terml,rll1,rll2) = split_triple epex
  in
    mlTacticData.export_terml file_term terml;
    writel file_eval (map reall_to_string rll1);
    writel file_poli (map reall_to_string rll2)
  end

fun read_dhex file =
  let
    val file_term = file ^ "_term"
    val file_eval = file ^ "_eval"
    val file_poli = file ^ "_poli"
    val terml = mlTacticData.import_terml file_term
    val rll1 = map string_to_reall (readl file_eval)
    val rll2 = map string_to_reall (readl file_poli)
  in
    combine_triple (terml,rll1,rll2)
  end

fun write_tnnex file ex =
  let
    val file_term = file ^ "_term"
    val file_eval = file ^ "_eval"
    val (terml,rll) = split ex
  in
    mlTacticData.export_terml file_term terml;
    writel file_eval (map reall_to_string rll)
  end

fun read_tnnex file =
  let
    val file_term = file ^ "_term"
    val file_eval = file ^ "_eval"
    val terml = mlTacticData.import_terml file_term
    val rll = map string_to_reall (readl file_eval)
  in
    combine (terml,rll)
  end

fun write_dhtnnparam file {operl,nlayer_oper,nlayer_headeval,
  nlayer_headpoli,dimin,dimpoli} =
  (
  write_operl (file ^ "_operl") operl;
  writel (file ^ "_param") [String.concatWith " "
    (map its [nlayer_oper,nlayer_headeval,nlayer_headpoli,dimin,dimpoli])]
  )
fun read_dhtnnparam file =
  let
    val operl = read_operl (file ^ "_operl")
    val (a,b,c,d,e) = quintuple_of_list (map string_to_int
      (String.tokens Char.isSpace (only_hd (readl (file ^ "_param")))))
  in
    {
    operl = operl,
    nlayer_oper = a,
    nlayer_headeval = b,
    nlayer_headpoli = c,
    dimin = d,
    dimpoli = e
    }
  end

(* -------------------------------------------------------------------------
   Scaling output values and ordering subterms
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

fun prepare_tnnex tnnex =
  let fun f (tm,rl) = (order_subtm tm, scale_out rl) in
    map f tnnex
  end

fun prepare_dhex dhex =
  let fun f (tm,rl1,rl2) = (order_subtm tm, scale_out rl1, scale_out rl2) in
    map f dhex
  end

(* -------------------------------------------------------------------------
   Fixed neural embedding derived by the name of the variable.
   Useful for fixing an embedding in one leaf of the tree.
   ------------------------------------------------------------------------- *)

val embedding_prefix = "embedding_"

fun is_embedding v =
  is_var v andalso String.isPrefix embedding_prefix (fst (dest_var v))

fun embed_nn v =
  if is_embedding v then
    let
      val vs = fst (dest_var v)
      val n1 = String.size embedding_prefix
      val ntot = String.size vs
      val es = String.substring (vs,n1,ntot-n1)
      val e1 = string_to_reall es
      val e2 = map (fn x => Vector.fromList [x]) e1
    in
      [{a = idactiv, da = didactiv, w = Vector.fromList e2}]
    end
  else msg_err "embed_nn" (fst (dest_var v))

fun mk_embedding_var rv =
  mk_var (embedding_prefix ^ reall_to_string (vector_to_list rv), bool)

(* -------------------------------------------------------------------------
   Forward propagation
   ------------------------------------------------------------------------- *)

fun fp_op dim opdict fpdict tm =
  let
    val (f,argl) = strip_comb tm
    val nn = dfind (f,length argl) opdict handle NotFound => embed_nn f
    val invl = map (fn x => #outnv (last (dfind x fpdict))) argl
    val inv = Vector.concat invl
  in
    fp_nn nn inv
  end
  handle Subscript => msg_err "fp_op" (its dim ^ "," ^ (fst (dest_var tm)))

fun fp_opdict dim opdict fpdict tml = case tml of
    []      => fpdict
  | tm :: m =>
    let 
      val fpdatal = fp_op dim opdict fpdict tm 
    in
      fp_opdict dim opdict (dadd tm fpdatal fpdict) m
    end

fun fp_head headnn fpdict tml =
  let val inv = #outnv (last (dfind (last tml) fpdict)) in
    fp_nn headnn inv
  end

fun fp_tnn tnn tml =
  let
    val fpdict = fp_opdict (#dimin tnn) (#opdict tnn) (dempty Term.compare) tml
    val fpdatal = fp_head (#headnn tnn) fpdict tml
  in
    (fpdict,fpdatal)
  end

fun fp_dhtnn dhtnn tml =
  let
    val fpdict = fp_opdict
      (#dimin dhtnn) (#opdict dhtnn) (dempty Term.compare) tml
    val fpdataleval = fp_head (#headeval dhtnn) fpdict tml
    val fpdatalpoli = fp_head (#headpoli dhtnn) fpdict tml
  in
    (fpdict,fpdataleval,fpdatalpoli)
  end

(* -------------------------------------------------------------------------
   Backward propagation
   ------------------------------------------------------------------------- *)

fun sum_operdwll (oper,dwll) = [sum_dwll dwll]

fun bp_tnn_opdict_aux dim doutnvdict fpdict bpdict revtml = case revtml of
    []      => dmap sum_operdwll bpdict
  | tm :: m =>
    let
      val (oper,argl) = strip_comb tm
      val opern = (oper,length argl)
      val doutnvl = dfind tm doutnvdict
      fun f doutnv =
        let
          val fpdatal = dfind tm fpdict
          val bpdatal = bp_nn_wocost fpdatal doutnv
          val dinv    = vector_to_list (#dinv (hd bpdatal))
          val dinvl   = map Vector.fromList (mk_batch dim dinv)
        in
          (map #dw bpdatal, combine (argl,dinvl))
        end
      val rl            = map f doutnvl
      val operdwll      = map fst rl
      val operdwl       = sum_dwll operdwll
      val tmdinvl       = List.concat (map snd rl)
      val newdoutnvdict = dappendl tmdinvl doutnvdict
      val newbpdict     = dappend (opern,operdwl) bpdict
    in
      bp_tnn_opdict_aux dim newdoutnvdict fpdict newbpdict m
    end

fun bp_tnn_opdict dim doutnvdict fpdict bpdict tml =
  bp_tnn_opdict_aux dim doutnvdict fpdict bpdict (rev tml)

fun bp_tnn_head fpdatal (tml,expectv) =
  let
    val outnv      = #outnv (last fpdatal)
    val doutnv     = diff_rvect expectv outnv
    val bpdatal    = bp_nn_wocost fpdatal doutnv
    val newdoutnv  = #dinv (hd bpdatal)
  in
    ((last tml,newdoutnv), bpdatal)
  end

fun bp_tnn dim (fpdict,fpdatal) (tml,expectv) =
  let
    val (tmgrad,bpdatal) = bp_tnn_head fpdatal (tml,expectv)
    val doutnvdict = dappend tmgrad (dempty Term.compare)
    val bpdict = bp_tnn_opdict dim doutnvdict fpdict (dempty oper_compare) tml
  in
    (bpdict, bpdatal)
  end

fun bp_dhtnn dim (fpdict,fpdataleval,fpdatalpoli)
  (tml,expecteval,expectpoli) =
  let
    val (tmgrad1,bpdataleval) = bp_tnn_head fpdataleval (tml,expecteval)
    val (tmgrad2,bpdatalpoli) = bp_tnn_head fpdatalpoli (tml,expectpoli)
    val doutnvdict = dappendl [tmgrad1,tmgrad2] (dempty Term.compare)
    val bpdict = bp_tnn_opdict dim doutnvdict fpdict (dempty oper_compare) tml
  in
    (bpdict,bpdataleval,bpdatalpoli)
  end

(* -------------------------------------------------------------------------
   Inference
   ------------------------------------------------------------------------- *)

fun infer_opdict dim opdict tml =
  let val fpdict = fp_opdict dim opdict (dempty Term.compare) tml in
    #outnv (last (dfind (last tml) fpdict))
  end

fun infer_tnn tnn tm =
  let val (_,fpdatal) = fp_tnn tnn (order_subtm tm) in
    descale_out (#outnv (last fpdatal))
  end

fun infer_tnn_nohead tnn tm =
  infer_opdict (#dimin tnn) (#opdict tnn) (order_subtm tm)

fun infer_dhtnn dhtnn tm =
  let val (_,fpdataleval,fpdatalpoli) = fp_dhtnn dhtnn (order_subtm tm) in
    (
    only_hd (descale_out (#outnv (last fpdataleval))),
    descale_out (#outnv (last fpdatalpoli))
    )
  end

fun infer_dhtnn_nohead dhtnn tm =
  infer_opdict (#dimin dhtnn) (#opdict dhtnn) (order_subtm tm)

fun infer_mse tnn (tml,ev) =
  let
    fun out_tnn tnn tml =
      let val (_,fpdatal) = fp_tnn tnn tml in (#outnv (last fpdatal)) end
  in
    mean_square_error (diff_rvect ev (out_tnn tnn tml))
  end

(* -------------------------------------------------------------------------
   Training a tree neural network
   ------------------------------------------------------------------------- *)

fun train_tnn_one tnn (tml,expectv) =
  let val (fpdict,fpdatal) = fp_tnn tnn tml in
    bp_tnn (#dimin tnn) (fpdict,fpdatal) (tml,expectv)
  end

fun train_tnn_subbatch tnn subbatch =
  let
    val {opdict,headnn,dimin,dimout} = tnn
    val (bpdictl,bpdatall) = split (map (train_tnn_one tnn) subbatch)
    val bpdict1 = dconcat oper_compare bpdictl
    val bpdict2 = filter (not o is_embedding o fst o fst) (dlist bpdict1)
    val bpdict3 = dnew oper_compare bpdict2
    fun f (oper,dwll) = [sum_dwll dwll]
    val bpdict4 = dmap f bpdict3
    val dwl_head = sum_dwll (map (map #dw) bpdatall)
  in
    (bpdict4, dwl_head, average_loss bpdatall)
  end

fun update_opernn param opdict (oper,dwll) =
  let
    val nn    = dfind oper opdict
    val dwl   = sum_dwll dwll
    val newnn = update_nn param nn dwl
  in
    (oper,newnn)
  end

fun train_tnn_batch param pf (tnn as {opdict,headnn,dimin,dimout}) batch =
  let
    val subbatchl = cut_modulo (#ncore param) batch
    val (bpdictl, dwl_headl, lossl) =
      split_triple (pf (train_tnn_subbatch tnn) subbatchl)
    val newheadnn = update_nn param headnn (sum_dwll dwl_headl)
    val bpdict = dconcat oper_compare bpdictl
    val newnnl = map (update_opernn param opdict) (dlist bpdict)
    val newopdict = daddl newnnl opdict
  in
    (
    {opdict = newopdict, headnn = newheadnn, dimin = dimin, dimout = dimout},
    average_real lossl
    )
  end

fun train_tnn_epoch param pf lossl tnn batchl = case batchl of
    [] => (tnn, average_real lossl)
  | batch :: m =>
    let val (newtnn,loss) = train_tnn_batch param pf tnn batch in
      train_tnn_epoch param pf (loss :: lossl) newtnn m
    end

fun train_tnn_nepoch param pf i tnn (ptrain,ptest) =
  if i >= #nepoch param then tnn else
  let
    val batchl = mk_batch (#batch_size param) (shuffle ptrain)
    val (newtnn,r1) = train_tnn_epoch param pf [] tnn batchl
    val r2 = if null ptest then 0.0 else
      average_real (map (infer_mse tnn) ptest)
    val sr = pretty_real
    val _ = msg param (its i ^ " train: " ^ sr r1 ^ " test: " ^ sr r2)
  in
    train_tnn_nepoch param pf (i+1) newtnn (ptrain,ptest)
  end

fun train_tnn_schedule schedule tnn (ptrain,ptest) =
  case schedule of
    [] => tnn
  | param :: m =>
    let
      val _ = msg param ("learning rate: " ^ rts (#learning_rate param))
      val _ = msg param ("ncore: " ^ its (#ncore param))
      val (pf,close_threadl) = parmap_gen (#ncore param)
      val newtnn = train_tnn_nepoch param pf 0 tnn (ptrain,ptest)
      val r = train_tnn_schedule m newtnn (ptrain,ptest)
    in
      (close_threadl (); r)
    end

fun output_info exl =
  if null exl then "empty" else
  let
    val l = list_combine exl
    val meanl = map (rts o approx 6 o average_real) l
    val devl = map (rts o approx 6 o standard_deviation) l
  in
    "  length: " ^ int_to_string (length exl) ^ "\n" ^
    "  mean: " ^ String.concatWith " " meanl ^ "\n" ^
    "  deviation: " ^ String.concatWith " " devl
  end

fun train_tnn schedule randtnn (trainex,testex) =
  let
    val _ = print_endline ("trainset " ^ output_info (map snd trainex))
    val _ = print_endline ("testset  " ^ output_info (map snd testex))
    val _ = if length trainex < #batch_size (hd schedule)
            then msg_err "train_tnn" "too few examples"
            else ()
    val pset = (prepare_tnnex trainex, prepare_tnnex testex)
    val (tnn,t) = add_time (train_tnn_schedule schedule randtnn) pset
  in
    print_endline ("Tree neural network training time: " ^ rts t); tnn
  end

(* -------------------------------------------------------------------------
   Training a double-headed tree neural network
   ------------------------------------------------------------------------- *)

fun train_dhtnn_one dhtnn (tml,expecteval,expectpoli) =
  let 
    val (fpdict,fpdataleval,fpdatalpoli) = fp_dhtnn dhtnn tml 
  in
    bp_dhtnn (#dimin dhtnn) (fpdict,fpdataleval,fpdatalpoli)
    (tml,expecteval,expectpoli)
  end

fun train_dhtnn_subbatch dhtnn subbatch =
  let
    val {opdict, headeval, headpoli, dimin, dimpoli} = dhtnn
    val (bpdictl,bpdatall1,bpdatall2) =
      split_triple (map (train_dhtnn_one dhtnn) subbatch)
    val dwle = sum_dwll (map (map #dw) bpdatall1)
    val dwlp = sum_dwll (map (map #dw) bpdatall2)
    val bpdict1 = dconcat oper_compare bpdictl
    val bpdict2 = filter (not o is_embedding o fst o fst) (dlist bpdict1)
    val bpdict3 = dnew oper_compare bpdict2
    fun f (oper,dwll) = [sum_dwll dwll]
    val bpdict4 = dmap f bpdict3
  in
    (bpdict4, (dwle,dwlp), (average_loss bpdatall1, average_loss bpdatall2))
  end

fun train_dhtnn_batch param pf dhtnn batch =
  let
    val subbatchl = cut_modulo (#ncore param) batch
    val {opdict, headeval, headpoli, dimin, dimpoli} = dhtnn
    val (bpdictl,dwllheadcpl,losscpl) =
      split_triple (pf (train_dhtnn_subbatch dhtnn) subbatchl)
    val (dwlle,dwllp) = split dwllheadcpl
    val (lossle,losslp) = split losscpl
    val newheadeval = update_nn param headeval (sum_dwll dwlle)
    val newheadpoli = update_nn param headpoli (sum_dwll dwllp)
    val dwlloper = dlist (dconcat oper_compare bpdictl)
    val newopdict = daddl (map (update_opernn param opdict) dwlloper) opdict
  in
    (
    {opdict = newopdict, headeval = newheadeval, headpoli = newheadpoli,
     dimin = dimin, dimpoli = dimpoli},
    (average_real lossle, average_real losslp)
    )
  end

fun train_dhtnn_epoch param pf (lossl1,lossl2) dhtnn batchl =
  case batchl of
    [] => (dhtnn, (average_real lossl1, average_real lossl2))
  | batch :: m =>
    let 
      val (newdhtnn,(loss1,loss2)) = train_dhtnn_batch param pf dhtnn batch
    in
      train_dhtnn_epoch param pf (loss1 :: lossl1, loss2 :: lossl2)
      newdhtnn m
    end

fun train_dhtnn_nepoch param pf i dhtnn dhex =
  if i >= #nepoch param then dhtnn else
  let
    val batchl = mk_batch (#batch_size param) (shuffle dhex)
    val (newdhtnn,(r1,r2)) = train_dhtnn_epoch param pf ([],[]) dhtnn batchl
    val sr = pretty_real
    val _ = msg param (its i ^ ": eval " ^ sr r1 ^ " poli " ^ sr r2)
  in
    train_dhtnn_nepoch param pf (i + 1) newdhtnn dhex
  end

fun train_dhtnn_schedule schedule dhtnn dhex = case schedule of
    [] => dhtnn
  | param :: m =>
    let
      val _ = msg param ("learning rate: " ^ rts (#learning_rate param))
      val _ = msg param ("ncore: " ^ its (#ncore param))
      val (pf,close_threadl) = parmap_gen (#ncore param)
      val newdhtnn = train_dhtnn_nepoch param pf 0 dhtnn dhex
      val r = train_dhtnn_schedule m newdhtnn dhex
    in
      close_threadl (); r
    end

fun train_dhtnn schedule dhtnn dhex =
  let
    val _ = print_endline ("eval " ^ output_info (map #2 dhex))
    val _ = print_endline ("poli " ^ output_info (map #3 dhex))
    val newdhex = prepare_dhex dhex
    val (newdhtnn,t) = add_time (train_dhtnn_schedule schedule dhtnn) newdhex
  in
    print_endline
      ("Double-headed tree neural network training time: " ^ rts t);
    newdhtnn
  end

(* -------------------------------------------------------------------------
   Measuring the accuracy of a tree neural network
   ------------------------------------------------------------------------- *)

fun is_accurate_tnn tnn (tm,rl) =
  let
    val rl1 = infer_tnn tnn tm
    val rl2 = combine (rl,rl1)
    fun test (x,y) = Real.abs (x - y) < 0.5
  in
    if all test rl2 then true else false
  end

fun tnn_accuracy tnn set =
  let val correct = filter (is_accurate_tnn tnn) set in
    Real.fromInt (length correct) / Real.fromInt (length set)
  end
*)
(* -------------------------------------------------------------------------
   Example: learn to tell if a term contains the variable "x" or not
   ------------------------------------------------------------------------- *)

(*
load "aiLib"; open aiLib;
load "psTermGen"; open psTermGen;
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;
load "Profile";

(*** objective ***)
fun contain_x tm = can (find_term (fn x => term_eq x ``x:'a``)) tm;

(*** generation of training examples ***)
val varl = [``x:'a``,``y:'a``,``z:'a``,``f:'a->'a->'a``,``g:'a -> 'a``];
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

(* 90/10 split *)
val l = shuffle (pos @ neg);
val (trainex,testex) = part_n (Real.round (Real.fromInt (length l) * 0.9)) l;

(*** tree neural network ***)
val tnn_param =
  {
  operl = map_assoc arity_of varl,
  nlayer_oper = 2, nlayer_headnn = 2,
  dimin = 16, dimout = 1
  };

Profile.reset_all ();
smlParallel.use_thread_flag := true;
val randtnn = random_tnn tnn_param;
val schedule =
  [{ncore=4, verbose=true, learning_rate=0.02, batch_size=16, nepoch=10}];
val newtnn = Profile.profile "4" (train_tnn schedule randtnn) (trainex,testex);
val schedule =
  [{ncore=1, verbose=true, learning_rate=0.02, batch_size=16, nepoch=10}];
val newtnn = Profile.profile "1" (train_tnn schedule randtnn) (trainex,testex);
val _ = smlParallel.use_thread_flag := true;
val schedule =
  [{ncore=1, verbose=true, learning_rate=0.02, batch_size=16, nepoch=10}];
val newtnn =
  Profile.profile "1t" (train_tnn schedule randtnn) (trainex,testex);
Profile.results ();

(*** inference example ***)
val tm = fst (hd (shuffle testex));
val r = infer_tnn newtnn tm;
val acc = tnn_accuracy newtnn trainex;
*)

end (* struct *)
