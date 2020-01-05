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
   Random TNN
   ------------------------------------------------------------------------- *)

type tnn = (term,nn) Redblackmap.dict

fun oper_nn diml = case diml of
    [] => raise ERR "oper_nn" ""
  | a :: m =>
    if a = 0 
    then random_nn (idactiv,didactiv) [0,last m] 
    else random_nn (tanh,dtanh) diml

fun random_tnn operdiml = dnew Term.compare (map_snd oper_nn operdiml)

(* -------------------------------------------------------------------------
   TNN I/O
   ------------------------------------------------------------------------- *)

fun write_tnn file tnn =
  let val (l1,l2) = split (dlist tnn) in
    export_terml (file ^ "_operl") l1;
    writel (file ^ "_nnl") 
      [String.concatWith "\n\nnnstop\n\n" (map string_of_nn l2)]
  end

fun read_tnn file =
  let
    val l1 = import_terml (file ^ "_operl") 
    val l2 = map read_nn_sl (rpt_split_sl "nnstop" (readl (file ^ "_nnl")))
  in
    dnew Term.compare (combine (l1,l2))
  end

(* -------------------------------------------------------------------------
   TNN Examples: I/O
   ------------------------------------------------------------------------- *)

type tnnex = (term list * real list) list

fun write_tnnex file ex =
  let val (tmll,rll) = split ex in
    writel (file ^ "_group") (map (its o length) tmll);
    export_terml (file ^ "_term") (List.concat tmll);
    writel (file ^ "_reall") (map reall_to_string rll)
  end

fun part_group groupl l = case groupl of
    [] => if null l then [] else raise ERR "part_group" ""
  | a :: m => let val (l1,l2) = part_n a l in
                l1 :: part_group m l2
              end

fun read_tnnex file =
  let
    val tml = import_terml (file ^ "_term")
    val groupl = map string_to_int (readl (file ^ "_group"))
    val tmll = part_group groupl tml
    val rll = map string_to_reall (readl (file ^ "_reall"))
  in
    combine (tmll,rll)
  end

(* -------------------------------------------------------------------------
   TNN Examples: ordering subterms and scaling output values
   ------------------------------------------------------------------------- *)

fun fst_compare cmp (a,b) = cmp (fst a, fst b)

fun order_subtm tml =
  let
    fun f x =
      let val (_,argl) = strip_comb x in
        (x, mk_fast_set Term.compare argl) :: List.concat (map f argl)
      end
    val tmdepl = mk_fast_set (fst_compare Term.compare) 
      (List.concat (map f tml))
  in
    topo_sort Term.compare tmdepl
  end

fun prepare_tnnex tnnex =
  let fun f (tml,rl) = 
    (order_subtm tml, 
     map_snd (fn x => Vector.fromList [scale_real x]) (combine (tml,rl)))
  in 
    map f tnnex
  end

(* -------------------------------------------------------------------------
   Fixed embedding
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

fun fp_oper tnn fpdict tm =
  let
    val (f,argl) = strip_comb tm
    val nn = dfind f tnn handle NotFound => embed_nn f
    val invl = map (fn x => #outnv (last (dfind x fpdict))) argl
    val inv = Vector.concat invl
  in
    fp_nn nn inv
  end
  handle Subscript => msg_err "fp_oper" (fst (dest_var tm))

fun fp_tnn_aux tnn fpdict tml = case tml of
    []      => fpdict
  | tm :: m => 
    let val fpdatal = fp_oper tnn fpdict tm in 
      fp_tnn_aux tnn (dadd tm fpdatal fpdict) m
    end

fun fp_tnn tnn tml = fp_tnn_aux tnn (dempty Term.compare) tml

(* -------------------------------------------------------------------------
   Backward propagation
   ------------------------------------------------------------------------- *)

fun sum_operdwll (oper,dwll) = [sum_dwll dwll]

fun dimout_fpdatal fpdatal = Vector.length (#outnv (last fpdatal))
fun dimout_tm fpdict tm = dimout_fpdatal (dfind tm fpdict)

fun bp_tnn_aux doutnvdict fpdict bpdict revtml = case revtml of
    []      => dmap sum_operdwll bpdict
  | tm :: m =>
    let
      val (oper,argl) = strip_comb tm
      val diml = map (dimout_tm fpdict) argl
      val doutnvl = dfind tm doutnvdict
      fun f doutnv =
        let
          val fpdatal = dfind tm fpdict
          val bpdatal = bp_nn_doutnv fpdatal doutnv
          val dinv    = vector_to_list (#dinv (hd bpdatal))
          val dinvl = map Vector.fromList (part_group diml dinv)
        in
          (map #dw bpdatal, combine (argl,dinvl))
        end
      val rl            = map f doutnvl
      val operdwll      = map fst rl
      val operdwl       = sum_dwll operdwll
      val tmdinvl       = List.concat (map snd rl)
      val newdoutnvdict = dappendl tmdinvl doutnvdict
      val newbpdict     = dappend (oper,operdwl) bpdict
    in
      bp_tnn_aux newdoutnvdict fpdict newbpdict m
    end

fun bp_tnn fpdict (tml,tmevl) =
  let 
    fun f (tm,ev) =
      let
        val fpdatal = dfind tm fpdict
        val doutnv = diff_rvect ev (#outnv (last fpdatal))
      in
        (tm,[doutnv])
      end
    val doutnvdict = dnew Term.compare (map f tmevl)
  in
    bp_tnn_aux doutnvdict fpdict (dempty Term.compare) (rev tml)
  end

(* -------------------------------------------------------------------------
   Inference
   ------------------------------------------------------------------------- *)

fun infer_tnn tnn tml =
  let 
    val fpdict = fp_tnn tnn (order_subtm tml) 
    val fpdatal = dfind (only_hd tml) fpdict
  in
    descale_out (#outnv (last fpdatal))
  end

(* -------------------------------------------------------------------------
   Training
   ------------------------------------------------------------------------- *)

fun se_of fpdict (tm,ev) =
  let
    val fpdatal = dfind tm fpdict
    val doutnv = diff_rvect ev (#outnv (last fpdatal))
    val r = only_hd (vector_to_list doutnv)
  in
    r * r
  end

fun mse_of fpdict tmevl =
  Math.sqrt (sum_real (map (se_of fpdict) tmevl))
  
fun train_tnn_one tnn (tml,tmevl) =
  let 
    val fpdict = fp_tnn tnn tml
    val bpdict = bp_tnn fpdict (tml,tmevl)
  in
    (bpdict, mse_of fpdict tmevl)
  end
 
fun train_tnn_subbatch tnn subbatch =
  let val (bpdictl,lossl) = split (map (train_tnn_one tnn) subbatch) in
    (dmap sum_operdwll (dconcat Term.compare bpdictl), lossl)
  end

fun update_oper param ((oper,dwll),tnn) =
  if is_embedding oper then tnn else
  let
    val nn = dfind oper tnn
    val dwl = sum_dwll dwll
    val newnn = update_nn param nn dwl
  in
    dadd oper newnn tnn
  end

fun train_tnn_batch param pf tnn batch =
  let
    val subbatchl = cut_modulo (#ncore param) batch
    val (bpdictl,lossll) = split (pf (train_tnn_subbatch tnn) subbatchl)
    val bpdict = dconcat Term.compare bpdictl
  in
    (foldl (update_oper param) tnn (dlist bpdict), 
     average_real (List.concat lossll))
  end

fun train_tnn_epoch param pf lossl tnn batchl = case batchl of
    [] => (tnn, average_real lossl)
  | batch :: m =>
    let val (newtnn,loss) = train_tnn_batch param pf tnn batch in
      train_tnn_epoch param pf (loss :: lossl) newtnn m
    end

(* todo: add support for testset *)
fun train_tnn_nepoch param pf i tnn (train,test) =
  if i >= #nepoch param then tnn else
  let
    val batchl = mk_batch (#batch_size param) (shuffle train)
    val _ = if null batchl then msg_err "train_tnn_nepoch" "empty" else ()
    val (newtnn,loss) = train_tnn_epoch param pf [] tnn batchl
    val _ = msg param (its i ^ " train: " ^ pretty_real loss)
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
      val r = train_tnn_schedule m newtnn (train,test)
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
    val _ = print_endline ("train " ^ output_info (map snd trainex))
    val _ = print_endline ("test  " ^ output_info (map snd testex))
    val (tnn,t) = add_time (train_tnn_schedule schedule randtnn) 
      (prepare_tnnex trainex, prepare_tnnex testex)
  in
    print_endline ("Tree neural network training time: " ^ rts t); tnn
  end

(* -------------------------------------------------------------------------
   Accuracy
   ------------------------------------------------------------------------- *)

fun is_accurate_tnn tnn (tml,rl) =
  let
    val rl1 = infer_tnn tnn tml
    val rl2 = combine (rl,rl1)
    fun test (x,y) = Real.abs (x - y) < 0.5
  in
    if all test rl2 then true else false
  end

fun tnn_accuracy tnn set =
  let val correct = filter (is_accurate_tnn tnn) set in
    Real.fromInt (length correct) / Real.fromInt (length set)
  end

(* -------------------------------------------------------------------------
   Example: learn to tell if a term contains the variable "x" or not
   ------------------------------------------------------------------------- *)

(*
load "aiLib"; open aiLib;
load "psTermGen"; open psTermGen;
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;

(* examples *)
fun contain_x tm = can (find_term (fn x => term_eq x ``x:'a``)) tm;
val varl = [``x:'a``,``y:'a``,``z:'a``,``f:'a->'a->'a``,``g:'a -> 'a``];
val head = mk_var ("head", ``:'a -> 'a``);

fun mk_dataset n =
  let
    val pxl = mk_term_set (random_terml varl (n,alpha) 100);
    val (px,pnotx) = partition contain_x pxl
  in
    (first_n 100 (shuffle px), first_n 100 (shuffle pnotx))
  end
val (l1,l2) = split (List.tabulate (20, fn n => mk_dataset (n + 1)));
val (l1',l2') = (List.concat l1, List.concat l2);
val (pos,neg) = (map_assoc (fn x => [1.0]) l1', map_assoc (fn x => [0.0]) l2');
val l = map_fst (single o (fn x => mk_comb (head,x))) 
  (shuffle (pos @ neg));

val (trainex,testex) = 
  part_n (Real.round (Real.fromInt (length l) * 0.9)) l;

(* training *)
val train_param =
  {ncore = 1, verbose = true,
   learning_rate = 0.02, batch_size = 16, nepoch = 100};
val schedule = [train_param];

val operdiml = 
  [(``x:'a``,[0,8]), (``y:'a``,[0,8]), (``z:'a``,[0,8]),
   (``f:'a->'a->'a``,[16,16,8]), (``g:'a -> 'a``,[8,8,8]),
   (head, [8,1])
   ];
val randtnn = random_tnn operdiml;
val tnn = train_tnn schedule randtnn (trainex,testex);

(* testing *)
val tm = fst (hd (shuffle testex));
val r = infer_tnn tnn tm;
val acc = tnn_accuracy tnn testex;
*)

end (* struct *)
