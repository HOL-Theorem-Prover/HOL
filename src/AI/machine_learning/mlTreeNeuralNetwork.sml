(* ========================================================================= *)
(* FILE          : mlTreeNeuralNetwork.sml                                   *)
(* DESCRIPTION   : Tree neural network                                       *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure mlTreeNeuralNetwork :> mlTreeNeuralNetwork =
struct

open HolKernel boolLib Abbrev aiLib mlMatrix mlNeuralNetwork smlParallel

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

val nlayer_glob = ref 2

fun id (x:real) = x:real
fun did (x:real) = 1.0

fun const_nn dim arity =
  if arity = 0
  then random_nn (id,did) (id,did) [1,dim]
  else random_nn (tanh,dtanh) (tanh,dtanh)
    (List.tabulate (!nlayer_glob, fn _ => arity * dim + 1) @ [dim])

val oper_compare = cpl_compare Term.compare Int.compare

fun random_opdict dimin cal =
  let val l = map_assoc (fn (_,a) => const_nn dimin a) cal in
    dnew oper_compare l
  end

fun random_headnn (dimin,dimout) =
  random_nn (tanh,dtanh) (tanh,dtanh)
    (List.tabulate (!nlayer_glob, fn _ => dimin + 1) @ [dimout])


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
   Input/output
   ------------------------------------------------------------------------- *)

fun string_of_oper (f,n) = (tts f ^ "," ^ its n)

fun string_of_opdict_one d ((oper,a),nn) =
  its (dfind oper d) ^ " " ^ its a ^ "\n" ^ string_of_nn nn ^ "\nnnstop\n"

fun string_of_opdict opdict =
  let
    val tml = mk_sameorder_set Term.compare (map fst (dkeys opdict))
    val d = dnew Term.compare (number_snd 0 tml)
  in
    String.concatWith "\n" (map (string_of_opdict_one d) (dlist opdict))
  end

fun string_of_tnn {opdict,headnn,dimin,dimout} =
  string_of_nn headnn ^ "\nheadstop\n\n" ^
  string_of_opdict opdict ^ "\nopdictstop"

fun string_of_dhtnn {opdict,headeval,headpoli,dimin,dimout} =
  string_of_nn headeval ^ "\nheadevalstop\n\n" ^
  string_of_nn headpoli ^ "\nheadpolistop\n\n" ^
  string_of_opdict opdict ^ "\nopdictstop"

fun write_tnn file tnn =
  let
    val file_operl = file ^ "_operl"
    val file_dhtnn = file ^ "_tnn"
    val operl = mk_sameorder_set Term.compare (map fst (dkeys (#opdict tnn)))
  in
    writel file_dhtnn [string_of_tnn tnn];
    mlTacticData.export_terml file_operl operl
  end

fun write_dhtnn file dhtnn =
  let
    val file_operl = file ^ "_operl"
    val file_dhtnn = file ^ "_dhtnn"
    val operl = mk_sameorder_set Term.compare (map fst (dkeys (#opdict dhtnn)))
  in
    writel file_dhtnn [string_of_dhtnn dhtnn];
    mlTacticData.export_terml file_operl operl
  end

fun read_opdict_one tos sl =
  let
    val (opers,ns) = pair_of_list (String.tokens Char.isSpace (hd sl))
    val (oper,n) = (tos (string_to_int opers), string_to_int ns)
  in
    ((oper,n),read_nn_sl (tl sl))
  end

fun read_opdict operl sl =
  let
    val d = dnew Int.compare (number_fst 0 operl)
    fun tos i = dfind i d
    val sll = rpt_split_sl "nnstop" sl
  in
    dnew oper_compare (map (read_opdict_one tos) sll)
  end

fun read_tnn_sl operl sl =
  let
    val (l1,contl1) = split_sl "headstop" sl
    val headnn = read_nn_sl l1
    val (l2,_) = split_sl "opdictstop" contl1
    val opdict = read_opdict operl l2
    val dimin = ((snd o mat_dim o #w o hd) headnn) - 1
    val dimout = (fst o mat_dim o #w o last) headnn
  in
    {opdict=opdict,headnn=headnn,dimin=dimin,dimout=dimout}
  end

fun read_tnn file =
  let
    val file_operl = file ^ "_operl"
    val file_tnn = file ^ "_tnn"
    val operl = mlTacticData.import_terml file_operl
    val sl = readl file_tnn
  in
    read_tnn_sl operl sl
  end

(*
load "mlTreeNeuralNetwork";
open aiLib mlNeuralNetwork mlTreeNeuralNetwork;
val file = HOLDIR ^ "/src/AI/test";
val tnn1 = random_tnn (4,2) [(``$+``,2),(``SUC``,1),(``0``,0)];
write_tnn file tnn1;
val tnn2 = read_tnn file;
*)

fun read_dhtnn_sl operl sl =
  let
    val (l1,contl1) = split_sl "headevalstop" sl
    val headeval = read_nn_sl l1
    val (l2,contl2) = split_sl "headpolistop" contl1
    val headpoli = read_nn_sl l2
    val (l3,_) = split_sl "opdictstop" contl2
    val opdict = read_opdict operl l3
    val dimin = ((snd o mat_dim o #w o hd) headpoli) - 1
    val dimout = (fst o mat_dim o #w o last) headpoli
  in
    {opdict=opdict,headeval=headeval,headpoli=headpoli,
     dimin=dimin,dimout=dimout}
  end

fun read_dhtnn file =
  let
    val file_operl = file ^ "_operl"
    val file_dhtnn = file ^ "_dhtnn"
    val operl = mlTacticData.import_terml file_operl
    val sl = readl file_dhtnn
  in
    read_dhtnn_sl operl sl
  end

fun write_operl file operl =
  let
    val file1 = file ^ "_operl_term"
    val file2 = file ^ "_operl_arity"
    val (l1,l2) = split operl
  in
    mlTacticData.export_terml file1 l1;
    writel file2 (map its l2)
  end

fun read_operl file =
  let
    val l1 = mlTacticData.import_terml (file ^ "_operl_term")
    val l2 = map string_to_int (readl (file ^ "_operl_arity"))
  in
    combine (l1,l2)
  end

fun reall_to_string rl =
  String.concatWith " " (map (IEEEReal.toString o Real.toDecimal) rl)

fun string_to_reall rls =
  map (valOf o Real.fromDecimal o valOf o IEEEReal.fromString)
    (String.tokens Char.isSpace rls)

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



(*
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;
val epex = [(``0``,[1.0],[2.0,3.0])];
val file = HOLDIR ^ "/src/AI/trainset";
write_dhexl file trainset;
val trainset1 = read_trainset file;
*)

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

fun prepare_dhtrainset dhtrainset =
  let fun f (tm,rl1,rl2) =
    (order_subtm tm, norm_vect (Vector.fromList rl1),
     norm_vect (Vector.fromList rl2))
  in
    map f dhtrainset
  end

(* -------------------------------------------------------------------------
   Forward propagation
   ------------------------------------------------------------------------- *)

fun fp_op opdict fpdict tm =
  let
    val (f,argl) = strip_comb tm
    val nn = dfind (f,length argl) opdict
      handle NotFound => raise ERR "fp_op" (string_of_oper (f,length argl))
    val invl = map (fn x => #outnv (last (dfind x fpdict))) argl
    val inv = Vector.concat (Vector.fromList [1.0] :: invl) 
  in
    fp_nn nn inv
  end

fun fp_opdict opdict fpdict tml = case tml of
    []      => fpdict
  | tm :: m =>
    let val fpdatal = fp_op opdict fpdict tm in
      fp_opdict opdict (dadd tm fpdatal fpdict) m
    end

fun fp_head headnn fpdict tml =
  let
    val invl = [#outnv (last (dfind (last tml) fpdict))]
    val inv = Vector.concat (Vector.fromList [1.0] :: invl)
  in
    fp_nn headnn inv
  end

fun fp_tnn tnn tml =
  let
    val fpdict = fp_opdict (#opdict tnn) (dempty Term.compare) tml
    val fpdatal = fp_head (#headnn tnn) fpdict tml
  in
    (fpdict,fpdatal)
  end

fun fp_tnn_nohead tnn tml =
  let val fpdict = fp_opdict (#opdict tnn) (dempty Term.compare) tml in
    #outnv (last (dfind (last tml) fpdict))
  end

fun fp_dhtnn dhtnn tml =
  let
    val fpdict = fp_opdict (#opdict dhtnn) (dempty Term.compare) tml
    val fpdataleval = fp_head (#headeval dhtnn) fpdict tml
    val fpdatalpoli = fp_head (#headpoli dhtnn) fpdict tml
  in
    (fpdict,fpdataleval,fpdatalpoli)
  end

fun infer_dhtnn dhtnn tm = 
  let val (_,fpdataleval,fpdatalpoli) = fp_dhtnn dhtnn (order_subtm tm) in
    (
    only_hd (vector_to_list (denorm_vect (#outnv (last fpdataleval)))),
    vector_to_list (denorm_vect (#outnv (last fpdatalpoli)))
    )
  end

(* -------------------------------------------------------------------------
   Backward propagation: bpdict is only used to store the result
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
          val dinvl   = map Vector.fromList (mk_batch dim (tl dinv))
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
    val newdoutnv  =
      (Vector.fromList o tl o vector_to_list o #dinv o hd) bpdatal
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

fun infer_tnn tnn tm =
  let val (_,fpdatal) = fp_tnn tnn (order_subtm tm) in
    vector_to_list (denorm_vect (#outnv (last fpdatal)))
  end

fun infer_tnn_nohead tnn tm =
  vector_to_list (fp_tnn_nohead tnn (order_subtm tm))

(* -------------------------------------------------------------------------
   Train tnn on one example
   ------------------------------------------------------------------------- *)

fun train_tnn_one tnn (tml,expectv) =
  let val (fpdict,fpdatal) = fp_tnn tnn tml in
    bp_tnn (#dimin tnn) (fpdict,fpdatal) (tml,expectv)
  end

fun train_dhtnn_one dhtnn (tml,expecteval,expectpoli) =
  let val (fpdict,fpdataleval,fpdatalpoli) = fp_dhtnn dhtnn tml in
    bp_dhtnn (#dimin dhtnn) (fpdict,fpdataleval,fpdatalpoli)
    (tml,expecteval,expectpoli)
  end

(* -------------------------------------------------------------------------
   Train tnn on one batch
   ------------------------------------------------------------------------- *)

(*
val momentum_glob = ref 0.0
val dwlhead_glob = ref NONE
val dwloper_glob = ref (dempty oper_compare)
*)

(* fun init_dwlglob () =
  (dwlhead_glob := NONE; dwloper_glob := dempty oper_compare) *)

fun update_head headnn bpdatall =
  let
    val dwll = map (map #dw) bpdatall
    val dwl = sum_dwll dwll
    (*
    val dwlmom =
      if isSome (!dwlhead_glob)
      then sum_dwll [smult_dwl (1.0 - (!momentum_glob)) dwl,
                     smult_dwl (!momentum_glob) (valOf (!dwlhead_glob))]
      else dwl
    *)
    val newheadnn = update_nn headnn dwl (* dwlmom *)
    (* val _ = dwlhead_glob := SOME dwlmom *)
    val loss = average_loss bpdatall
  in
    (newheadnn, loss)
  end

fun update_opernn opdict (oper,dwll) =
  let
    val nn    = dfind oper opdict
    val dwl   = sum_dwll dwll
    (* val dwlmom =
      if dmem oper (!dwloper_glob)
      then sum_dwll [smult_dwl (1.0 - (!momentum_glob))  dwl,
                     smult_dwl (!momentum_glob) (dfind oper (!dwloper_glob))]
      else dwl
    *)
    val newnn = update_nn nn dwl (* dwlmom *)
    (* val _ = dwloper_glob := dadd oper dwlmom (!dwloper_glob) *)
  in
    (oper,newnn)
  end

fun random_update_tnn (tnn as {opdict,headnn,dimin,dimout}) =
  {
  opdict = dmap (fn (k,v) => random_update_nn v) opdict,
  headnn = random_update_nn headnn, 
  dimin = dimin, dimout = dimout
  }

fun train_tnn_batch ncore (tnn as {opdict,headnn,dimin,dimout}) batch =
  let
    val (bpdictl,bpdatall) =
      split (parmap_batch ncore (train_tnn_one tnn) batch)
    val (newheadnn,loss) = update_head headnn bpdatall
    val bpdict = dconcat oper_compare bpdictl
    val newnnl = map (update_opernn opdict) (dlist bpdict)
    val newopdict = daddl newnnl opdict
  in
    ({opdict = newopdict, headnn = newheadnn, dimin = dimin, dimout = dimout},
      loss)
  end

(* -------------------------------------------------------------------------
   Train tnn on one epoch
   ------------------------------------------------------------------------- *)

fun train_tnn_epoch_aux ncore lossl tnn batchl = case batchl of
    [] => (tnn, average_real lossl)
  | batch :: m =>
    let val (newtnn,loss) = train_tnn_batch ncore tnn batch in
      train_tnn_epoch_aux ncore (loss :: lossl) newtnn m
    end

fun train_tnn_epoch ncore tnn batchl =
  (
  (* init_dwlglob (); *)
  train_tnn_epoch_aux ncore [] tnn batchl
  )

fun out_tnn tnn tml =
  let val (_,fpdatal) = fp_tnn tnn tml in (#outnv (last fpdatal)) end

fun infer_mse tnn (tml,ev) =
  mean_square_error (diff_rvect ev (out_tnn tnn tml))

fun train_tnn_nepoch (ncore,bsize) n tnn (ptrain,ptest) =
  if n <= 0 then tnn else
  let
    val batchl = (mk_batch bsize o shuffle) ptrain
    val (newtnn,trainloss) = train_tnn_epoch ncore tnn batchl
    val testloss = average_real (map (infer_mse tnn) ptest)
    fun nice r = pad 8 "0" (rts (approx 6 (r / 2.0)))
    val _ = print_endline
      (its n ^ " train: " ^ nice trainloss ^ " test: " ^ nice testloss)
  in
    train_tnn_nepoch (ncore,bsize) (n - 1) newtnn (ptrain,ptest)
  end

fun train_tnn_schedule (ncore,bsize) tnn (ptrain,ptest) schedule =
  case schedule of
    [] => tnn
  | (nepoch, lrate) :: m =>
    let
      val _ = learningrate_glob := lrate
      val _ = print_endline ("learning_rate: " ^ rts lrate)
      val newtnn = train_tnn_nepoch (ncore,bsize) nepoch tnn (ptrain,ptest)
    in
      train_tnn_schedule (ncore,bsize) newtnn (ptrain,ptest) m
    end

(* -------------------------------------------------------------------------
   Training a double-headed tnn
   ------------------------------------------------------------------------- *)

fun train_dhtnn_batch ncore dhtnn batch =
  let
    val {opdict, headeval, headpoli, dimin, dimout} = dhtnn
    val (bpdictl,bpdatall1,bpdatall2) =
      split_triple (parmap_batch ncore (train_dhtnn_one dhtnn) batch)
    val (newheadeval,loss1) = update_head headeval bpdatall1
    val (newheadpoli,loss2) = update_head headpoli bpdatall2
    val bpdict = dconcat oper_compare bpdictl
    val newopdict =
      daddl (map (update_opernn opdict) (dlist bpdict)) opdict
  in
    ({opdict = newopdict, headeval = newheadeval, headpoli = newheadpoli,
     dimin = dimin, dimout = dimout},(loss1,loss2))
  end


fun train_dhtnn_epoch_aux ncore (lossl1,lossl2) dhtnn batchl =
  case batchl of
    [] => (dhtnn, (average_real lossl1, average_real lossl2))
  | batch :: m =>
    let val (newdhtnn,(loss1,loss2)) =
      train_dhtnn_batch ncore dhtnn batch
    in
      train_dhtnn_epoch_aux ncore (loss1 :: lossl1, loss2 :: lossl2)
      newdhtnn m
    end

fun train_dhtnn_epoch ncore dhtnn batchl =
  train_dhtnn_epoch_aux ncore ([],[]) dhtnn batchl

fun random_batchl size x = mk_batch size (shuffle x)

fun pretty_real r = pad 8 "0" (rts (approx 6 r))

fun train_dhtnn_nepoch ncore n dhtnn size eptrain =
  if n <= 0 then dhtnn else
  let
    val batchl = Profile.profile "random_batchl" (random_batchl size) eptrain
    val (newdhtnn,(loss1,loss2)) = train_dhtnn_epoch ncore dhtnn batchl
    val _ = print_endline
      (its n ^ ": eval " ^ pretty_real loss1 ^ " poli " ^ pretty_real loss2)
  in
    train_dhtnn_nepoch ncore (n - 1) newdhtnn size eptrain
  end

fun train_dhtnn_schedule_aux ncore dhtnn bsize eptrain schedule =
  case schedule of
    [] => dhtnn
  | (nepoch, lrate) :: m =>
    let
      val _ = learningrate_glob := lrate
      val _ = print_endline ("learning_rate: " ^ rts lrate)
      val newdhtnn = train_dhtnn_nepoch ncore nepoch dhtnn bsize eptrain
    in
      train_dhtnn_schedule_aux ncore newdhtnn bsize eptrain m
    end

fun train_dhtnn_schedule ncore dhtnn bsize epex schedule =
  let
    val eptrain = prepare_dhtrainset epex
    val dhtnn_new = train_dhtnn_schedule_aux ncore dhtnn bsize eptrain schedule
  in
    dhtnn_new
  end

(* -------------------------------------------------------------------------
   Preparation of the training set for a tnn
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

(* -------------------------------------------------------------------------
   Accuracy test
   ------------------------------------------------------------------------- *)

fun is_accurate tnn (tm,rl) =
  let
    val rl1 = infer_tnn tnn tm
    val rl2 = combine (rl,rl1)
    fun test (x,y) = Real.abs (x - y) < 0.5
  in
    if all test rl2 then true else false
  end

fun accuracy_set tnn set =
  let val correct = filter (is_accurate tnn) set in
    Real.fromInt (length correct) / Real.fromInt (length set)
  end



end (* struct *)
