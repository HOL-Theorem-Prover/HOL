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
   External parallelism
   ------------------------------------------------------------------------- *)

val ml_gencode_dir = ref (HOLDIR ^ "/src/AI/machine_learning/gencode")
fun gencode_dir () = !ml_gencode_dir

fun dhtnn_file () = gencode_dir () ^ "/dhtnn"
fun exl_file () = gencode_dir () ^ "/exl"
fun widin_file wid = gencode_dir () ^ "/" ^ its wid ^ "/in"
fun widout_file wid = gencode_dir () ^ "/" ^ its wid ^ "/out"
fun widscript_file wid = 
  gencode_dir () ^ "/" ^ its wid ^ "/script" ^ its wid ^ ".sml"
fun widbatchl_file wid = gencode_dir () ^ "/" ^ its wid ^ "/batchl"
fun widdwl_file wid = gencode_dir () ^ "/" ^ its wid ^ "/dwl"

fun writel_atomic file sl =
  (writel (file ^ "_temp") sl; 
   OS.FileSys.rename {old = file ^ "_temp", new=file})
fun readl_rm file =
  let val sl = readl file in OS.FileSys.remove file; sl end

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

fun id (x:real) = x:real
fun did (x:real) = 1.0

fun const_nn dim activ arity =
  if arity = 0
  then random_nn (id,did) (id,did) [1,dim]
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
   Random tree neural network
   ------------------------------------------------------------------------- *)

fun id (x:real) = x:real
fun did (x:real) = 1.0

fun const_nn2 dim activ arity =
  if arity = 0
  then random_nn (id,did) (id,did) [1,dim]
  else random_nn activ activ [arity * dim + 1, arity * dim, dim, dim]

fun random_opdict2 dimin cal =
  let val l = map_assoc (fn (_,a) => const_nn2 dimin (tanh,dtanh) a) cal in
    dnew oper_compare l
  end

fun random_headnn2 (dimin,dimout) =
  random_nn (tanh,dtanh) (tanh,dtanh) [dimin+1,dimin,dimout]

fun random_tnn2 (dimin,dimout) operl =
  {
  opdict = random_opdict2 dimin operl,
  headnn = random_headnn2 (dimin,dimout),
  dimin = dimin,
  dimout = dimout
  }

(* -------------------------------------------------------------------------
   Output
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
  string_of_nn headnn ^ "\nheadstop\n\n" ^ string_of_opdict opdict

fun string_of_dhtnn {opdict,headeval,headpoli,dimin,dimout} =
  string_of_nn headeval ^ "\nheadevalstop\n\n" ^ 
  string_of_nn headpoli ^ "\nheadpolistop\n\n" ^ 
  string_of_opdict opdict ^ "\nopdictstop"

fun write_dhtnn file dhtnn =
  let
    val file_operl = file ^ "_operl"
    val file_dhtnn = file ^ "_dhtnn"
    val operl = mk_sameorder_set Term.compare (map fst (dkeys (#opdict dhtnn)))
  in
    writel file_dhtnn [string_of_dhtnn dhtnn];
    mlTacticData.export_terml file_operl operl
  end

fun write_operl file dhtnn =
  let
    val file_operl = file ^ "_operl"
    val operl = mk_sameorder_set Term.compare (map fst (dkeys (#opdict dhtnn)))
  in
    mlTacticData.export_terml file_operl operl
  end

fun write_dhtnn_nooper file dhtnn =
  let val file_dhtnn = file ^ "_dhtnn" in
    writel file_dhtnn [string_of_dhtnn dhtnn]
  end

(* -------------------------------------------------------------------------
   Input
   ------------------------------------------------------------------------- *)

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

fun read_operl file = mlTacticData.import_terml (file ^ "_operl")

fun read_dhtnn_nooper operl file =
  read_dhtnn_sl operl (readl (file ^ "_dhtnn"))

(* 
load "mlTreeNeuralNetwork"; 
open aiLib mlNeuralNetwork mlTreeNeuralNetwork;
val file = HOLDIR ^ "/src/AI/test";
val dhtnn1 = random_dhtnn (4,2) [(``$+``,2),(``SUC``,1),(``0``,0)];
val (_,t1) = add_time (write_dhtnn file) dhtnn1;
val (dhtnn2,t2) = add_time read_dhtnn file;
*)

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

fun fp_dhtnn dhtnn tml =
  let
    val fpdict = fp_opdict (#opdict dhtnn) (dempty Term.compare) tml
    val fpdataleval = fp_head (#headeval dhtnn) fpdict tml
    val fpdatalpoli = fp_head (#headpoli dhtnn) fpdict tml
  in
    (fpdict,fpdataleval,fpdatalpoli)
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
   Train tnn on a part of the mini-batch
   ------------------------------------------------------------------------- *)

fun string_of_namedwl (name,dwl) = 
  name ^ "\n" ^ string_of_wl dwl ^ "\nend_dwl"

fun worker_train_dhtnn wid dhtnn batch =
  let
    val (bpdictl,bpdatall1,bpdatall2) = 
      split_triple (map (train_dhtnn_one dhtnn) batch)
    val dwleval = ("eval", sum_dwll (map (map #dw) bpdatall1))
    val dwlpoli = ("poli", sum_dwll (map (map #dw) bpdatall2))
    val operndict = dnew (cpl_compare Term.compare Int.compare) 
      (number_snd 0 (dkeys (#opdict dhtnn)))
    val bpdict = dconcat oper_compare bpdictl 
    fun f (oper,dwll) = 
      (its (dfind oper operndict), sum_dwll dwll)
    val l = map f (dlist bpdict)
  in
    writel (widdwl_file wid) 
      (map string_of_namedwl (dwleval :: dwlpoli :: l));
    writel_atomic (widout_file wid) ["done"]
  end

fun read_namedwl dhtnn wid = 
  let 
    val noperdict = dnew Int.compare (number_fst 0 (dkeys (#opdict dhtnn))) 
    val (sleval,cont1) = split_sl "end_dwl" (Profile.profile "read_raw" 
      readl (widdwl_file wid))
    val (slpoli,cont2) = split_sl "end_dwl" cont1
    val sll = rpt_split_sl "end_dwl" cont2 
    val dwleval = read_wl_sl (tl sleval)
    val dwlpoli = read_wl_sl (tl slpoli)
    fun f opersl = 
      let 
        val oper = dfind (string_to_int (hd opersl)) noperdict  
        val dwl  = read_wl_sl (tl opersl)
      in
        (oper,dwl)
      end
  in
    (dwleval, dwlpoli, map f sll) 
  end
  

(* -------------------------------------------------------------------------
   Estimation of the computational cost of a training example
   ------------------------------------------------------------------------- *)

(*
(* todo precompute the cost *)
fun nntm_cost tm = 
  let val (oper,argl) = strip_comb tm in
    if null argl then 0 else 1 + length argl + sum_int (map nntm_cost argl) 
  end

fun cmp_snd cmp (a,b) = cmp (snd a, snd b)

fun push_ex ncore (ex as (tml,_,_),batchl) =
  let 
    val batchl1 = dict_sort (cmp_snd Int.compare) batchl
    val (exl,oldcost) = hd batchl1
    val newcost = 4 + nntm_cost (last tml) + oldcost
  in
    (ex :: exl, newcost) :: (tl batchl1)    
  end

fun distrib_exl ncore exl =
  let val batchl = List.tabulate (ncore,fn _ => ([],0)) in  
    shuffle (map fst (foldl (push_ex ncore) batchl exl))
  end

   load "aiLib"; load "rlEnv"; open aiLib; open rlEnv;
   open mlTreeNeuralNetwork;
   val dhtnn = random_dhtnn_gamespec rlGameArithGround.gamespec;
   val operl = map fst (dkeys (#opdict dhtnn));

   val size = 15;
   val nex = 128;
   val epex = List.tabulate (nex, fn _ => random_example operl 15);
   val eptrain = prepare_dhtrainset epex;

   val (batchl,t) = add_time (distrib_exl 16) eptrain;
   map (mapran batchl;
*)

(* -------------------------------------------------------------------------
   Train tnn on one batch with external parallelism
   ------------------------------------------------------------------------- *)

val operl_test = [(``$+``,2),(``SUC``,1),(``0``,0)]

fun worker_listen wid operl (traind,batchl) = 
  if exists_file (widin_file wid) 
  then case hd (readl_rm (widin_file wid)) of
      "stop" => ()
    | "batch" => 
      let 
        val dhtnn = read_dhtnn_nooper operl (dhtnn_file ())
        val batch = map (fn x => dfind x traind) (hd batchl) 
      in
        worker_train_dhtnn wid dhtnn batch;
        worker_listen wid operl (traind, tl batchl) 
      end
    | _ => raise ERR "worker_listen" ""
  else worker_listen wid operl (traind,batchl)

fun read_batchl file = 
  let fun f s = map string_to_int (String.tokens Char.isSpace s) in
    map f (readl file)
  end

fun write_batchl file batchl =
  let fun f batch = String.concatWith " " (map its batch) in
    writel file (map f batchl)
  end

fun mk_batchl (nepoch,bsize) nex = 
  let val l = List.tabulate (nex,I) in
    List.concat (List.tabulate (nepoch, fn _ => mk_batch bsize (shuffle l)))
  end

fun tnn_worker_start wid =
  let 
    val operl = read_operl (dhtnn_file ())
    val exl = read_dhex (exl_file ())
    val extrain = prepare_dhtrainset exl
    val traind = dnew Int.compare (number_fst 0 extrain)
    val batchl = read_batchl (widbatchl_file wid)
  in
    writel_atomic (widout_file wid) ["up"];
    worker_listen wid operl (traind,batchl)
  end

(* Boss *)
fun boss_stop_workers threadl =
  let 
    val ncore = length threadl 
    fun send_stop wid = writel_atomic (widin_file wid) ["stop"] 
    fun loop threadl =
      (
      OS.Process.sleep (Time.fromReal (0.001));
      if exists Thread.isActive threadl then loop threadl else ()
      )
  in
    app send_stop (List.tabulate (ncore,I));
    print_endline ("stop " ^ its ncore ^ " workers");
    loop threadl;
    print_endline ("  " ^ its ncore ^ " workers stopped")
  end

fun bts b = if b then "true" else "false"
fun flags_to_string (b1,b2) = "(" ^ bts b1 ^ "," ^  bts b2 ^ ")"

fun boss_start_worker wid =
  let
    val codel =
    [
     "open mlTreeNeuralNetwork;",
     "val _ = ml_gencode_dir := " ^ quote (!ml_gencode_dir) ^ ";",
     "val _ = tnn_worker_start " ^ its wid ^ ";"
    ]  
  in
    writel (widscript_file wid) codel; 
    smlOpen.run_buildheap false (widscript_file wid);
    remove_file (widscript_file wid)
  end

val attrib = [Thread.InterruptState Thread.InterruptAsynch, Thread.EnableBroadcastInterrupt true]

fun boss_wait_upl widl =
  let 
    fun rm_out wid = remove_file (widout_file wid) 
    fun is_up wid = hd (readl (widout_file wid)) = "up" handle Io _ => false 
  in
    if all is_up widl then app rm_out widl else boss_wait_upl widl
  end

fun update_head_dwl headnn dwl = update_nn headnn dwl

fun update_opernn_dwl opdict (oper,dwl) =
  let
    val nn    = dfind oper opdict
    val newnn = update_nn nn dwl
  in
    (oper,newnn)
  end

fun update_opdict_dwl opdict dwloperl =
  let val opernnl = map (update_opernn_dwl opdict) dwloperl in
    daddl opernnl opdict
  end

fun update_dhtnn_dwl dhtnn (dwleval,dwlpoli,dwloperl) =
  let 
    val {opdict, headeval, headpoli, dimin, dimout} = dhtnn 
    val newopdict = update_opdict_dwl opdict dwloperl
    val newheadeval = update_nn headeval dwleval
    val newheadpoli = update_nn headpoli dwlpoli
  in
    {opdict = newopdict, headeval = newheadeval, headpoli = newheadpoli,
     dimin = dimin, dimout = dimout}
  end

fun boss_read_update widl dhtnn =
  let 
    val (dwlleval,dwllpoli,dwlloperl) = 
      split_triple (Profile.profile "read" (map (read_namedwl dhtnn)) widl) 
    val operdwll_list = dlist (dregroup 
       (cpl_compare Term.compare Int.compare) (List.concat dwlloperl))
    val (dwleval,dwlpoli,dwloperl) =
      let fun f () =
        (sum_dwll dwlleval, sum_dwll dwllpoli, map_snd sum_dwll operdwll_list)
      in
        Profile.profile "sum" f ()
      end
    val dhtnn_new = Profile.profile "update"
      (update_dhtnn_dwl dhtnn) (dwleval,dwlpoli,dwloperl)
  in
    app (remove_file o widout_file) widl;
    dhtnn_new
  end


fun boss_collect_dwl widl dhtnn =
  if all (exists_file o widout_file) widl 
  then Profile.profile "read_sum_update" (boss_read_update widl) dhtnn
  else boss_collect_dwl widl dhtnn

fun boss_process_onebatch widl dhtnn =
  let fun send_batch wid = writel_atomic (widin_file wid) ["batch"] 
  in
    Profile.profile "write_dhtnn" (write_dhtnn_nooper (dhtnn_file ())) dhtnn;
    Profile.profile "write_batch"  (app send_batch) widl;
    Profile.profile "boss_collect" (boss_collect_dwl widl) dhtnn
  end

fun boss_process_nbatch widl nbatch dhtnn =
  if nbatch <= 0 then dhtnn else 
  let val dhtnn_new = boss_process_onebatch widl dhtnn in
    if nbatch mod 10 = 0 then print_endline (its nbatch) else ();
    boss_process_nbatch widl (nbatch - 1) dhtnn_new
  end

(*
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;
load "psTermGen"; open psTermGen;

val operl_test = [(``$+``,2),(``SUC``,1),(``0``,0)];
val exl1 = 
  [(random_term (map fst operl_test) (15,``:num``),[0.0],[0.0])] @
  [(random_term (map fst operl_test) (15,``:num``),[0.0],[0.0])];

val exl2 = 
  [(random_term (map fst operl_test) (15,``:num``),[0.0],[0.0])] @
  [(random_term (map fst operl_test) (15,``:num``),[0.0],[0.0])];


val dhtnnl = tnn_boss_start 2 [exl1,exl2];
*)

(* -------------------------------------------------------------------------
   Train tnn on one batch
   ------------------------------------------------------------------------- *)

fun update_head headnn bpdatall =
  let
    val dwll      = map (map #dw) bpdatall
    val dwl       = Profile.profile "sum_dwll" sum_dwll dwll
    val newheadnn = Profile.profile "udpate_nn" (update_nn headnn) dwl
    val loss      = average_loss bpdatall
  in
    (newheadnn, loss)
  end

fun update_opernn opdict (oper,dwll) =
  let
    val nn    = dfind oper opdict
    val dwl   = Profile.profile "sum_dwll" sum_dwll dwll
    val newnn = Profile.profile "udpate_nn" (update_nn nn) dwl
  in
    (oper,newnn)
  end

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
  train_tnn_epoch_aux ncore [] tnn batchl

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
      ("train: " ^ nice trainloss ^ " test: " ^ nice testloss)
  in
    train_tnn_nepoch (ncore,bsize) (n - 1) newtnn (ptrain,ptest)
  end

fun train_tnn_schedule (ncore,bsize) tnn (ptrain,ptest) schedule =
  case schedule of
    [] => tnn
  | (nepoch, lrate) :: m =>
    let
      val _ = learning_rate := lrate
      val _ = print_endline ("learning_rate: " ^ rts lrate)
      val newtnn = train_tnn_nepoch (ncore,bsize) nepoch tnn (ptrain,ptest)
    in
      train_tnn_schedule (ncore,bsize) newtnn (ptrain,ptest) m
    end

(* -------------------------------------------------------------------------
   Training a double-headed tnn
   ------------------------------------------------------------------------- *)

val parext_flag = ref false

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

fun train_dhtnn_nepoch ncore n dhtnn size eptrain =
  if n <= 0 then dhtnn else
  let
    val batchl = Profile.profile "random_batchl" (random_batchl size) eptrain
    val (newdhtnn,(loss1,loss2)) = train_dhtnn_epoch ncore dhtnn batchl
    val _ = print_endline
      ("eval_loss: " ^ pad 8 "0" (rts (approx 6 loss1)) ^ " " ^
       "poli_loss: " ^ pad 8 "0" (rts (approx 6 loss2)))
  in
    train_dhtnn_nepoch ncore (n - 1) newdhtnn size eptrain
  end

fun train_dhtnn_schedule_aux ncore dhtnn bsize eptrain schedule =
  case schedule of
    [] => dhtnn
  | (nepoch, lrate) :: m =>
    let
      val _ = learning_rate := lrate
      val _ = print_endline ("learning_rate: " ^ rts lrate)
      val newdhtnn = train_dhtnn_nepoch ncore nepoch dhtnn bsize eptrain
    in
      train_dhtnn_schedule_aux ncore newdhtnn bsize eptrain m
    end

val timer0 = ref 0.0
val timer1 = ref 0.0
fun reset_timers () = (timer0 := 0.0; timer1 := 0.0)
fun timer i = if i = 0 then timer0 else timer1
fun print_timers () = 
  print_endline (String.concatWith " " (map (rts o !) [timer0,timer1])); 

fun start_parext ncore (nepoch,bsize) dhtnn epex = 
  let
    val nex = length epex
    val _ = mkDir_err (gencode_dir ())
    fun mk_local_dir wid = mkDir_err ((gencode_dir ()) ^ "/" ^ its wid) 
    val _ = app mk_local_dir (List.tabulate (ncore,I))
    fun rm wid = (remove_file (widin_file wid); remove_file (widout_file wid))
    val _ = app rm (List.tabulate (ncore,I))
    val _ = print_endline ("start " ^ its ncore ^ " workers")
    val widl = List.tabulate (ncore,I)
    val _ = write_dhex (exl_file ()) epex
    val _ = write_operl (dhtnn_file ()) dhtnn
    val batchl = mk_batchl (nepoch,bsize) nex
    fun write_widbatchl wid = 
      let 
        fun g batch = List.nth (cut_n ncore batch, wid)
        val widbatchl = map g batchl
      in
        write_batchl (widbatchl_file wid) widbatchl
      end
    val _ = reset_timers
    val _ = app write_widbatchl widl
    fun fork wid = Thread.fork (fn () =>
      total_time (timer wid) boss_start_worker wid, attrib)
    val threadl = map fork widl
  in
    boss_wait_upl widl;
    print_endline ("  " ^ its ncore ^ " workers started");
    (fn () => boss_stop_workers threadl, length batchl)
  end

fun train_dhtnn_schedule ncore dhtnn bsize epex schedule =
  let
    val eptrain = prepare_dhtrainset epex
    val nepoch = sum_int (map fst schedule)   
    val widl = List.tabulate (ncore,I)
    val (stop_workers,nbatch) = 
      if !parext_flag 
      then start_parext ncore (nepoch,bsize) dhtnn epex
      else (fn () => (), 0)
    val dhtnn_new = 
      if !parext_flag 
      then Profile.profile "train" (boss_process_nbatch widl nbatch) dhtnn
      else Profile.profile "train"
        (train_dhtnn_schedule_aux ncore dhtnn bsize eptrain) schedule
  in
    stop_workers (); dhtnn_new
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

end (* struct *)
