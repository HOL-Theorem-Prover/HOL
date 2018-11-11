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
   Initialization
   ------------------------------------------------------------------------- *)

type opdict = ((term * int),nn) Redblackmap.dict
type treenn = opdict * nn

fun const_nn dim activ arity =
  if arity = 0
  then random_nn activ activ [1,dim]
  else random_nn activ activ [arity * dim + 1, dim, dim]

fun random_opdict dim cal =
  let val l = map_assoc (fn (_,a) => const_nn dim (tanh,dtanh) a) cal in
    dnew (cpl_compare Term.compare Int.compare) l
  end

fun random_headnn dim =
  random_nn (tanh,dtanh) (tanh,dtanh) [dim+1,dim,1]

fun random_treenn dim cal = (random_opdict dim cal, random_headnn dim)

fun string_of_opdictone ((oper,a),nn) =
  term_to_string oper ^ " " ^ int_to_string a ^ "\n\n" ^ string_of_nn nn 

fun string_of_opdict opdict =
  String.concatWith "\n\n\n" (map string_of_opdictone (dlist opdict))

fun string_of_treenn (opdict,headnn) = 
  "head\n\n" ^ string_of_nn headnn ^ "\n\n\n" ^ string_of_opdict opdict

(* -------------------------------------------------------------------------
   Formatting the input
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
    topo_sort (g tm)
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
        handle NotFound => raise ERR "fp_treenn" ""
      val invl = map (fn x => #outnv (last (dfind x fpdict))) argl
      val inv = Vector.concat (Vector.fromList [1.0] :: invl)
      val fpdatal = fp_nn nn inv
    in
      fp_opdict opdict (dadd tm fpdatal fpdict) m
    end

fun fp_treenn (opdict,headnn) tml =
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

fun dsave (k,v) d =
  let val oldl = dfind k d handle NotFound => [] in
    dadd k (v :: oldl) d
  end

fun dsavel kvl d = foldl (uncurry dsave) d kvl

fun bp_treenn_aux dim doutnvdict fpdict bpdict revtml = case revtml of
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
          handle HOL_ERR _ => raise ERR "bp_treenn" ""
        end
      val rl            = map f doutnvl
      val operbpdatall  = map fst rl
      val tmdinvl       = List.concat (map snd rl)
      val newdoutnvdict = dsavel tmdinvl doutnvdict
      val newbpdict     = dsavel operbpdatall bpdict
    in
      bp_treenn_aux dim newdoutnvdict fpdict newbpdict m
    end

fun bp_treenn dim (fpdict,fpdatal) (tml,expectv) =
  let
    val outnv      = #outnv (last fpdatal)
    val doutnv     = diff_rvect expectv outnv
    val bpdatal    = bp_nn_wocost fpdatal doutnv
    val newdoutnv  =
      (Vector.fromList o tl o vector_to_list o #dinv o hd) bpdatal
    val doutnvdict = dsave (last tml,newdoutnv) (dempty Term.compare)
    val bpdict     = dempty (cpl_compare Term.compare Int.compare)
  in
    (bp_treenn_aux dim doutnvdict fpdict bpdict (rev tml), bpdatal)
  end

(* -------------------------------------------------------------------------
   Training set
   ------------------------------------------------------------------------- *)

fun prepare_trainset_poli trainset =
  let fun f (cj,poli) = (order_subtm cj, norm_vect (Vector.fromList poli)) in
    map f trainset
  end

fun prepare_trainset_eval trainset =
  prepare_trainset_poli (map_snd (fn x => [x]) trainset)

fun string_of_trainset_poli trainset =
  let 
    fun cmp (x,y) = Real.compare (hd (snd x), hd (snd y))
    val l = dict_sort cmp trainset
    fun sr x = Real.toString (approx 4 x)
    fun f (cj,poli) =
      term_to_string cj ^ ": " ^ String.concatWith " " (map sr poli)
  in
    String.concatWith "\n" (map f l)
  end

fun string_of_trainset_eval trainset =
  let 
    val l = dict_sort compare_rmin trainset
    fun sr x = Real.toString (approx 4 x)
    fun f (cj,eval) = term_to_string cj ^ ": " ^ sr eval
  in
    String.concatWith "\n" (map f l)
  end

(* -------------------------------------------------------------------------
   Inference
   ------------------------------------------------------------------------- *)

fun poli_treenn treenn tm = 
  let val (_,fpdatal) = fp_treenn treenn (order_subtm tm) in
    vector_to_list (denorm_vect (#outnv (last fpdatal)))
  end

fun eval_treenn treenn tm = hd (poli_treenn treenn tm)
  
(* -------------------------------------------------------------------------
   Training a treenn for some epochs
   ------------------------------------------------------------------------- *)

fun train_treenn_one dim treenn (tml,expectv) =
  let
    val (fpdict,fpdatal) = fp_treenn treenn tml
  in
     bp_treenn dim (fpdict,fpdatal) (tml,expectv)
  end

fun update_head bsize headnn bpdatall =
  let
    val dwl       = average_bpdatall bsize bpdatall
    val newheadnn = update_nn headnn dwl
    val loss      = average_loss bpdatall
  in
    debug ("head loss: " ^ Real.toString loss);
    (newheadnn, loss)
  end

fun merge_bpdict bpdictl =
  let
    fun f (x,l) = map (fn y => (x,y)) l
    val l0 = List.concat (map dlist bpdictl)
    val l1 = List.concat (map f l0)
  in
    dsavel l1 (dempty (cpl_compare Term.compare Int.compare))
  end

fun string_of_oper (optm,i) = term_to_string optm ^ " " ^ int_to_string i

fun update_opernn bsize opdict (oper,bpdatall) =
  let
    val nn       = dfind oper opdict 
      handle NotFound => raise ERR "update_opernn" (string_of_oper oper)
    val dwl      = average_bpdatall bsize bpdatall
    val loss     = average_loss bpdatall
    val _        = debug (string_of_oper oper ^ ": " ^ Real.toString loss) 
    val newnn    = update_nn nn dwl
  in
    (oper,newnn)
  end

fun train_treenn_batch dim (treenn as (opdict,headnn)) batch =
  let
    val (bpdictl,bpdatall) =
      split (map (train_treenn_one dim treenn) batch)
    val bsize = length batch
    val (newheadnn,loss) = update_head bsize headnn bpdatall
    val bpdict    = merge_bpdict bpdictl
    val newnnl    = map (update_opernn bsize opdict) (dlist bpdict)
    val newopdict = daddl newnnl opdict
  in
    ((newopdict,newheadnn), loss)
  end

fun train_treenn_epoch_aux dim lossl treenn batchl = case batchl of
    [] =>
    let val loss = average_real lossl in
     print_endline ("loss: " ^ Real.toString loss); (treenn, loss)
    end
  | batch :: m =>
    let val (newtreenn,loss) = train_treenn_batch dim treenn batch in
      train_treenn_epoch_aux dim (loss :: lossl) newtreenn m
    end

fun train_treenn_epoch dim treenn batchl =
  train_treenn_epoch_aux dim [] treenn batchl

fun train_treenn_nepoch n dim (treenn,loss) size trainset =
  if n <= 0 then (treenn,loss) else
  let  
    val batchl              = mk_batch size (shuffle trainset)
    val (newtreenn,newloss) = train_treenn_epoch dim treenn batchl
  in
    train_treenn_nepoch (n - 1) dim (newtreenn,newloss) size trainset
  end

fun train_treenn_schedule_aux dim (treenn,loss) bsize prepset schedule = 
  case schedule of
    [] => (treenn,loss)
  | (nepoch, lrate) :: m => 
    let 
      val _ = learning_rate := lrate 
      val _ = print_endline ("learning_rate: " ^ Real.toString lrate)
      val (newtreenn,newloss) =
        train_treenn_nepoch nepoch dim (treenn,loss) bsize prepset  
    in
      train_treenn_schedule_aux dim (newtreenn,newloss) bsize prepset m
    end

fun train_treenn_schedule dim treenn bsize prepset schedule =
  train_treenn_schedule_aux dim (treenn,0.0) bsize prepset schedule  

(* -------------------------------------------------------------------------
   Input terms for the tree neural networks
   ------------------------------------------------------------------------- *)

(* new operators *)
val seq_sym      = mk_var ("seq_sym", ``:bool -> bool -> bool``)
val asm_cat      = mk_var ("asm_cat", ``:bool -> bool -> bool``)
val goal_cat     = mk_var ("goal_cat", ``:bool -> bool -> bool``)
val forget_relation = 
  mk_var ("forget_relation", ``:bool -> bool -> bool``)
val cut_relation = 
  mk_var ("cut_relation", ``:bool -> bool -> bool``)
val cutpos_relation = 
  mk_var ("cutpos_relation", ``:bool -> bool -> bool``)
val initcut_relation = 
  mk_var ("initcut_relation", ``:bool -> bool -> bool``)
val buildcut_relation = 
  mk_var ("buildcut_relation", ``:bool -> bool -> bool``)
val goalchoice_relation = 
  mk_var ("goalchoice_relation", ``:bool -> bool -> bool``)


(* contructors for those operators *)
fun mk_seqsym (a,b) = list_mk_comb (seq_sym,[a,b])
fun mk_asmcat (a,b) = list_mk_comb (asm_cat,[a,b])
fun list_mk_asmcat (asm,asml)  = case asml of
    []     => asm
  | a :: m => mk_asmcat (asm, list_mk_asmcat (a,m))
fun strip_asml tm = case strip_comb tm of
    (a,[b,c]) => (if a <> asm_cat then [tm] else b :: strip_asml c)  
  | _         => [tm]
fun mk_goalcat (a,b) = list_mk_comb (goal_cat,[a,b])
fun list_mk_goalcat (tm,tml)  = case tml of
    []     => tm
  | a :: m => mk_goalcat (tm, list_mk_goalcat (a,m))

(* representing a goal as a nnterm *)
fun goal_to_nnterm (asm,w) = case asm of
    []     => w
  | a :: m => mk_seqsym (list_mk_asmcat (a,m),w)

fun goallist_to_nnterm gl = case map goal_to_nnterm gl of
    []     => raise ERR "goallist_to_nnterm" ""
  | a :: m => list_mk_goalcat (a,m)

(* board state/move to nnterm transformation *)
fun forget_to_nnterm (g,t) =
  list_mk_comb (forget_relation, [goal_to_nnterm g, t])

fun cut_to_nnterm (g,t) = 
  list_mk_comb (cut_relation, [goal_to_nnterm g, t])

fun cutpos_to_nnterm (g,t) = 
  list_mk_comb (cutpos_relation, [goal_to_nnterm g, t])

fun initcut_to_nnterm (g,t) =
  list_mk_comb (initcut_relation, [goal_to_nnterm g, t])

fun buildcut_to_nnterm ((g,t1),t2) =
  list_mk_comb (buildcut_relation, [cut_to_nnterm (g,t1), t2])

fun goalchoice_to_nnterm (gl,g) =
  list_mk_comb (goalchoice_relation, [goallist_to_nnterm gl, goal_to_nnterm g])

(* -------------------------------------------------------------------------
   Set of operators of a tree neural network
   ------------------------------------------------------------------------- *)

fun fo_terms tm = 
  let val (oper,argl) = strip_comb tm in 
    tm :: List.concat (map fo_terms argl)
  end  

val extra_operators = 
  [
   (seq_sym,2),
   (asm_cat,2),
   (goal_cat,2),
   (forget_relation,2),
   (cut_relation,2),
   (initcut_relation,2),
   (buildcut_relation,2),
   (cutpos_relation,2),
   (goalchoice_relation,2)
  ]

fun operl_of_term tm = 
  let 
    val tml = mk_fast_set Term.compare (fo_terms tm)
    fun f x = let val (oper,argl) = strip_comb x in (oper, length argl) end  
  in
    extra_operators @
    mk_fast_set (cpl_compare Term.compare Int.compare) (map f tml)
  end

end (* struct *)

