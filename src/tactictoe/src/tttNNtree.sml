(* ========================================================================== *)
(* FILE          : tttNNtree.sml                                              *)
(* DESCRIPTION   : Tree neural network                                        *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University          *)
(* DATE          : 2018                                                       *)
(* ========================================================================== *)

structure tttNNtree :> tttNNtree =
struct

open HolKernel boolLib Abbrev tttTools tttMatrix tttNN

val ERR = mk_HOL_ERR "tttNNtree"

(*----------------------------------------------------------------------------
 * Debugging
 *----------------------------------------------------------------------------*)

fun log s = () (* append_endline (tactictoe_dir ^ "/log/tttNNtree") s *)

(*---------------------------------------------------------------------------
  Initialization
  --------------------------------------------------------------------------- *)

type treenn = ((term,nn) Redblackmap.dict * nn)

fun const_nn dim activ arity =
  if arity = 0
    then random_nn activ activ [1,dim]
  else if arity = 1
    then random_nn activ activ [dim + 1, dim, dim]
  else random_nn activ activ [2 *dim + 1, dim, dim]

fun random_treenn dim cal poln =
  let val l = map (fn (c,a) =>
    (c, const_nn dim (tanh,dtanh) a)) cal
  in
    (dnew Term.compare l,
     random_nn (tanh,dtanh) (tanh,dtanh) [dim+1,dim,1+poln])
  end

(*---------------------------------------------------------------------------
  Training set
  --------------------------------------------------------------------------- *)

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

(*---------------------------------------------------------------------------
  Forward propagation
  --------------------------------------------------------------------------- *)

fun fp_treenn_aux opdict fpdict tml = case tml of
    []      => fpdict
  | tm :: m =>
    let
      val (f,argl) = strip_comb tm
      val nn = dfind f opdict
        handle NotFound => raise ERR "fp_treenn" (term_to_string tm)
      val invl = map (fn x => #outnv (last (dfind x fpdict))) argl
      val inv = Vector.concat (Vector.fromList [1.0] :: invl)
      val fpdatal = fp_nn nn inv
    in
      fp_treenn_aux opdict (dadd tm fpdatal fpdict) m
    end

fun fp_treenn (opdict,headnn) tml =
  let
    val fpdict = fp_treenn_aux opdict (dempty Term.compare) tml
    val invl = [#outnv (last (dfind (last tml) fpdict))]
    val inv = Vector.concat (Vector.fromList [1.0] :: invl)
    val fpdatal = fp_nn headnn inv
  in
    (fpdict, fpdatal)
  end

(*---------------------------------------------------------------------------
  Backward pass
  --------------------------------------------------------------------------- *)

fun dsave (k,v) d =
  let val oldl = dfind k d handle NotFound => [] in
    dadd k (v :: oldl) d
  end

fun dsavel kvl d = foldl (uncurry dsave) d kvl

fun print_length l = () (* print_endline (int_to_string (length l)) *)

fun bp_treenn_aux dim doutnvdict fpdict bpdict revtml = case revtml of
    []      => bpdict
  | tm :: m =>
    let
      val (oper,argl) = strip_comb tm
      (* val _ = print_endline (term_to_string tm) *)
      val doutnvl = dfind tm doutnvdict
      val _ = print_length doutnvl
      fun f doutnv =
        let
          val fpdatal     = dfind tm fpdict
          val bpdatal     = bp_nn_wocost fpdatal doutnv
          val operbpdatal = (oper,bpdatal)
          val dinv        = vector_to_list (#dinv (hd bpdatal))
          val dinvl       = map Vector.fromList (mk_batch dim (tl dinv))
        in
          (operbpdatal, combine (argl,dinvl))
          handle HOL_ERR _ => raise ERR "bp_treenn" ""
        end
      val rl            = map f doutnvl
      val operbpdatall  = map fst rl
      val tmdinvl       = List.concat (map snd rl)
      val _ = print_length tmdinvl
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
    val bpdict     = dempty Term.compare
  in
    (bp_treenn_aux dim doutnvdict fpdict bpdict (rev tml), bpdatal)
  end

(*---------------------------------------------------------------------------
  Training
  --------------------------------------------------------------------------- *)

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
    log ("head loss: " ^ Real.toString loss);
    (newheadnn, loss)
  end

fun merge_bpdict bpdictl =
  let
    fun f (x,l) = map (fn y => (x,y)) l
    val l0 = List.concat (map dlist bpdictl)
    val l1 = List.concat (map f l0)
  in
    dsavel l1 (dempty Term.compare)
  end

fun update_opernn bsize opdict (oper,bpdatall) =
  let
    val nn       = dfind oper opdict 
      handle NotFound => raise ERR "" (term_to_string oper)
    val dwl      = average_bpdatall bsize bpdatall
    val loss     = average_loss bpdatall
    val _        = log (term_to_string oper ^ ": " ^ Real.toString loss) 
    val newnn    = update_nn nn dwl
  in
    (oper,newnn)
  end

fun train_treenn_batch dim (treenn as (opdict,headnn)) batch =
  let
    val (bpdictl,bpdatall) =
      split (parmap 3 (train_treenn_one dim treenn) batch)
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
    (print_endline ("loss: " ^ Real.toString (average_real lossl));
     treenn)
  | batch :: m =>
    let val (newtreenn,loss) = train_treenn_batch dim treenn batch in
      train_treenn_epoch_aux dim (loss :: lossl) newtreenn m
    end

fun train_treenn_epoch dim treenn batchl =
  train_treenn_epoch_aux dim [] treenn batchl

fun train_treenn_nepoch n dim treenn size trainset =
  if n <= 0 then treenn else
  let  
    val batchl           = mk_batch size (shuffle trainset)
    val newtreenn        = train_treenn_epoch dim treenn batchl
  in
    train_treenn_nepoch (n - 1) dim newtreenn size trainset
  end

fun train_treenn_schedule dim treenn bsize prepset schedule = 
  case schedule of
    [] => treenn
  | (nepoch, lrate) :: m => 
    let 
      val _ = learning_rate := lrate 
      val _ = print_endline ("learning_rate: " ^ Real.toString lrate)
      val trainedtreenn =
        train_treenn_nepoch nepoch dim treenn bsize prepset  
    in
      train_treenn_schedule dim trainedtreenn bsize prepset m
    end

(*---------------------------------------------------------------------------
  Printing
  --------------------------------------------------------------------------- *)

fun string_of_treenn (opdict,headnn) = 
  let fun f (oper,nn) = term_to_string oper ^ "\n\n" ^ string_of_nn nn in
    String.concatWith "\n\n\n" 
      (("head\n\n" ^ string_of_nn headnn) :: map f (dlist opdict))
  end

end (* struct *)

(*---------------------------------------------------------------------------

load "tttNN";
open tttTools tttMatrix tttNN;
erase_file (tactictoe_dir ^ "/log/tttNN");

(* Peano arithmetic: axioms + tactics *)
val ax1 = ``PRE 0 = 0``;
val ax2 = ``PRE (SUC x) = x``;
val ax3 = ``(SUC x = SUC y) ==> (x = y)``;
val ax4 = ``x + 0 = x``;
val ax5 = ``x + SUC y = SUC (x + y)``;
val ax6 = ``x * 0 = 0``;
val ax7 = ``x * (SUC y) = (x * y) + x``;

(* Initial treenn *)
val cl = List.concat (map (find_terms is_const) [ax1,ax2,ax4,ax5,ax6,ax7]);
val cset = mk_fast_set Term.compare cl;
val arity = [2,2,0,2,1,1];
val cal = combine (cset,arity);
val dim = 10; 
val poln = 14;
val treenn = init_treenn dim cal poln;

(* Random training examples *)
val trainset1 = treenn_prepare_trainset rawtrainset;
val bsize = 32;

(* Training *)
learning_rate := 0.01;
val treenn1 = train_treenn_nepoch 100 dim treenn bsize trainset2;
val embedding0 = dfind ``0`` (fst treenn1);

*)



