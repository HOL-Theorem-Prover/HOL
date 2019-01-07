(* ========================================================================= *)
(* FILE          : rlTrain.sml                                               *)
(* DESCRIPTION   : Extract examples form proofs                              *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure rlTrain :> rlTrain =
struct

open HolKernel Abbrev boolLib aiLib psMCTS
  rlLib rlRules mlTreeNeuralNetwork

val ERR = mk_HOL_ERR "rlTrain"

(* -------------------------------------------------------------------------
   Training examples
   ------------------------------------------------------------------------- *)

type allex = {
  tacevalex : (term * real) list,
  tacpoliex : (term * real list) list,
  stopevalex : (term * real) list,
  stoppoliex : (term * real list) list,
  lrevalex : (term * real) list,
  lrpoliex : (term * real list) list,
  imitevalex : (term * real) list,
  imitpoliex : (term * real list) list,
  conjunctevalex : (term * real) list,
  conjunctpoliex : (term * real list) list
  }

val empty_allex = {
  tacevalex = [], tacpoliex = [],
  stopevalex = [], stoppoliex = [],
  lrevalex = [], lrpoliex= [],
  imitevalex = [], imitpoliex = [],
  conjunctevalex = [], conjunctpoliex = []
  }

fun add_tacex
  {tacevalex,tacpoliex,stopevalex,stoppoliex,lrevalex,lrpoliex,
   imitevalex,imitpoliex,conjunctevalex,conjunctpoliex}
  (tacevale,tacpolie) =
  {
  tacevalex = tacevale :: tacevalex,
  tacpoliex = tacpolie :: tacpoliex,
  stopevalex = stopevalex,
  stoppoliex = stoppoliex,
  lrevalex = lrevalex,
  lrpoliex = lrpoliex,
  imitevalex = imitevalex,
  imitpoliex = imitpoliex,
  conjunctevalex = conjunctevalex,
  conjunctpoliex = conjunctpoliex
  }

fun add_stopex
  {tacevalex,tacpoliex,stopevalex,stoppoliex,lrevalex,lrpoliex,
   imitevalex,imitpoliex,conjunctevalex,conjunctpoliex}
  (stopevale,stoppolie) =
  {
  tacevalex = tacevalex,
  tacpoliex = tacpoliex,
  stopevalex = stopevale :: stopevalex,
  stoppoliex = stoppolie :: stoppoliex,
  lrevalex = lrevalex,
  lrpoliex = lrpoliex,
  imitevalex = imitevalex,
  imitpoliex = imitpoliex,
  conjunctevalex = conjunctevalex,
  conjunctpoliex = conjunctpoliex
  }

fun add_lrex
  {tacevalex,tacpoliex,stopevalex,stoppoliex,lrevalex,lrpoliex,
   imitevalex,imitpoliex,conjunctevalex,conjunctpoliex}
  (lrevale,lrpolie) =
  {
  tacevalex = tacevalex,
  tacpoliex = tacpoliex,
  stopevalex = stopevalex,
  stoppoliex = stoppoliex,
  lrevalex = lrevale :: lrevalex,
  lrpoliex = lrpolie :: lrpoliex,
  imitevalex = imitevalex,
  imitpoliex = imitpoliex,
  conjunctevalex = conjunctevalex,
  conjunctpoliex = conjunctpoliex
  }

fun add_imitex
  {tacevalex,tacpoliex,stopevalex,stoppoliex,lrevalex,lrpoliex,
   imitevalex,imitpoliex,conjunctevalex,conjunctpoliex}
  (imitevale,imitpolie) =
  {
  tacevalex = tacevalex,
  tacpoliex = tacpoliex,
  stopevalex = stopevalex,
  stoppoliex = stoppoliex,
  lrevalex = lrevalex,
  lrpoliex = lrpoliex,
  imitevalex = imitevale :: imitevalex,
  imitpoliex = imitpolie :: imitpoliex,
  conjunctevalex = conjunctevalex,
  conjunctpoliex = conjunctpoliex
  }

fun add_conjunctex
  {tacevalex,tacpoliex,stopevalex,stoppoliex,lrevalex,lrpoliex,
   imitevalex,imitpoliex,conjunctevalex,conjunctpoliex}
  (conjunctevale,conjunctpolie) =
  {
  tacevalex = tacevalex,
  tacpoliex = tacpoliex,
  stopevalex = stopevalex,
  stoppoliex = stoppoliex,
  lrevalex = lrevalex,
  lrpoliex = lrpoliex,
  imitevalex = imitevalex,
  imitpoliex = imitpoliex,
  conjunctevalex = conjunctevale :: conjunctevalex,
  conjunctpoliex = conjunctpolie :: conjunctpoliex
  }

fun add_simulex (tree,allex) =
  let
    val root = dfind [0] tree
    val polisc = poli_example tree [0]
    val evalsc = eval_example tree [0]
    val nntm = nntm_of_sit (#sit root)
    val polieval = ((nntm,evalsc),(nntm,polisc))
  in
    case #sit root of
      (true, TacBoard tm) => add_tacex allex polieval
    | (true, StopBoard (tm,pos)) => add_stopex allex polieval
    | (true, LrBoard (tm,pos)) => add_lrex allex polieval
    | (true, ImitBoard ((tm,pos),res)) => add_imitex allex polieval
    | (false, ConjunctBoard (tm1,tm2)) => add_conjunctex allex polieval
    | _ => raise ERR "add_simulex" ""
  end

fun discard_oldex
  {tacevalex,tacpoliex,stopevalex,stoppoliex,lrevalex,lrpoliex,
   imitevalex,imitpoliex,conjunctevalex,conjunctpoliex} limit =
  {
  tacevalex = first_n limit tacevalex,
  tacpoliex = first_n limit tacpoliex,
  stopevalex = first_n limit stopevalex,
  stoppoliex = first_n limit stoppoliex,
  lrevalex = first_n limit lrevalex,
  lrpoliex = first_n limit lrpoliex,
  imitevalex = first_n limit imitevalex,
  imitpoliex = first_n limit imitpoliex,
  conjunctevalex = first_n limit conjunctevalex,
  conjunctpoliex = first_n limit conjunctpoliex
  }

(* -------------------------------------------------------------------------
   Neural networks
   ------------------------------------------------------------------------- *)

type alltnn =
  {
  taceval : treenn,
  tacpoli : treenn,
  stopeval : treenn,
  stoppoli : treenn,
  lreval : treenn,
  lrpoli : treenn,
  imiteval : treenn,
  imitpoli : treenn,
  conjuncteval : treenn,
  conjunctpoli : treenn
  }

fun random_alltnn dim operl = {
  taceval = random_treenn (dim,1) operl,
  tacpoli = random_treenn (dim,length all_tacchoice) operl,
  stopeval = random_treenn (dim,1) operl,
  stoppoli = random_treenn (dim,length all_stopchoice) operl,
  lreval = random_treenn (dim,1) operl,
  lrpoli = random_treenn (dim,length all_lrchoice) operl,
  imiteval = random_treenn (dim,1) operl,
  imitpoli = random_treenn (dim,length all_imitchoice) operl,
  conjuncteval = random_treenn (dim,1) operl,
  conjunctpoli = random_treenn (dim,length all_conjunctchoice) operl
}

(* -------------------------------------------------------------------------
   Training
   ------------------------------------------------------------------------- *)

fun trainset_info_eval trainset =
  let
    val mean = average_real (map snd trainset)
    val dev = standard_deviation (map snd trainset)
  in
    "  length: " ^ int_to_string (length trainset) ^ "\n" ^
    "  mean: " ^ Real.toString mean ^ "\n" ^
    "  standard deviation: " ^ Real.toString dev
  end

fun trainset_info_poli trainset =
  "  length: " ^ int_to_string (length trainset)

fun train_tnn_eval dim randtnn trainset =
  if null trainset then (print_endline "empty trainset"; randtnn) else
  let
    val _        = print_endline (trainset_info_eval trainset)
    val bsize    = if length trainset < 16 then 1 else 16
    val schedule = [(50,0.1),(50,0.01)]
    val prepset  = prepare_trainset_eval trainset
    val ((tnn,loss), nn_tim) =
      add_time (train_treenn_schedule dim randtnn bsize prepset) schedule
  in
    print_endline ("  NN Time: " ^ Real.toString nn_tim);
    print_endline ("  Last loss: " ^ Real.toString loss);
    tnn
  end

fun train_tnn_poli dim randtnn trainset =
  if null trainset then (print_endline "empty trainset"; randtnn) else
  let
    val _        = print_endline (trainset_info_poli trainset)
    val bsize    = if length trainset < 16 then 1 else 16
    val schedule = [(50,0.1),(50,0.01)]
    val prepset  = prepare_trainset_poli trainset
    val ((tnn,loss), nn_tim) =
      add_time (train_treenn_schedule dim randtnn bsize prepset) schedule
  in
    print_endline ("  NN Time: " ^ Real.toString nn_tim);
    print_endline ("  Last loss: " ^ Real.toString loss);
    tnn
  end

fun singleton x = [x]

fun all_train dim operl allex =
  let val randalltnn = random_alltnn dim operl in
    {
    taceval = train_tnn_eval dim (#taceval randalltnn) (#tacevalex allex),
    tacpoli = train_tnn_poli dim (#tacpoli randalltnn) (#tacpoliex allex),
    stopeval = train_tnn_eval dim (#stopeval randalltnn) (#stopevalex allex),
    stoppoli = train_tnn_poli dim (#stoppoli randalltnn) (#stoppoliex allex),
    lreval = train_tnn_eval dim (#lreval randalltnn) (#lrevalex allex),
    lrpoli = train_tnn_poli dim (#lrpoli randalltnn) (#lrpoliex allex),
    imiteval = train_tnn_eval dim (#imiteval randalltnn) (#imitevalex allex),
    imitpoli = train_tnn_poli dim (#imitpoli randalltnn) (#imitpoliex allex),
    conjuncteval =
      train_tnn_eval dim (#conjuncteval randalltnn) (#conjunctevalex allex),
    conjunctpoli =
      train_tnn_poli dim (#conjunctpoli randalltnn) (#conjunctpoliex allex)
    }
  end


end (* struct *)





