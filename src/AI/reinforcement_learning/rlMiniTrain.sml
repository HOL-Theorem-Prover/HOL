(* ========================================================================= *)
(* FILE          : rlMiniTrain.sml                                           *)
(* DESCRIPTION   : Extract examples form proofs                              *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure rlMiniTrain :> rlMiniTrain =
struct

open HolKernel Abbrev boolLib aiLib mlTreeNeuralNetwork psMCTS
  rlLib rlMiniRules

val ERR = mk_HOL_ERR "rlMiniTrain"

(* -------------------------------------------------------------------------
   Training examples
   ------------------------------------------------------------------------- *)

fun option_singleton x = case x of SOME y => [y] | NONE => []

type allex = {
  stopevalex : (term * real) list,
  stoppoliex : (term * real list) list,
  lrevalex : (term * real) list,
  lrpoliex : (term * real list) list,
  subevalex : (term * real) list,
  subpoliex : (term * real list) list
  }

val empty_allex = {
  stopevalex = [], stoppoliex = [],
  lrevalex = [], lrpoliex= [],
  subevalex = [], subpoliex = []
  }

fun add_stopex
  ({stopevalex,stoppoliex,lrevalex,lrpoliex,subevalex,subpoliex} : allex)
  (stopevale,stoppolie) =
  {
  stopevalex = stopevale :: stopevalex,
  stoppoliex = option_singleton stoppolie @ stoppoliex,
  lrevalex = lrevalex,
  lrpoliex = lrpoliex,
  subevalex = subevalex,
  subpoliex = subpoliex
  }

fun add_lrex
  ({stopevalex,stoppoliex,lrevalex,lrpoliex,subevalex,subpoliex} : allex)
  (lrevale,lrpolie) =
  {
  stopevalex = stopevalex,
  stoppoliex = stoppoliex,
  lrevalex = lrevale :: lrevalex,
  lrpoliex = option_singleton lrpolie @ lrpoliex,
  subevalex = subevalex,
  subpoliex = subpoliex
  }

fun add_subex
  ({stopevalex,stoppoliex,lrevalex,lrpoliex,subevalex,subpoliex} : allex)
  (subevale,subpolie) =
  {
  stopevalex = stopevalex,
  stoppoliex = stoppoliex,
  lrevalex = lrevalex,
  lrpoliex = lrpoliex,
  subevalex = subevale :: subevalex,
  subpoliex = option_singleton subpolie @ subpoliex
  }

fun add_simulex (tree,allex : allex) =
  let
    val root = dfind [0] tree
    val polio = poli_example tree [0]
    val evalsc = eval_example tree [0]
    val nntm = nntm_of_sit (#sit root)
    val polieval = ((nntm,evalsc),
      case polio of
        NONE => NONE
      | SOME polisc => SOME (nntm,polisc)
      )
  in
    case #sit root of
      (true, StopBoard (tm,pos)) => add_stopex allex polieval
    | (true, LrBoard (tm,pos)) => add_lrex allex polieval
    | (true, SubBoard (tm,pos)) => add_subex allex polieval
    | _ => raise ERR "add_simulex" ""
  end

fun discard_oldex
  {stopevalex,stoppoliex,lrevalex,lrpoliex,subevalex,subpoliex} limit =
  {
  stopevalex = first_n limit stopevalex,
  stoppoliex = first_n limit stoppoliex,
  lrevalex = first_n limit lrevalex,
  lrpoliex = first_n limit lrpoliex,
  subevalex = first_n limit subevalex,
  subpoliex = first_n limit subpoliex
  }

(* -------------------------------------------------------------------------
   Neural networks: training
   ------------------------------------------------------------------------- *)

type alltnn =
  {stopeval : treenn, stoppoli : treenn,
   lreval : treenn, lrpoli : treenn,
   subeval : treenn, subpoli : treenn}

fun random_alltnn dim operl = {
  stopeval = random_treenn (dim,1) operl,
  stoppoli = random_treenn (dim,length all_stopchoice) operl,
  lreval = random_treenn (dim,1) operl,
  lrpoli = random_treenn (dim,length all_lrchoice) operl,
  subeval = random_treenn (dim,1) operl,
  subpoli = random_treenn (dim,length all_subchoice) operl
}

fun train_alltnn dim operl allex =
  let val randalltnn = random_alltnn dim operl in
    {
    stopeval = train_tnn_eval dim (#stopeval randalltnn)
      (split_traintest 2.0 (#stopevalex allex)),
    stoppoli = train_tnn_poli dim (#stoppoli randalltnn)
      (split_traintest 2.0 (#stoppoliex allex)),
    lreval = train_tnn_eval dim (#lreval randalltnn)
      (split_traintest 2.0 (#lrevalex allex)),
    lrpoli = train_tnn_poli dim (#lrpoli randalltnn)
      (split_traintest 2.0 (#lrpoliex allex)),
    subeval = train_tnn_eval dim (#subeval randalltnn)
      (split_traintest 2.0 (#subevalex allex)),
    subpoli = train_tnn_poli dim (#subpoli randalltnn)
      (split_traintest 2.0 (#subpoliex allex))
    }
  end

(* -------------------------------------------------------------------------
   Nearest neighbor: training
   ------------------------------------------------------------------------- *)

type allknn =
  {
  stopevalk : (knninfo * (term, real) Redblackmap.dict),
  stoppolik : (knninfo * (term, real list) Redblackmap.dict),
  lrevalk : (knninfo * (term, real) Redblackmap.dict),
  lrpolik : (knninfo * (term, real list) Redblackmap.dict),
  subevalk : (knninfo * (term, real) Redblackmap.dict),
  subpolik : (knninfo * (term, real list) Redblackmap.dict)
  }

fun train_allknn allex =
  {
  stopevalk = train_knn (#stopevalex allex),
  stoppolik = train_knn (#stoppoliex allex),
  lrevalk = train_knn (#lrevalex allex),
  lrpolik = train_knn (#lrpoliex allex),
  subevalk = train_knn (#subevalex allex),
  subpolik = train_knn (#subpoliex allex)
  }

end (* struct *)





