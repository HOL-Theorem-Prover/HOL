(* ========================================================================  *)
(* FILE          : mlNearestNeighbor.sml                                     *)
(* DESCRIPTION   : Predictions of tactics, theorems, terms                   *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure mlNearestNeighbor :> mlNearestNeighbor =
struct

open HolKernel Abbrev aiLib mlFeature mlThmData mlTacticData

val ERR = mk_HOL_ERR "mlNearestNeighbor"

type symweight = (int, real) Redblackmap.dict  
type 'a afea = ('a * fea) list
val inter_time = ref 0.0
val dfind_time = ref 0.0
val sum_time = ref 0.0

(* ------------------------------------------------------------------------
   Distance
   ------------------------------------------------------------------------ *)

fun knn_dist symweight feao feap =
  let
    val feai = total_time inter_time inter_increasing feao feap
    fun wf n = dfind n symweight handle NotFound => raise ERR "knn_dist" ""
    val weightl = total_time dfind_time (map wf) feai
  in
    total_time sum_time sum_real weightl
  end

(* ------------------------------------------------------------------------
   Sorting feature vectors according to the distance
   ------------------------------------------------------------------------ *)

fun knn_sortu cmp n (symweight,feav) feao =
  let 
    fun g x = SOME (x, dfind x symweight) handle NotFound => NONE
    val feaosymweight = dnew Int.compare (List.mapPartial g feao)
    fun f (x,feap) = (x, knn_dist feaosymweight feao feap) 
  in
    best_n_rmaxu cmp n (map f feav)
  end

(* ------------------------------------------------------------------------
   Term predictions
   ------------------------------------------------------------------------ *)

fun termknn (symweight,termfea) n fea =
  knn_sortu Term.compare n (symweight,termfea) fea

(* ------------------------------------------------------------------------
   Theorem predictions
   ------------------------------------------------------------------------ *)

fun thmknn (symweight,thmfea) n fea =
  knn_sortu String.compare n (symweight,thmfea) fea

(* ----------------------------------------------------------------------
   Adding theorem dependencies
   ---------------------------------------------------------------------- *)

fun add_thmdep n predl =
  let
    fun f pred = pred :: validdep_of_thmid pred
    val predl0 = List.concat (map f predl)
    val predl1 = mk_sameorder_set String.compare predl0
  in
    first_n n predl1
  end

fun thmknn_wdep (symweight,feavdict) n fea =
  add_thmdep n (thmknn (symweight,feavdict) n fea)

(* ------------------------------------------------------------------------
   Tactic predictions
   ------------------------------------------------------------------------ *)

fun tacknn (symweight,tacfea) n fea =
  knn_sortu String.compare n (symweight,tacfea) fea

fun callknn (symweight,callfea) n fea =
  knn_sortu call_compare n (symweight,callfea) fea

(* ----------------------------------------------------------------------
   Adding tactic dependencies
   --------------------------------------------------------------------- *)

fun dep_call_g rl loopd calldep g =
  if dmem g loopd then () else
  let 
    val newloopd = dadd g () loopd
    val calls = dfind g calldep handle _ => [] 
    val _ = rl := calls @ (!rl)
    val newgl = mk_fast_set goal_compare (List.concat (map #ogl calls))
  in
    app (dep_call_g rl newloopd calldep) newgl
  end

fun dep_call calldep call =
  let 
    val rl = ref []
    val gl = #ogl call
    val loopd = dempty goal_compare
  in
    app (dep_call_g rl loopd calldep) gl;
    (rev (!rl))
  end

fun add_calldep calldep n calls =
  let
    val l1 = List.concat (map (fn x => x :: dep_call calldep x) calls)
    val l2 = mk_sameorder_set call_compare l1
  in
    first_n n l2
  end

(* ----------------------------------------------------------------------
   Training from a dataset of term-value pairs for comparison with
   tree neural networks.
   --------------------------------------------------------------------- *)

type 'a knnpred = (symweight * term afea) * (term, 'a) Redblackmap.dict

fun train_knn trainset =
  let
    val termfea = map_assoc (fea_of_term true) (map fst trainset);
    val symweight = learn_tfidf termfea;
  in
    ((symweight,termfea), dnew Term.compare trainset)
  end

fun infer_knn ((symweight,termfea),d) tm =
  let val neartm = hd (termknn (symweight,termfea) 1 (fea_of_term true tm)) in
    dfind neartm d
  end

fun is_accurate_knn knnpred (tm,rlo) =
  let
    val rl1 = infer_knn knnpred tm
    val rl2 = combine (rl1, rlo)
    fun test (x,y) = Real.abs (x - y) < 0.5
  in
    if all test rl2 then true else false
  end

fun knn_accuracy knnpred exset =
  let val correct = filter I (map (is_accurate_knn knnpred) exset) in
    Real.fromInt (length correct) / Real.fromInt (length exset)
  end


end (* struct *)
