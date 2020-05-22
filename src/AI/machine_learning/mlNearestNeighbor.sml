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

(* ------------------------------------------------------------------------
   Distance
   ------------------------------------------------------------------------ *)

fun knn_dist symweight dicto feap =
  let
    val feai    = filter (fn x => dmem x dicto) feap
    fun wf n    = dfind n symweight handle NotFound => raise ERR "knn_dist" ""
    val weightl = map wf feai
  in
    sum_real weightl
  end

(* ------------------------------------------------------------------------
   Sorting feature vectors according to the distance
   ------------------------------------------------------------------------ *)

fun knn_sort (symweight,feav) feao =
  let
    val dicto = dset Int.compare feao
    fun f (x,feap) = ((x,feap), knn_dist symweight dicto feap)
  in
    dict_sort compare_rmax (map f feav)
  end

(* ------------------------------------------------------------------------
   Term predictions
   ------------------------------------------------------------------------ *)

fun termknn (symweight,termfea) n fea =
  let
    val l1 = map (fst o fst) (knn_sort (symweight,termfea) fea)
    val l2 = mk_sameorder_set Term.compare l1
  in
    first_n n l2
  end

(* ------------------------------------------------------------------------
   Theorem predictions
   ------------------------------------------------------------------------ *)

fun thmknn (symweight,thmfea) n fea =
  let
    val l1 = map (fst o fst) (knn_sort (symweight,thmfea) fea)
    val l2 = mk_sameorder_set String.compare l1
  in
    first_n n l2
  end

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

fun tacknn (symweight,tacfea) n feao =
  let 
    val l1 = map (fst o fst) (knn_sort (symweight,tacfea) feao) 
    val l2 = mk_sameorder_set String.compare l1
  in
    first_n n l2 
  end

fun callknn (symweight,callfea) n feao =
  let 
    val l1 = map (fst o fst) (knn_sort (symweight,callfea) feao) 
    val l2 = mk_sameorder_set call_compare l1
  in
    first_n n l2
  end

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
    val termfea = map_assoc feahash_of_term (map fst trainset);
    val symweight = learn_tfidf termfea;
  in
    ((symweight,termfea), dnew Term.compare trainset)
  end

fun infer_knn ((symweight,termfea),d) tm =
  let val neartm = hd (termknn (symweight,termfea) 1 (feahash_of_term tm)) in
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
