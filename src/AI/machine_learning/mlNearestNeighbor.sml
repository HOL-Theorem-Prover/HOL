(* ========================================================================  *)
(* FILE          : mlNearestNeighbor.sml                                     *)
(* DESCRIPTION   : Predictions of tactics, theorems, terms                   *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure mlNearestNeighbor :> mlNearestNeighbor =
struct

open HolKernel Abbrev aiLib mlFeature mlThmData

val ERR = mk_HOL_ERR "mlNearestNeighbor"

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

fun termknn (symweight,feavdict) n fea =
  let
    val l1 = map (fst o fst) (knn_sort (symweight, dlist feavdict) fea)
    val l2 = mk_sameorder_set Term.compare l1
  in
    first_n n l2
  end

(* ------------------------------------------------------------------------
   Theorem predictions
   ------------------------------------------------------------------------ *)

fun thmknn (symweight,feavdict) n fea =
  let
    val l1 = map (fst o fst) (knn_sort (symweight, dlist feavdict) fea)
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

fun stacknn_preselect (symweight,feav) n feao =
  let val l = map fst (knn_sort (symweight,feav) feao) in
    first_n n l
  end

fun stacknn_uniq (symweight,feav) n feao =
  let val l = stacknn_preselect (symweight,feav) n feao in
    mk_sameorder_set String.compare (map (#1 o fst) l)
  end

(* ----------------------------------------------------------------------
   Adding tactic dependencies (self-including)
   --------------------------------------------------------------------- *)

fun desc_lbl_aux rlist rdict ddict (lbl as (stac,_,_,gl)) =
  (
  rlist := lbl :: (!rlist);
  if dmem lbl rdict then () else (* rdict detects loops *)
    let
      val new_rdict = dadd lbl () rdict
      fun f g =
        let val lbls = dfind g ddict handle _ => [] in
          app (desc_lbl_aux rlist new_rdict ddict) lbls
        end
    in
      app f gl
    end
  )

fun desc_lbl ddict lbl =
  let val rlist = ref [] in
    desc_lbl_aux rlist (dempty lbl_compare) ddict lbl;
    !rlist
  end

fun add_stacdep ddict n l =
  let
    val l1 = List.concat (map (desc_lbl ddict) l)
    val l2 = mk_sameorder_set lbl_compare l1
  in
    first_n n l2
  end

(* ----------------------------------------------------------------------
   Training from a dataset of pair (term,value)
   --------------------------------------------------------------------- *)

type knninfo =
  (int, real) Redblackmap.dict * (term, int list) Redblackmap.dict

fun train_knn trainset =
  let
    val trainfea = map_assoc feahash_of_term (map fst trainset);
    val trainfead = dnew Term.compare trainfea;
    val symweight = learn_tfidf trainfea;
  in
    (* rev for newest first since it might not be a set *)
    ((symweight,trainfead), dnew Term.compare (rev trainset))
  end

fun infer_knn (knninfo,trainsetd) tm =
  let val neartm = hd (termknn knninfo 1 (feahash_of_term tm)) in
    dfind neartm trainsetd (* predicting from the trainset *)
  end

fun is_accurate_knn knn i (tm,rl) =
  let
    val _ = if i mod 10 = 0 then print_endline (its i) else ()
    val rl1 = infer_knn knn tm
    val rl2 = combine (rl,rl1)
    fun test (x,y) = Real.abs (x - y) < 0.5
  in
    if all test rl2 then true else false
  end

fun knn_accuracy knn set =
  let val correct = filter I (mapi (is_accurate_knn knn) set) in
    Real.fromInt (length correct) / Real.fromInt (length set)
  end


end (* struct *)
