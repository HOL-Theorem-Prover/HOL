(* ========================================================================  *)
(* FILE          : mlNearestNeighbor.sml                                     *)
(* DESCRIPTION   : Predictions of tactics, theorems, terms                   *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure mlNearestNeighbor :> mlNearestNeighbor =
struct

open HolKernel Abbrev anotherLib mlFeature mlDataThm

val ERR = mk_HOL_ERR "mlNearestNeighbor"

(* ------------------------------------------------------------------------
   Distance
   ------------------------------------------------------------------------ *)

fun knn_dist symweight dicto fea_p =
  let
    val fea_i   = filter (fn x => dmem x dicto) fea_p
    fun wf n    = dfind n symweight handle NotFound => raise ERR "knn_dist" ""
    val weightl = map wf fea_i
  in
    sum_real weightl
  end

(* ------------------------------------------------------------------------
   Sorting feature vectors according to the distance
   ------------------------------------------------------------------------ *)

fun knn_sort symweight feal feao =
  let
    val dicto = dset Int.compare feao
    fun f (x,fea) = ((x,fea), knn_dist symweight dicto fea)
  in
    dict_sort compare_rmax (map f feal)
  end

(* ------------------------------------------------------------------------
   Theorem predictions
   ------------------------------------------------------------------------ *)

fun thmknn (symweight,feavdict) n fea =
  let
    val l1 = map (fst o fst) (knn_sort symweight (dlist feavdict) fea)
    val l2 = mk_sameorder_set String.compare l1
  in
    first_n n l2
  end

(* ----------------------------------------------------------------------
   Adding theorem dependencies
   ---------------------------------------------------------------------- *)

fun add_thmdep n predl =
  let
    val predl0 = List.concat (map validdep_of_thmid predl)
    val predl1 = mk_sameorder_set String.compare predl0
  in
    first_n n predl1
  end

fun thmknn_wdep (symweight,feavdict) n fea =
  add_thmdep n (thmknn (symweight,feavdict) n fea)


(* ------------------------------------------------------------------------
   Tactic predictions
   ------------------------------------------------------------------------ *)

fun stacknn_preselect symweight n feal feao =
  let val l1 = map fst (knn_sort symweight feal feao) in
    first_n n l1
  end

fun stacknn_uniq symweight n feal feao =
  let
    val l = stacknn_preselect symweight n feal feao
    fun f (lbl1,lbl2) = String.compare (#1 lbl1, #1 lbl2)
  in
    first_n n (mk_sameorder_set f (map fst l))
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

end (* struct *)
