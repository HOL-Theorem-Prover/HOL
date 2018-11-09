(* ========================================================================  *)
(* FILE          : mlNearestNeighbor.sml                                     *)
(* DESCRIPTION   : Predictions of tactics, theorems, terms                   *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure mlNearestNeighbor :> mlNearestNeighbor =
struct

open HolKernel Abbrev anotherLib mlFeature smlThm

val ERR = mk_HOL_ERR "mlNearestNeighbor"

(* ------------------------------------------------------------------------
   TFIDF: weight of symbols (power of 6 comes from the neareset neighbor 
   distance)
   ------------------------------------------------------------------------ *)

fun weight_tfidf symsl =
  let
    val syms      = List.concat symsl
    val dict      = count_dict (dempty Int.compare) syms
    val n         = length symsl
    fun f (fea,freq) =
      Math.pow (Math.ln (Real.fromInt n) - Math.ln (Real.fromInt freq), 6.0)
  in
    Redblackmap.map f dict
  end

fun learn_tfidf feavl = weight_tfidf (map snd feavl)

(* ------------------------------------------------------------------------
   Distance
   ------------------------------------------------------------------------ *)

fun knn_dist symweight dict_o fea_p =
  let
    val fea_i   = filter (fn x => dmem x dict_o) fea_p
    fun wf n    = dfind_err "knn_sim1" n symweight
    val weightl = map wf fea_i
  in
    sum_real weightl
  end

(* ------------------------------------------------------------------------
   Sorting feature vectors
   ------------------------------------------------------------------------ *)

fun knn_sort symweight feal fea_o =
  let
    val dict_o = dset Int.compare fea_o
    fun f (x,fea) = ((x,fea), knn_dist symweight dict_o fea)
  in
    dict_sort compare_rmax (map f feal)
  end

(* ------------------------------------------------------------------------
   Tactic predictions
   ------------------------------------------------------------------------ *)

fun stacknn_preselect symweight n feal fea_o =
  let val l1 = map fst (knn_sort symweight feal fea_o) in
    first_n n l1
  end

(* used during search *)
fun stacknn_uniq symweight n feal fea_o =
  let
    val l = stacknn_preselect symweight n feal fea_o
    fun f (lbl1,lbl2) = String.compare (#1 lbl1, #1 lbl2)
  in
    first_n n (mk_sameorder_set f (map fst l))
  end

(* ------------------------------------------------------------------------
   Theorem predictions
   ------------------------------------------------------------------------ *)

fun exists_tid s =
  let val (a,b) = split_string "Theory." s in
    a = namespace_tag orelse can (DB.fetch a) b
  end

fun thmknn (symweight,feav) n fea_o =
  let
    val l1 = map (fst o fst) (knn_sort symweight feav fea_o)
    val l2 = mk_sameorder_set String.compare l1
  in
    first_test_n exists_tid n l2
  end

(*
val thmfea_cache = ref (dempty goal_compare)

fun update_thmfea_cache (name,thm) =
  let val g = dest_thm thm in
    if not (dmem g (!dict)) andalso uptodate_thm thm
    then 
      let 
        val fea = dfind g (!add_fea_cache) handle NotFound => 
          let val fea' = feahash_of_goal g in
            add_fea_cache := dadd g fea' (!add_fea_cache);
            fea'
          end
      in
        dict := dadd g (name,fea) (!dict)
      end
    else ()
  end

fun insert_namespace thmdict =
  let
    val dict = ref thmdict
    fun f (x,y) = (namespace_tag ^ "Theory." ^ x, y)
    val l1 = namespace_thms ()
    val l2 = map f l1
  in
    app (add_fea dict) l2;
    (!dict)
  end

fun all_thmfeav thmfea =
  let
    val newdict = insert_namespace (!ttt_thmfea)

    val feav = map snd (dlist newdict)
    fun f (g,(name,fea)) = (name,(g,fea))
    val revdict = dnew String.compare (map f (dlist newdict))
    val symweight = learn_tfidf feav
  in
    (symweight,feav,revdict)
  end

fun thmknn_std n goal =
  let val (symweight,feav, _) = all_thmfeav () in
    thmknn (symweight,feav) n (fea_of_goal goal)
  end
*)

(* ----------------------------------------------------------------------
   Adding theorem dependencies
   ---------------------------------------------------------------------- *)

(*
fun uptodate_tid s =
  let val (a,b) = split_string "Theory." s in
    a = namespace_tag orelse uptodate_thm (DB.fetch a b)
  end

(* Uptodate-ness is probably already verified elsewhere *)
fun add_thmdep revdict n l0 =
  let
    fun f1 x = x :: deplPartial_of_sthm x
    val l1 = mk_sameorder_set String.compare (List.concat (map f1 l0))
    fun f2 x = exists_tid x andalso uptodate_tid x andalso dmem x revdict
  in
    first_test_n f2 n l1
  end

fun thmknn_wdep (symweight,feav,revdict) n gfea =
  let val l0 = thmknn (symweight,feav) n gfea in
    add_thmdep revdict n l0
  end
*)

(* ----------------------------------------------------------------------
   Adding tactic dependencies
   --------------------------------------------------------------------- *)

(*
(* includes itself *)
fun desc_lbl_aux rlist rdict ddict (lbl as (stac,_,_,gl)) =
  (
  rlist := lbl :: (!rlist);
  if dmem lbl rdict then () else
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
*)


end (* struct *)
