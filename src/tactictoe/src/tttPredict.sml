(* =========================================================================  *)
(* FILE          : tttPredictor.sml                                           *)
(* DESCRIPTION   : Predictions of tactics, theorems, terms and lists of goals *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2018                                                       *)
(* ========================================================================== *)

structure tttPredict :> tttPredict =
struct

open HolKernel Abbrev tttTools tttSetup tttFeature tttExec

val ERR = mk_HOL_ERR "tttPredict"

(* --------------------------------------------------------------------------
   TFIDF: weight of symbols (power of 6 comes from the distance)
   -------------------------------------------------------------------------- *)

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

(* --------------------------------------------------------------------------
   Distance
   -------------------------------------------------------------------------- *)

fun inter_dict dict l = filter (fn x => dmem x dict) l
fun union_dict dict l = dkeys (daddl (map (fn x => (x,())) l) dict)

val random_gen = Random.newgen ()

fun knn_sim1 symweight dict_o fea_p =
  let
    val fea_i   = inter_dict dict_o fea_p
    fun wf n    = dfind_err "knn_sim1" n symweight
    val weightl = map wf fea_i
  in
    sum_real weightl
  end

(* --------------------------------------------------------------------------
   Ordering prediction with duplicates
   -------------------------------------------------------------------------- *)

fun compare_score ((_,x),(_,y)) = Real.compare (y,x)

fun pre_pred dist symweight (feal: ('a * int list) list) fea_o =
  let
    val dict_o = dnew Int.compare (map (fn x => (x,())) fea_o)
    fun f (lbl,fea) = (lbl, dist symweight dict_o fea)
    val l0 = map f feal
    val l1 = dict_sort compare_score l0
  in
    l1
  end

fun pre_sim1 symweight feal fea_o = pre_pred knn_sim1 symweight feal fea_o

(* --------------------------------------------------------------------------
   Tactic predictions
   -------------------------------------------------------------------------- *)

(* used for preselection *)
fun stacknn symweight n feal fea_o =
  let
    val l1 = map fst (pre_sim1 symweight feal fea_o)
    fun coverage x = dfind x (!ttt_taccov) handle _ => 0 
    fun compare_coverage (lbl1,lbl2) = 
      Int.compare (coverage (#1 lbl2), coverage (#1 lbl1))
    val l1' = 
      if !ttt_covdist_flag 
      then dict_sort compare_coverage l1
      else l1
    val l2 = mk_sameorder_set lbl_compare l1'
  in
    first_n n l2
  end

(* used during search *)
fun stacknn_uniq symweight n feal fea_o =
  let
    val l = stacknn symweight n feal fea_o
    fun f (lbl1,lbl2) = String.compare (#1 lbl1, #1 lbl2)
  in
    mk_sameorder_set f l
  end

(* --------------------------------------------------------------------------
   Theorem predictions
   -------------------------------------------------------------------------- *)

fun exists_tid s =
  let val (a,b) = split_string "Theory." s in
    a = namespace_tag orelse
    can (DB.fetch a) b
  end

fun thmknn (symweight,feav) n fea_o =
  let
    val l1 = map fst (pre_sim1 symweight feav fea_o)
    val l2 = mk_sameorder_set String.compare l1
  in
    first_test_n exists_tid n l2
  end

val add_fea_cache = ref (dempty goal_compare)

fun add_fea dict (name,thm) =
  let val g = dest_thm thm in
    if not (dmem g (!dict)) andalso uptodate_thm thm
    then 
      let 
        val fea = dfind g (!add_fea_cache) 
          handle NotFound => 
            let val fea' = fea_of_goal g in
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

fun all_thmfeav () =
  let
    val newdict =
      if !ttt_namespacethm_flag
      then insert_namespace (!ttt_thmfea)
      else (!ttt_thmfea)
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

(* ----------------------------------------------------------------------
   Adding theorem dependencies in the predictions
   ---------------------------------------------------------------------- *)

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

(* ----------------------------------------------------------------------
   Adding stac descendants. Should be modified to work on labels instead.
 ---------------------------------------------------------------------- *)

(* includes itself *)
fun desc_lbl_aux rlist rdict ddict (lbl as (stac,_,_,gl)) =
  (
  rlist := lbl :: (!rlist);
  if dmem lbl rdict
    then () (* debug ("Warning: descendant_of_feav: " ^ stac) *)
    else
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

fun add_stacdesc ddict n l =
   let
     val l1 = List.concat (map (desc_lbl ddict) l)
     val l2 = mk_sameorder_set lbl_compare l1
   in
     first_n n l2
   end

(* --------------------------------------------------------------------------
   Term prediction.
   Relies on mdict_glob to calculate symweight.
   Predicts everything but the term itself.
   -------------------------------------------------------------------------- *)

fun termknn n ((asl,w):goal) term =
  let
    fun not_term tm = tm <> term
    fun f x = (x, fea_of_goal ([],x))
    val l0 = List.concat (map (rev o find_terms not_term) (w :: asl))
    val l1 = mk_sameorder_set Term.compare l0
    val thmfeav = map (snd o snd) (dlist (!ttt_thmfea))
    val feal = map f l1
    val fea_o = tttFeature.fea_of_goal ([],term)
    val symweight = weight_tfidf (fea_o :: (map snd feal) @ thmfeav)
    val pre_sim = pre_sim1
    val l3 = pre_sim symweight feal fea_o
  in
    first_n n (map fst l3)
  end
  
(* --------------------------------------------------------------------------
   Term prediction for conjecturing experiments.
   -------------------------------------------------------------------------- *)

fun tmknn n (symweight,tmfea) fea_o =
  let val l = pre_sim1 symweight tmfea fea_o in
    first_n n (map fst l)
  end

(* --------------------------------------------------------------------------
   Goal list prediction.
   -------------------------------------------------------------------------- *)

fun mcknn symweight radius feal fea =
  let
    val pre_sim = pre_sim1
    val bnl = map fst (first_n radius (pre_sim symweight feal fea))
    fun ispos (b,n) = b
    fun isneg (b,n) = not b
    fun posf bnl = length (filter ispos bnl)
    fun negf bnl = length (filter isneg bnl)
    fun proba bnl =
      let
        val pos = Real.fromInt (posf bnl)
        val neg = Real.fromInt (negf bnl)
      in
        pos / (neg + pos)
      end
  in
    if null bnl then 0.0 else proba bnl
  end

end (* struct *)
