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

fun knn_sim1 symweight dict_o fea_p =
  let
    val fea_i   = inter_dict dict_o fea_p
    fun wf n    = dfind_err "knn_distance" n symweight
    val weightl = map wf fea_i
  in
    sum_real weightl
  end

fun knn_sim2 symweight dict_o fea_p =
  let
    val fea_i    = inter_dict dict_o fea_p
    fun wf n     = dfind_err "knn_similarity" n symweight
    val weightl  = map wf fea_i
    val tot      = Real.fromInt (dlength dict_o + length fea_p)
  in
    sum_real weightl / Math.ln (Math.e + tot)
  end

fun knn_sim3 symweight dict_o fea_p =
  let
    val feai     = inter_dict dict_o fea_p
    val feau     = union_dict dict_o fea_p
    fun wf n     = dfind n symweight handle _ => 0.0
    val weightli = map wf feai
    val weightlu = map wf feau
  in
    sum_real weightli / (sum_real weightlu + 1.0)
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
fun pre_sim2 symweight feal fea_o = pre_pred knn_sim2 symweight feal fea_o
fun pre_sim3 symweight feal fea_o = pre_pred knn_sim3 symweight feal fea_o

(* --------------------------------------------------------------------------
   Tactic predictions
   -------------------------------------------------------------------------- *)

fun stacknn symweight n feal fea_o =
  let
    val l1 = map fst (pre_sim1 symweight feal fea_o)
    val l2 = mk_sameorder_set lbl_compare l1
  in
    first_n n l2
  end

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
    val l1 = debug_t "namespace_thms" namespace_thms ()
    val l2 = map f l1
  in
    debug_t "add_fea" (app (add_fea dict)) l2;
    debug ("adding " ^ int_to_string (dlength (!dict) - dlength thmdict) ^ 
      " theorems from the namespace");
    (!dict)
  end

fun all_thmfeav () =
  let
    val newdict =
      if !ttt_namespacethm_flag
      then debug_t "insert_namespace" insert_namespace (!ttt_thmfea)
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

(* Probably uptodate-ness is already verified elsewhere *)
fun uptodate_tid s =
  let val (a,b) = split_string "Theory." s in
    a = namespace_tag orelse uptodate_thm (DB.fetch a b)
  end

fun depnumber_of_thm thm =
  (Dep.depnumber_of o Dep.depid_of o Tag.dep_of o Thm.tag) thm
  handle HOL_ERR _ => raise ERR "depnumber_of_thm" ""

fun depidl_of_thm thm =
  (Dep.depidl_of o Tag.dep_of o Thm.tag) thm
  handle HOL_ERR _ => raise ERR "depidl_of_thm" ""

fun has_depnumber n (_,thm) = n = depnumber_of_thm thm
fun name_of_did (thy,n) =
  case List.find (has_depnumber n) (DB.thms thy) of
    SOME (name,_) => SOME (thy ^ "Theory." ^ name)
  | NONE => NONE

fun dep_of_thm s =
  let val (a,b) = split_string "Theory." s in
    if a = namespace_tag
    then []
    else List.mapPartial name_of_did (depidl_of_thm (DB.fetch a b))
  end

fun add_thmdep revdict n l0 =
  let
    fun f1 x = x :: dep_of_thm x
    val l1 = mk_sameorder_set String.compare (List.concat (map f1 l0))
    fun f2 x = exists_tid x andalso uptodate_tid x andalso dmem x revdict
  in
    debug_t "add_thmdep: first_test_n" (first_test_n f2 n) l1
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
    then debug ("Warning: descendant_of_feav: " ^ stac)
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
    fun togoal t = ([],t)
    fun f x = (x, fea_of_goal (togoal x))
    val l0 = List.concat (map (rev o find_terms not_term) (w :: asl))
    val l1 = mk_sameorder_set Term.compare l0
    val thmfeav = map (snd o snd) (dlist (!ttt_thmfea))
    val feal = map f l1
    val fea_o = tttFeature.fea_of_goal ([],term)
    val symweight = weight_tfidf (fea_o :: (map snd feal) @ thmfeav)
    val pre_sim = case !ttt_termpresim_int of
      1 => pre_sim1 | 2 => pre_sim2 | 3 => pre_sim3 | _ => pre_sim2
    val l3 = debug_t "pre_sim" pre_sim symweight feal fea_o
    val r = first_n n (map fst l3)
  in
    r
  end

(* --------------------------------------------------------------------------
   Goal list prediction.
   -------------------------------------------------------------------------- *)

fun mcknn symweight radius feal fea =
  let
    val pre_sim = case !ttt_mcpresim_int of
      1 => pre_sim1 | 2 => pre_sim2 | 3 => pre_sim3 | _ => pre_sim2
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
