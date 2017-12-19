(* =========================================================================  *)
(* FILE          : hhsPredictor.sml                                           *)
(* DESCRIPTION   : Tactic and theorem selections through external calls to    *)
(* machine learning programs                                                  *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsPredict :> hhsPredict =
struct

open HolKernel Abbrev hhsTools hhsSetup hhsFeature

val ERR = mk_HOL_ERR "hhsPredict"

(* -------------------------------------------------------------------------- 
   TFIDF: weight of symbols (power of 6 comes from the distance)
   -------------------------------------------------------------------------- *)

fun learn_tfidf feavl = 
  let
    val syms      = List.concat (map snd feavl)
    val dict      = count_dict (dempty Int.compare) syms
    val n         = length feavl
    fun f (fea,freq) = 
      Math.pow (Math.ln (Real.fromInt n) - Math.ln (Real.fromInt freq), 6.0)
  in
    Redblackmap.map f dict
  end

(* --------------------------------------------------------------------------
   KNN distance
   -------------------------------------------------------------------------- *)

fun inter_dict dict l = filter (fn x => dmem x dict) l
fun union_dict dict l = dkeys (daddl (map (fn x => (x,())) l) dict)

fun knn_distance symweight dict_o fea_p =
  let 
    val fea_i   = inter_dict dict_o fea_p
    fun wf n    = dfind_err "knn_distance" n symweight
    val weightl = map wf fea_i
  in
    sum_real weightl
  end

fun knn_similarity symweight dict_o fea_p =
  let 
    val fea_i    = inter_dict dict_o fea_p
    fun wf n     = dfind_err "knn_similarity" n symweight
    val weightl  = map wf fea_i
    val tot      = Real.fromInt (dlength dict_o + length fea_p)
  in
    sum_real weightl / Math.ln (Math.e + tot)
  end

(* --------------------------------------------------------------------------
   Internal predictions
   -------------------------------------------------------------------------- *)

fun compare_score ((_,x),(_,y)) = Real.compare (y,x)

(* Ordering prediction with duplicates *)
fun pre_pred dist symweight (feal: ('a * int list) list) fea_o =
  let 
    val dict_o = dnew Int.compare (map (fn x => (x,())) fea_o)
    fun f (lbl,fea) = (lbl, dist symweight dict_o fea)
    val l0 = map f feal
    val l1 = dict_sort compare_score l0
  in
    l1
  end

fun pre_knn symweight feal fea_o = 
  pre_pred knn_distance symweight feal fea_o
fun pre_sim symweight feal fea_o = 
  pre_pred knn_similarity symweight feal fea_o
   
fun stacknn symweight n feal fea_o =
  let 
    val l1 = map fst (pre_knn symweight feal fea_o)
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

fun exists_tid s = 
  let val (a,b) = split_string "Theory." s in can (DB.fetch a) b end

fun is_orthothm a = fst (dfind a (!hhs_mdict))

fun thmknn symweight n feav fea_o =
  let 
    val newfeav = 
      if !hhs_thmortho_flag 
      then filter (is_orthothm o fst) feav 
      else feav
    val l1 = map fst (pre_knn symweight newfeav fea_o)
    val l2 = mk_sameorder_set String.compare l1
  in
    first_test_n exists_tid n l2
  end    

fun all_thmfeav () =
  let
    fun f (a,(_,b)) = (a,b)
    val feav = map f (dlist (!hhs_mdict))
    val symweight = learn_tfidf feav
  in
    (symweight, feav)
  end

fun thmknn_std n goal =
  let 
    val (symweight,feav) = all_thmfeav ()
    val newfeav = 
      if !hhs_thmortho_flag 
      then filter (is_orthothm o fst) feav 
      else feav
  in
    thmknn symweight n newfeav (fea_of_goal goal)
  end

(* ----------------------------------------------------------------------
   Adding theorem dependencies in the predictions
   ---------------------------------------------------------------------- *)

fun uptodate_tid s =
  let val (a,b) = split_string "Theory." s in uptodate_thm (DB.fetch a b) end

fun depnumber_of_thm thm =
  (Dep.depnumber_of o Dep.depid_of o Tag.dep_of o Thm.tag) thm
  
fun depidl_of_thm thm =
  (Dep.depidl_of o Tag.dep_of o Thm.tag) thm   

fun thm_of_string s =
  let val (a,b) = split_string "Theory." s in DB.fetch a b end

fun has_depnumber n (_,thm) = n = depnumber_of_thm thm
fun name_of_did (thy,n) = 
  case List.find (has_depnumber n) (DB.thms thy) of
    SOME (name,_) => SOME (thy ^ "Theory." ^ name)
  | NONE => NONE
  
fun dep_of_thm s =
  List.mapPartial name_of_did (depidl_of_thm (thm_of_string s))

fun add_thmdep n l0 = 
  let 
    fun f x = x :: dep_of_thm x
    val l1 = mk_sameorder_set String.compare (List.concat (map f l0))
    fun g x = uptodate_tid x andalso 
      (not (!hhs_thmortho_flag) orelse is_orthothm x)
  in
    first_test_n g n l1
  end

fun thmknn_wdep thmsymweight n thmfeav gfea =
  let val l0 = thmknn thmsymweight n thmfeav gfea in
    add_thmdep n l0
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
   Term prediction for tactic arguments. 
   Relies on mdict_glob to calculate symweight.
   -------------------------------------------------------------------------- *)

(*
fun same_type term1 term2 =
  polymorphic (type_of term1) orelse type_of term1 = type_of term2
*)

fun is_true _ = true

fun closest_subterm ((asl,w):goal) term =
  let 
    fun togoal t = ([],t)
    fun dummy_lbl l = map (fn (_,a) => ((),a)) l
    fun f x = (togoal x, fea_of_goal (togoal x))
    val l0 = List.concat (map (rev o find_terms is_true) (w :: asl))
    val l1 = debug_t "mk_sameorder_set" (mk_sameorder_set Term.compare) l0
    val thmfeav = map (fn (a,(_,b)) => (a,b)) (dlist (!hhs_mdict))
    val feal = debug_t "features" (map f) l1
    val fea_o = hhsFeature.fea_of_goal ([],term)
    val symweight = 
      learn_tfidf (((),fea_o) :: dummy_lbl feal @ dummy_lbl thmfeav)
    val l3 = debug_t "pre_sim" pre_sim symweight feal fea_o
  in
    snd (fst (hd l3)) handle _ => raise ERR "closest_subterm" ""
  end

(* --------------------------------------------------------------------------
   Goal list evaluation for monte carlo tree search.
   -------------------------------------------------------------------------- *)

fun mcknn symweight radius feal fea =
  let
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
