structure tactictoe :> tactictoe =
struct

open HolKernel boolLib
hhsLog hhsSearch hhsTools hhsLexer hhsExec hhsFeature hhsPredict hhsData

val ERR = mk_HOL_ERR "tactictoe"
  
(* ----------------------------------------------------------------------
   Global references (local to the file)
   ---------------------------------------------------------------------- *)

val timeout = ref 5.0
fun set_timeout r = timeout := r 

val max_select_pred = ref 0
val hhs_metis_npred = ref 0
val hhs_prev_thy = ref ""
val hhs_badstacl = ref []
val hhs_stacfea = ref [] 
val hhs_thmfea = ref []
val hhs_debug = ref false 
(* there is also another debug_flag named hhs_debug_flag *)

(* ----------------------------------------------------------------------
   Convert string tactics to tactics.
   ---------------------------------------------------------------------- *)

fun fast_mk_tacdict tacticl =
  let 
    val (_,goodl) = partition (fn x => mem x (!hhs_badstacl)) tacticl
    fun read_stac x = (x, valid_tactic_of_sml x)
      handle _ => (hhs_badstacl := x :: (!hhs_badstacl) ;
                   raise ERR "mk_tacdict" "")
    val l = combine (goodl, valid_tacticl_of_sml goodl)
            handle _ => mapfilter read_stac goodl
    val rdict = Redblackmap.fromList String.compare l
  in
    rdict
  end

(* ----------------------------------------------------------------------
   Initialization
   ---------------------------------------------------------------------- *)

fun init_prev () =
  let 
    val cthy = current_theory ()
    val (stacfea, thmfea) = read_data (ancestry cthy)
  in
    hhs_badstacl := [];
    hhs_stacfea := stacfea; 
    hhs_thmfea := thmfea
  end

(* ----------------------------------------------------------------------
   Parameters
   ---------------------------------------------------------------------- *)

fun set_parameters () =
  (
  (* features *)
  hhs_notopfea_flag := false;
  hhs_hofea_flag := true;
  (* predicting *)
  hhs_nolengthpen_flag := true;
  hhs_debug_flag  := false;
  max_select_pred := 500;
  (* searching *)
  hhs_noscore := true;
  hhs_cache_flag := true;
  hhs_depthpen_flag := true;
  hhs_depthpen    := 0.8;
  hhs_widthpen_flag := true;
  hhs_widthpen := 0.8;
  hhs_search_time := Time.fromReal (!timeout);
  hhs_tactic_time := 0.02;
  (* metis *)
  hhs_metis_npred := 16;
  hhs_metis_time := 0.1
  )

(* ----------------------------------------------------------------------
   Theorems dependencies
   ---------------------------------------------------------------------- *)

fun thm_of_did (thy,n) =
  let
    val thml = DB.thms thy
    fun find_number x =
      if (Dep.depnumber_of o Dep.depid_of o Tag.dep_of o Thm.tag o snd) x = n
      then x
      else raise ERR "find_number" ""
  in
    (thy ^ "." ^ fst (tryfind find_number thml)
    handle _ => raise ERR "thm_of_depid" "Not found")
  end

fun split_thm s =
  pair_of_list (String.tokens (fn x => x = #".") s)

fun rename_thm thm =
  let val (a,b) = split_thm thm in 
    "DB.fetch " ^ mlquote a ^ " " ^ mlquote b
  end

fun thm_of_string s =
  let val (a,b) = split_thm s in 
    DB.fetch a b
  end

fun hhs_dep_of thm =
  let 
    val dl = (Dep.depidl_of o Tag.dep_of o Thm.tag) thm
    val l = mapfilter thm_of_did dl
  in
    l
  end

(* ----------------------------------------------------------------------
   Main function
   ---------------------------------------------------------------------- *)

fun debug s = if !hhs_debug then print (s ^ "\n") else ()

fun main_tactictoe term =
  let
    (* global initialization *)
    val cthy = current_theory ()
    val _ = 
       if cthy <> !hhs_prev_thy
       then 
         (
         print ("<<Initialize tactictoe: " ^ cthy ^ " ...");
         init_prev ();
         print (" done>>" ^ "\n");
         hhs_prev_thy := cthy
         ) 
       else ()
    (* local initialization *)
    val _ = debug "local"
    val _ = set_parameters ()
    val (stacfea, thmfea) = (!hhs_stacfea, !hhs_thmfea)
    (* metis *)
    val _ = debug "metis"
    fun compare_first ((a1,_),(a2,_)) = String.compare (a1,a2)
    val thmfea_short =
      if !hhs_metis_flag 
      then mk_fast_set compare_first (map (fn (a,b,c) => (a,b)) thmfea)
      else []
    val (thmfea_symweight, thmfea_symweight_time) = 
      hhs_add_time learn_tfidf thmfea_short
    val thmfea_dep = 
    mapfilter (fn (a,b) => (a, b, hhs_dep_of (thm_of_string a))) thmfea_short
    (* learning *)
    val _ = debug "learning"
    val nfeav = length stacfea
    val (symweight, symweight_time) = hhs_add_time learn_tfidf stacfea
    (* selection of tactics *)
    val _ = debug "tactic selection"
    val (seltacticl, seltime) = 
      hhs_add_time (knn_ext (!max_select_pred) thmfea) (fea_of_goal ([],term))
    (* mk_tacdict *)
    val _ = debug "mk_tacdict"
    val (tacdict, tactime) = hhs_add_time fast_mk_tacdict seltacticl
    (* selection of theorems for metis *)
    val _ = debug "theorem selection"
    val (metispred, metispredtime) = 
      if !hhs_metis_flag 
      then hhs_add_time (tknn_ext (!max_select_pred) thmfea_dep) 
        (fea_of_goal ([],term))
      else ([],0.0)
    val metisdict = Redblackmap.fromList String.compare 
      (map (fn x => (x,())) metispred) 
    val metisfea0 = filter (fn (x,_,_) => dmem x metisdict) thmfea_dep
    val metisfea1 = map (fn (a,b,c) => (rename_thm a,b)) metisfea0
    (* selection of feature vectors *)
    val _ = debug "feature vector selection"
    val stacfea1 = filter (fn (x,_) => dmem x tacdict) stacfea
    val (stacfea2, knn_sort_time) = 
      let
        val feag  = fea_of_goal ([],term)
        val (l,t) = hhs_add_time (knn_sort symweight stacfea1) feag
      in
        (first_n (!max_select_pred) l, t)
      end
    (* reporting *)
    val _          =
      if !hhs_debug_flag then 
      hhs_print (
       "  tacdict time: " ^ Real.toString tactime ^ " " ^
       "  thmfea: "   ^ int_to_string (length thmfea) ^ " " ^
       "  tacdict: " ^ int_to_string (Redblackmap.numItems tacdict) ^ "\n" ^ 
       "  selection time: " ^ Real.toString seltime ^ " " ^
       "  selection: "     ^ int_to_string (length seltacticl) ^ "\n" ^
       "  metispred time: " ^ Real.toString metispredtime ^ " " ^
       "  metispred: "     ^ int_to_string (length metispred) ^ "\n" ^
       "  metisfea0: "     ^ int_to_string (length metisfea0) ^ "\n" ^
       "  thmfea_symweight time: " ^ Real.toString thmfea_symweight_time 
       ^ "\n" ^
       "  symweight time: " ^ Real.toString symweight_time ^ "\n" ^
       "  knn_sort time: " ^ Real.toString knn_sort_time ^ " " ^
       "  stacfea: "  ^ int_to_string (length stacfea) ^
       "  stacfea1: "  ^ int_to_string (length stacfea1) ^
       "  stacfea2: "  ^ int_to_string (length stacfea2) 
          )
      else ()
    (* predicting *) (* score is not normalized yet *)
    fun stac_predictor g =
      knn_score symweight (!max_select_pred) stacfea2 (fea_of_goal g)
    fun thm_predictor g =
      if !hhs_metis_flag 
      then map fst (knn_score thmfea_symweight (!hhs_metis_npred)
        metisfea1 (fea_of_goal g))
      else []
  in
    debug "Search ...";
    (* searching *)
    imperative_search thm_predictor stac_predictor 
      nfeav symweight tacdict ([],term)
  end

fun bare_tactictoe term = 
  (
  hhs_metis_flag := false;
  main_tactictoe term
  )

fun tactictoe term = 
  (
  hhs_metis_flag := 
    (true andalso exec_sml "metis_test" "metisTools.METIS_TAC []")
  ; 
  main_tactictoe term
  )

end (* struct *)
