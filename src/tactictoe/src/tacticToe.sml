(* ========================================================================== *)
(* FILE          : tacticToe.sml                                              *)
(* DESCRIPTION   : Automated theorem prover based on tactic selection         *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure tacticToe :> tacticToe =
struct

open HolKernel boolLib Abbrev
hhsSearch hhsTools hhsLexer hhsExec hhsFeature hhsPredict hhsData hhsInfix
hhsRedirect hhsFeature hhsTacticgen hhsLearn hhsMinimize

val ERR = mk_HOL_ERR "tacticToe"

(* turn on evaluation here *)
val hhs_eval_flag = ref false

val init_error_file = tactictoe_dir ^ "/code/init_error"
val main_error_file = tactictoe_dir ^ "/code/main_error"
val hide_error_file = tactictoe_dir ^ "/code/hide_error"

(* ----------------------------------------------------------------------
   Local references
   ---------------------------------------------------------------------- *)

val timeout = ref 5.0
fun set_timeout r = timeout := r

val max_select_pred = ref 0
val hhs_metis_npred = ref 0
val hhs_previous_theory = ref ""
val mdict_glob = ref (dempty String.compare)

(* ----------------------------------------------------------------------
   Parse string tactic to HOL tactic.
   ---------------------------------------------------------------------- *)

fun mk_tacdict tacticl =
  let 
    val (_,goodl) = partition (fn x => mem x (!hhs_badstacl)) tacticl
    fun read_stac x = (x, tactic_of_sml x)
      handle _ => (print ("Bad tactic: " ^ x ^ "\n");
                   hhs_badstacl := x :: (!hhs_badstacl);
                   raise ERR "mk_tacdict" "")
    val l = combine (goodl, tacticl_of_sml goodl)
            handle _ => mapfilter read_stac goodl
    val rdict = Redblackmap.fromList String.compare l
  in
    rdict
  end

(* ----------------------------------------------------------------------
   Initialization
   ---------------------------------------------------------------------- *)

fun add_thy_mdict thy =
  let
    fun f (name,thm) =
      mdict_glob := dadd (thy ^ "Theory." ^ name) 
        (fea_of_goal (dest_thm thm)) (!mdict_glob)
  in
    app f (DB.thms thy)
  end
  
fun add_cthy_mdict () =
  let
    val cthy = current_theory ()
    fun f (name,thm) =
      mdict_glob := 
        dadd (cthy ^ "Theory." ^ name) 
               (fea_of_goal (dest_thm thm)) (!mdict_glob)
  in
    app f (DB.thms cthy)
  end

fun init_prev () =
  let
    val thyl = ancestry (current_theory ())
    val succratel = import_succrate thyl
    val _ = succ_cthy_dict := dempty String.compare
    val _ = succ_glob_dict := dnew String.compare succratel
    val (stacfea,t) = add_time import_feav thyl
    val _ = mdict_glob := dempty String.compare
    val _ = app add_thy_mdict thyl
  in
    hide init_error_file QUse.use (tactictoe_dir ^ "/src/infix_file.sml");
    debug ("Reading feature vectors: " ^ Real.toString t ^ " " ^
           int_to_string (length stacfea));
    hhs_badstacl := [];
    init_stacfea_ddict stacfea
  end

(* ----------------------------------------------------------------------
   Parameters
   ---------------------------------------------------------------------- *)

fun set_parameters () =
  (
  hhs_debug_flag := true;
  (* predicting *)
  max_select_pred := 500;
  (* searching *)
  hhs_cache_flag := true;
  set_timeout 5.0;
  hhs_search_time := Time.fromReal (!timeout);
  hhs_tactic_time := 0.02;
  hhs_astar_flag := false;
  hhs_timedepth_flag := false; 
  (* learning *)
  hhs_ortho_flag := false;
  hhs_selflearn_flag := false;
  hhs_succrate_flag := false;
  (* tactic generation *)
  hhs_mutate_flag := false;
  hhs_metis_flag := (false andalso 
                     exec_sml "metis_test" "metisTools.METIS_TAC []");
  hhs_metis_npred := 8;
  (* result *)
  hhs_minimize_flag := false
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
    (thy ^ "Theory." ^ fst (tryfind find_number thml)
    handle _ => raise ERR "thm_of_depid" "Not found")
  end

fun thm_of_string s =
  let val (a,b) = split_string "Theory." s in DB.fetch a b end

fun hhs_dep_of s =
  let 
    val thm = thm_of_string s
    val dl = (Dep.depidl_of o Tag.dep_of o Thm.tag) thm
    val l = mapfilter thm_of_did dl
  in
    l
  end

(* ----------------------------------------------------------------------
   Main function
   ---------------------------------------------------------------------- *)

fun init_tactictoe () =
  let 
    val cthy = current_theory ()
    val thyl = ancestry cthy
  in
    if !hhs_previous_theory <> cthy
    then 
     (
     debug ("Initialize tactictoe in theory " ^ cthy ^ "...\n");
     init_prev ();   
     debug ("  loading " ^ int_to_string (length (!hhs_stacfea)) ^ " " ^
            "stacfeav.\n");
     hhs_previous_theory := cthy
     ) 
    else ();
    debug "set_parameters";
    set_parameters ()
  end

(* includes itself *)
fun descendant_of_feav_aux rlist rdict ddict (feav as ((stac,_,_,gl),_)) =
  (
  rlist := feav :: (!rlist);
  if dmem feav rdict
    then debug ("warning: descendant_of_feav: " ^ stac)
    else 
      let 
        val new_rdict = dadd feav () rdict
        fun f g = 
          let val feavl = dfind g ddict handle _ => [] in  
            app (descendant_of_feav_aux rlist new_rdict ddict) feavl
          end
      in
        app f gl
      end
  )
     
fun descendant_of_feav ddict feav =
  let val rlist = ref [] in
    descendant_of_feav_aux rlist (dempty feav_compare) ddict feav;
    !rlist
  end

fun string_of_feav ((stac,_,g,gl),_) = 
  stac ^ "\n  " ^ 
  string_of_goal g ^ "\n  " ^ 
  String.concatWith "," (map string_of_goal gl)

fun select_thmfeav goalfea =
  let 
    val _ = debug "theorem selection"
    val _ = add_thy_mdict (current_theory ()) 
    val thmfeav = dlist (!mdict_glob)
    val thmsymweight = learn_tfidf thmfeav  
    val thmfeavdep = mapfilter (fn (a,b) => (a, b, hhs_dep_of a)) thmfeav
    val thml = thmknn_ext (!max_select_pred) thmfeavdep goalfea
    val pdict = dnew String.compare (map (fn x => (x,())) thml) 
    val feav0 = filter (fn (x,_,_) => dmem x pdict) thmfeavdep
    val feav1 = map (fn (a,b,c) => (a,b)) feav0
  in
    (thmsymweight,feav1)
  end
  
fun select_stacfeav goalfea =
  let 
    val _ = debug "learn_tfidf"
    val stacsymweight = learn_tfidf (!hhs_stacfea)
    (* selecting neighbors *)
    val _ = debug "stacknn_ext"
    val (l0, seltime) = 
      add_time (stacknn_ext (!max_select_pred) (!hhs_stacfea)) goalfea
    (* selecting descendants *)
    val l1 = List.concat (map (descendant_of_feav (!hhs_ddict)) l0)
    val l2 = mk_sameorder_set feav_compare l1
    val l3 = first_n (!max_select_pred) l2
    (* parsing selected tactics *)
    val _ = debug "mk_tacdict"
    val (tacdict, tactime) = add_time mk_tacdict (map (#1 o fst) l3)
    val stacfeav = filter (fn ((stac,_,_,_),_) => dmem stac tacdict) l3 
  in
    (stacsymweight, stacfeav, tacdict)
  end
      
fun main_tactictoe goal =
  let  
    (* preselection *)
    val goalfea = fea_of_goal goal       
    val (stacsymweight, stacfeav, tacdict) = select_stacfeav goalfea
    val (thmsymweight, thmfeav) = 
      if !hhs_metis_flag 
      then select_thmfeav goalfea 
      else (dempty String.compare, [])
    (* fast predictors *)
    fun stacpredictor g =
      stacknn stacsymweight (!max_select_pred) stacfeav (fea_of_goal g)
    fun thmpredictor g = 
      map fst (thmknn thmsymweight (!hhs_metis_npred) thmfeav (fea_of_goal g))
  in
    debug "Search ...";
    imperative_search thmpredictor stacpredictor tacdict (!hhs_ddict) goal
  end

fun print_proof_status r = case r of
   ProofError     => print ("Proof status: Error\n")
 | ProofSaturated => print ("Proof status: Saturated\n")
 | ProofTimeOut   => print ("Proof status: Time Out\n")
 | Proof s        => print (s ^ "\n")

fun debug_eval_status r = 
  case r of
    ProofError     => debug_proof "Error: print_eval_status\n"
  | ProofSaturated => debug_proof "Proof status: Saturated\n"
  | ProofTimeOut   => debug_proof "Proof status: Time Out\n"
  | Proof s        => debug_proof ("Proof found: " ^ s ^ "\n")


fun eval_tactictoe goal =
  if !hhs_eval_flag
  then
    let
      val _ = debug "Start evaluation"
      val _ = init_tactictoe ()
      val r = hhsRedirect.hide main_error_file main_tactictoe goal 
    in
      debug_eval_status r;
      debug "End evaluation"
    end
  else ()
 
fun tactictoe goal =
  let
    val _ = init_tactictoe ()
    val r = hhsRedirect.hide main_error_file main_tactictoe goal 
  in
    print_proof_status r
  end
 
(* ----------------------------------------------------------------------
   Predicting only the next tactic based on some distance measure.
   ---------------------------------------------------------------------- *)

fun try_tac tacdict memdict n goal stacl = case stacl of
    [] => []
  | stac :: m => 
    let 
      val tac = dfind stac tacdict
      val ro = (SOME (add_time (hhsTimeout.timeOut 0.1 tac) goal)) 
               handle _ => NONE 
      
    in
      case ro of 
        NONE => try_tac tacdict memdict n goal m
      | SOME ((gl,_),t) =>
        let 
          val lbl = (stac,t,goal,gl)
        in
          if dmem gl memdict
          then try_tac tacdict memdict n goal m
          else lbl :: (try_tac tacdict (dadd gl lbl memdict) (n-1) goal m)
        end
    end
    
fun next_tac n goal =    
  let  
    val _ = init_tactictoe ()
    (* preselection *)
    val goalfea = fea_of_goal goal       
    val (stacsymweight, stacfeav, tacdict) = select_stacfeav goalfea
    val (thmsymweight, thmfeav) = select_thmfeav goalfea
    (* predicting *)
    fun stac_predictor g =
      stacknn stacsymweight (!max_select_pred) stacfeav (fea_of_goal g)
    val stacl = map (#1 o fst) (stac_predictor goal)
    (* executing tactics *)
    val memdict = dempty (list_compare goal_compare)
    val rl = rev (try_tac tacdict memdict n goal stacl)
    (* printing tactics *)
    fun f (stac,_,g,gl) =
      let val s = hide hide_error_file (pretty_stac stac g) gl in
        print (s ^ "\n")
      end
  in
    app f rl
  end


end (* struct *)
