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
hhsFeature hhsMetis hhsLearn hhsMinimize

val ERR = mk_HOL_ERR "tacticToe"

(* ----------------------------------------------------------------------
   References
   ---------------------------------------------------------------------- *)

val max_select_pred     = ref 0
val hhs_previous_theory = ref ""

val hhs_norecord_flag   = ref false
val hhs_goalstep_flag   = ref false
val hhs_internalthm_flag = ref true

(* Evaluation after recording (cheat) *)
val hhs_after_flag         = ref false
val hhs_aftersmall_flag    = ref false
val hhs_aftertac_flag      = ref false
val hhs_aftertoken_flag    = ref false
val hhs_afterthm_flag      = ref false
val hhs_afterstring_flag   = ref false
val hhs_aftertactic_flag   = ref false
val hhs_afterall_flag      = ref false
val hhs_afterall2_flag     = ref false
val hhs_afterthm2_flag     = ref false
val hhs_afterthmthm_flag   = ref false

(* set following tags to true to simulate version 2 *)
val hhs_norecprove_flag = ref true
val hhs_nolet_flag      = ref true
val hhs_noprove_flag    = ref true

val hhs_eval_flag     = ref true
val hhs_seldesc_flag  = ref true

val hh_only_flag = ref false

(* ----------------------------------------------------------------------
   Parameters
   ---------------------------------------------------------------------- *)

fun hh_eval goal =
  let val (staco,t) = add_time (!hh_stac_glob) goal in
    debug_proof ("hh_eval");
    debug_proof ("Time: " ^ Real.toString t);
    case staco of
      NONE      => debug_proof ("Proof status: Time Out")
    | SOME stac => debug_proof ("Proof found: " ^ stac)
  end

val timeout = ref 5.0
fun set_timeout r = timeout := r
val one_in_flag = ref true
val one_in_value = ref 10
val one_in_counter = ref 0
val one_in_offset = ref 0
fun one_in_n () =
  if !one_in_flag
  then 
    let val b = (!one_in_counter) mod (!one_in_value) = (!one_in_offset) in
      (incr one_in_counter; b)
    end
  else true

fun set_esearch () = 
  (
  (* evaluating *)
  one_in_flag := true;
  one_in_value := 10;
  one_in_offset := 0;
  (* predicting *)
  max_select_pred := 500;
  hhs_seldesc_flag := true;
  (* searching *)
  timeout := 5.0;
  hhs_unsafecache_flag := false;
  hhs_invalid_flag := false;
  hhs_cache_flag := true;
  hhs_diag_flag := true;
  hhs_width_coeff := 1.0;
  hhs_visited_flag := false;
  hhs_search_time := Time.fromReal (!timeout);
  hhs_tactic_time := 0.02;
  hhs_astar_flag := false;
  hhs_astar_radius := 1;
  hhs_timedepth_flag := false;
  (* synthetizing *)
  hhs_stacpred_flag := false;
  (* metis *)
  hhs_metis_flag := (true andalso can load "metisTools");
  hhs_metis_npred := 16;
  hhs_metis_time := 0.1;
  hhs_thmortho_flag := true;
  (* holyhammer *)
  hh_only_flag := 
    (
    false andalso 
    ((load "holyHammer"; update_hh_stac (); true) handle _ => false)
    );
  hh_stac_flag := 
    (
    false andalso 
    ((load "holyHammer"; update_hh_stac (); true) handle _ => false)
    );
  (* result *)
  hhs_minimize_flag := false;
  hhs_prettify_flag := false
  ) 
 
val set_isearch_hook = ref (fn () => ()) 
    
fun set_isearch () =
  (
  (* predicting *)
  max_select_pred := 500;
  hhs_seldesc_flag := true;
  (* searching *)
  hhs_invalid_flag := false;
  hhs_cache_flag := true;
  hhs_diag_flag := true;
  hhs_width_coeff := 1.0;
  hhs_visited_flag := false;
  hhs_search_time := Time.fromReal (!timeout);
  hhs_tactic_time := 0.02;
  hhs_astar_flag := false;
  hhs_astar_radius := 1;
  hhs_timedepth_flag := false;
  (* metis *)
  hhs_metis_flag := (true andalso can load "metisTools");
  hhs_metis_npred := 16;
  hhs_metis_time := 0.1;
  (* holyhammer *)
  (* result *)
  hhs_minimize_flag := true;
  hhs_prettify_flag := true;
  (* holyhammer *)
  !set_isearch_hook ();
  if !hh_stac_flag
  then (load "holyHammer"; update_hh_stac ())
  else ()
  )

(* ----------------------------------------------------------------------
   Parse string tactic to HOL tactic. Quite slow because of 
   ---------------------------------------------------------------------- *)

fun mk_tacdict tacticl =
  let 
    val (_,goodl) = partition (fn x => mem x (!hhs_badstacl)) tacticl
    fun read_stac x = (x, tactic_of_sml x)
      handle _ => (debug ("Warning: bad tactic: " ^ x ^ "\n");
                   hhs_badstacl := x :: (!hhs_badstacl);
                   raise ERR "" "")
    val l = combine (goodl, tacticl_of_sml goodl)
            handle _ => mapfilter read_stac goodl
    val rdict = dnew String.compare l
  in
    rdict
  end

(* ----------------------------------------------------------------------
   Initialization
   val succratel = 
      if !hhs_succrate_flag 
      then debug_t "import_succrate" import_succrate thyl
      else []
    val _ = succ_cthy_dict := dempty String.compare
    val _ = succ_glob_dict := dnew String.compare succratel
    val _ = debug ("  success rates: " ^ 
                   int_to_string (dlength (!succ_glob_dict)))
   
   ---------------------------------------------------------------------- *)

fun import_ancestry () =
  let
    val thyl    = ancestry (current_theory ())
    val stacfea = debug_t "import_feavl" import_feavl thyl
    val _ = debug (int_to_string (length stacfea));
    val _ = debug_t "init_mdict" init_mdict ()
    val _ = debug (int_to_string (dlength (!mdict_glob)))
  in
    hide_out QUse.use (tactictoe_dir ^ "/src/infix_file.sml");
    init_stacfea_ddict stacfea
  end

fun init_tactictoe () =
  let 
    val cthy = current_theory ()
    val thyl = ancestry cthy
  in
    if !hhs_previous_theory <> cthy
    then 
      let 
        val _ = debug_t ("init_tactictoe " ^ cthy) import_ancestry ()
        val ns = int_to_string (dlength (!hhs_stacfea))
        val ms = int_to_string (dlength (!mdict_glob))
      in  
        debug (ns ^ " tactic feature vectors");
        debug (ns ^ " theorem feature vectors");
        print_endline ("Loading " ^ ns ^ " tactic feature vectors");
        print_endline ("Loading " ^ ms ^ " theorem feature vectors");
        hhs_previous_theory := cthy
      end
    else ()
  end

(* ----------------------------------------------------------------------
   Main function
   ---------------------------------------------------------------------- *)

(* includes itself *)
fun descendant_of_feav_aux rlist rdict ddict (feav as ((stac,_,_,gl),_)) =
  (
  rlist := feav :: (!rlist);
  if dmem feav rdict
    then debug ("Warning: descendant_of_feav: " ^ stac)
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
  if !hhs_metis_flag 
  then
    let 
      val _ = debug "theorem selection"
      val _ = debug_t "update_mdict" update_mdict (current_theory ())
      val thmfeav = dlist (!mdict_glob)
      val thmsymweight = learn_tfidf thmfeav
      val thmfeavdep = 
        debug_t "dependency_of_thm"
        (mapfilter (fn (a,b) => (a,b,dependency_of_thm a))) thmfeav
      (* Some theorems might disappear so map is not enough here
         Orthogonalization and dependencies are slightly contradictory *)
      val thml = thmknn_ext (!max_select_pred) thmfeavdep goalfea
      val pdict = dnew String.compare (map (fn x => (x,())) thml) 
      val feav0 = filter (fn (x,_,_) => dmem x pdict) thmfeavdep
      val feav1 = map (fn (a,b,c) => (a,b)) feav0
    in
      (thmsymweight,feav1)
    end
  else (dempty Int.compare, [])
  
fun select_desc l =
   let
     val l1 = List.concat (map (descendant_of_feav (!hhs_ddict)) l)
     val l2 = mk_sameorder_set feav_compare l1
   in
     first_n (!max_select_pred) l2
   end

(* Minimum number of steps (or time) to solve a goal *)
fun min_option (a,bo) = case bo of
    NONE => a
  | SOME x => Real.min (a,x)

fun list_min l = case l of 
    [] => NONE
  | a :: m => SOME (min_option (a,list_min m))

fun sum_real_option l = 
  if all (fn x => Option.isSome x) l 
  then SOME (sum_real (map valOf l))
  else NONE 
  
fun minstep_aux parents g =
  let 
    val new_parents = dadd g () parents
    val somel = SOME (dfind g (!hhs_ddict)) handle _ => NONE
    fun f ((_,t,_,gl),_) = 
      if exists (fn x => dmem x new_parents) gl
      then NONE
      else sum_real_option
           (
           SOME (if !hhs_timedepth_flag then t else 1.0) ::
           (map (minstep_aux new_parents) gl)
           )
  in 
    case somel of
      NONE => NONE
    | SOME l => list_min (List.mapPartial f l)
  end  

val minstep_debug = ref (dempty goal_compare)

fun minstep g = case minstep_aux (dempty goal_compare) g of
    NONE => (
            if dmem g (!minstep_debug) 
            then (
                 minstep_debug := dadd g () (!minstep_debug);
                 debug ("Warning: min_step:" ^ string_of_goal g)
                 )
            else ()
            ; 
            NONE
            )
  | x    => x

fun create_minstep stacfeav =
  if !hhs_astar_flag then 
    let 
      val goal_set = mk_fast_set goal_compare (map (#3 o fst) stacfeav)
      val l = map (fn x => (x, minstep x)) goal_set 
    in
      dnew goal_compare l
    end
  else dempty goal_compare 

fun select_stacfeav goalfea =
  let 
    val stacfeav_org = dlist (!hhs_stacfea)
    (* computing tfidf *)
    val stacsymweight = debug_t "learn_tfidf" learn_tfidf stacfeav_org
    (* selecting neighbors *)
    val l0 = debug_t "stacknn_ext" 
      (stacknn_ext (!max_select_pred) stacfeav_org) goalfea
    (* selecting descendants *)
    val l1 = 
      if !hhs_seldesc_flag 
      then debug_t "select_desc" select_desc l0
      else l0
    (* parsing selected tactics *)
    val tacdict = debug_t "mk_tacdict" mk_tacdict (map (#1 o fst) l1)
    (* filtering readable tactics *)
    val stacfeav = filter (fn ((stac,_,_,_),_) => dmem stac tacdict) l1
    (* minstep value of a goal *)  
    val minstepdict = debug_t "create_minstep" create_minstep stacfeav   
  in
    (stacsymweight, stacfeav, tacdict, minstepdict)
  end
      
fun main_tactictoe goal =
  let  
    (* preselection *)
    val goalfea = fea_of_goal goal       
    val (stacsymweight, stacfeav, tacdict, minstepdict) = select_stacfeav goalfea
    val (thmsymweight, thmfeav) = select_thmfeav goalfea
    (* fast predictors *)
    fun stacpredictor g =
      stacknn stacsymweight (!max_select_pred) stacfeav (fea_of_goal g)
    fun thmpredictor g = 
      map fst (thmknn thmsymweight (!hhs_metis_npred) thmfeav (fea_of_goal g))
  in
    debug_t "Search" 
       (imperative_search thmpredictor stacpredictor tacdict minstepdict) 
       goal
  end

fun tactic_of_status r = case r of
   ProofError     => 
   (print_endline "tactictoe: error"; FAIL_TAC "tactictoe: error")
 | ProofSaturated => 
   (print_endline "tactictoe: saturated"; FAIL_TAC "tactictoe: saturated")
 | ProofTimeOut   => 
   (print_endline "tactictoe: time out"; FAIL_TAC "tactictoe: time out")
 | Proof s        => 
   (print_endline s; hide_out tactic_of_sml s)

fun debug_eval_status r = 
  case r of
    ProofError     => debug_proof "Error: print_eval_status"
  | ProofSaturated => debug_proof "Proof status: Saturated"
  | ProofTimeOut   => debug_proof "Proof status: Time Out"
  | Proof s        => debug_proof ("Proof found: " ^ s)

(* integer_words return errors hopefully no other *)
fun eval_tactictoe name goal =
  if !hhs_eval_flag 
    andalso not (mem (current_theory ())
              ["integer_word","word_simp","wordSem","labProps",
               "data_to_word_memoryProof","word_to_stackProof"])
    andalso one_in_n ()
    andalso 
      not (!hhs_noprove_flag andalso String.isPrefix "tactictoe_prove_" name)
  then
    let val _ = set_esearch () in
      if !hh_only_flag 
        then hh_eval goal handle _ => debug_proof "Error: print_eval_status" 
      else
        let val r = hide_out main_tactictoe goal in debug_eval_status r end
    end
  else ()

fun tactictoe goal =
  let
    val _ = init_tactictoe ()
    val _ = hide_out set_isearch ()
    val r = hide_out main_tactictoe goal
  in
    tactic_of_status r
  end

fun tt_tac goal = (tactictoe goal) goal

(*
val l1 = ["gcd","seq","poly","llist","set_relation"];
val l2 = map (fn x => x ^ "Theory") l1;
app load l2;
load "hhsTools";
open hhsTools;
val l3 = map (length o DB.thms) l1;
sum_int l3;
*)
 
(* ----------------------------------------------------------------------
   Predicting only the next tactic based on some distance measure.
   ---------------------------------------------------------------------- *)

fun string_stac stac g gl =
  let val stac0 = pretty_stac stac g gl in
    comestic_stac stac0
  end

val next_tac_glob = ref []
val next_tac_number = ref 5
fun next n = List.nth (!next_tac_glob,n)

fun save_stac tac stac g gl =
  (
  next_tac_glob := !next_tac_glob @ [tac];
  print_endline (hide_out (string_stac stac g) gl)
  )

(* TODO: timeout tactic_of_sml as it can loop *)
fun try_tac tacdict memdict n goal stacl =
   if n <= 0 then () else
   case stacl of
    [] => print_endline "no more tactics"
  | stac :: m => 
    let 
      fun p0 s = print_endline s
      fun p s = (print_endline ("  " ^ s))
      val tac = dfind stac tacdict
      val ro = SOME (hide_out (hhsTimeout.timeOut 1.0 tac) goal)
               handle _ => NONE   
    in
      case ro of 
        NONE => (print "."; try_tac tacdict memdict n goal m)
      | SOME (gl,_) =>
        let val lbl = (stac,goal,gl) in
          if dmem gl memdict
          then (print "."; try_tac tacdict memdict n goal m)
          else 
            (
            if gl = []
            then (p0 ""; save_stac tac stac goal gl; p "solved")
            else 
              (
              if mem goal gl 
                then 
                  (print "."; try_tac tacdict (dadd gl lbl memdict) n goal m)
                else (p0 "";
                      save_stac tac stac goal gl;
                      app (p o string_of_goal) gl;
                      try_tac tacdict (dadd gl lbl memdict) (n-1) goal m)
              )
            )
        end
    end
    
fun next_tac goal =    
  let  
    val _ = hide_out set_isearch ()
    val _ = init_tactictoe ()
    val _ = next_tac_glob := []
    (* preselection *)
    val goalfea = fea_of_goal goal       
    val (stacsymweight,stacfeav,tacdict,_) = hide_out select_stacfeav goalfea
    (* predicting *)
    fun stac_predictor g =
      stacknn stacsymweight (!max_select_pred) stacfeav (fea_of_goal g)
    val stacl = map (#1 o fst) (stac_predictor goal)
    (* executing tactics *)
    val memdict = dempty (list_compare goal_compare)
    (* printing tactics *)
  in
    try_tac tacdict memdict (!next_tac_number) goal stacl
  end



end (* struct *)
