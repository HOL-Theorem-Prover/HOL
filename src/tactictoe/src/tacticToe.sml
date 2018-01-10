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
hhsFeature hhsMetis hhsLearn hhsMinimize hhsSetup

val ERR = mk_HOL_ERR "tacticToe"

fun set_timeout r = hhs_search_time := Time.fromReal r

fun assoc_thmfea l = 
  let fun f x = SOME (x, snd (dfind x (!hhs_mdict))) 
    handle _ => (debug ("Warning: could not find theorem " ^ x); NONE)
  in List.mapPartial f l end

fun assoc_stacfea l =
  let fun f x = (x, dfind x (!hhs_stacfea)) in map f l end

fun select_thmfeav gfea =
  if !hhs_metishammer_flag orelse !hhs_hhhammer_flag orelse !hhs_thmlarg_flag
  then
    let 
      val (thmsymweight,thmfeav) = all_thmfeav ()
      val l0 = debug_t "thmknn_wdep" 
        (thmknn_wdep thmsymweight (!hhs_maxselect_pred) thmfeav) gfea
      val l1 = debug_t "assoc_thmfea" assoc_thmfea l0
    in
      (thmsymweight, l1)
    end
  else (dempty Int.compare, [])


(* ----------------------------------------------------------------------
   Evaluating holyhammer
   ---------------------------------------------------------------------- *)

val hh_eval_ref = ref 0

fun hh_eval goal =
  let 
    val (thmsymweight,thmfeav) = all_thmfeav ()
    val _ = incr hh_eval_ref
    val index = !hh_eval_ref + hash_string (current_theory ())
    fun hammer goal =
      (!hh_stac_glob) index (thmsymweight,thmfeav) (!hhs_hhhammer_time) goal
    val _ = debug ("hh_eval " ^ int_to_string index)
    val _ = debug_proof ("hh_eval " ^ int_to_string index)
    val (staco,t) = add_time hammer goal 
      handle _ => (debug ("Error: hammer " ^ int_to_string index); (NONE,0.0))
  in
    debug_proof ("Time: " ^ Real.toString t);
    case staco of
      NONE      => debug_proof ("Proof status: Time Out")
    | SOME stac => 
      let val b = app_tac 2.0 (tactic_of_sml stac) goal in
        if isSome b then debug_proof ("Reconstructed: Yes") else ();
        debug_proof ("Proof found: " ^ stac)
      end
  end

(* ----------------------------------------------------------------------
   Parse string tactic to HOL tactic.
   ---------------------------------------------------------------------- *)

fun mk_tacdict stacl =
  let 
    (* val _ = app debug stacl *)
    val (_,goodl) = 
      partition (fn x => mem x (!hhs_badstacl) orelse is_absarg_stac x) stacl
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
   Initialize TacticToe. Reading feature vectors from disk.
   ---------------------------------------------------------------------- *)

fun import_ancestry () =
  let
    val thyl    = ancestry (current_theory ())
    val stacfea = debug_t "import_feavl" import_feavl thyl
    val _ = debug (int_to_string (length stacfea));
    val _ = debug_t "import_mdict" import_mdict ()
    val _ = debug (int_to_string (dlength (!hhs_mdict)))
    val _ = debug_t "import_mc" import_mc thyl
    val _ = debug (int_to_string (dlength (!hhs_mcdict)))
  in
    init_stacfea stacfea
  end

(* remember in which theory was the last call of tactictoe *)
val previous_theory = ref ""

fun init_tactictoe () =
  let 
    val cthy = current_theory ()
    val thyl = ancestry cthy
  in
    if !previous_theory <> cthy
    then 
      let 
        val _ = debug_t ("init_tactictoe " ^ cthy) import_ancestry ()
        val ns = int_to_string (dlength (!hhs_stacfea))
        val ms = int_to_string (dlength (!hhs_mdict))
      in  
        hide_out QUse.use (tactictoe_dir ^ "/src/infix_file.sml");
        print_endline ("Loading " ^ ns ^ " tactic feature vectors");
        print_endline ("Loading " ^ ms ^ " theorem feature vectors");
        previous_theory := cthy
      end
    else ()
  end

(* ----------------------------------------------------------------------
   Preselection of theorems and tactics
   ---------------------------------------------------------------------- *)

fun select_stacfeav goalfea =
  let 
    val stacfeav = dlist (!hhs_stacfea)
    val stacsymweight = debug_t "learn_tfidf" 
      learn_tfidf stacfeav
    val l0 = debug_t "stacknn" 
      (stacknn stacsymweight (!hhs_maxselect_pred) stacfeav) goalfea
    val l1 = debug_t "add_stacdesc" 
      add_stacdesc (!hhs_ddict) (!hhs_maxselect_pred) l0
    val tacdict = debug_t "mk_tacdict" 
      mk_tacdict (mk_fast_set String.compare (map #1 l1))
    fun filter_f (stac,_,_,_) = is_absarg_stac stac orelse dmem stac tacdict
    val l2 = filter filter_f l1
    val l3 = assoc_stacfea l2 
  in
    (stacsymweight, l3, tacdict)
  end

fun select_mcfeav stacfeav =
  if !hhs_mc_flag andalso !hhs_mcrecord_flag then
    let
      fun f ((_,_,g,_),_) = (hash_goal g, ())
      val goal_dict = dnew Int.compare (map f stacfeav)    
      val mcfeav0 = map (fn (a,b) => (b,a)) (dlist (!hhs_mcdict))
      fun filter_f ((b,n),nl) = dmem n goal_dict
      val mcfeav1 = filter filter_f mcfeav0
      val mcsymweight = debug_t "mcsymweight" learn_tfidf mcfeav0
    in
      (mcsymweight, mcfeav1)
    end
  else (dempty Int.compare, [])
  
fun main_tactictoe goal =
  let  
    (* preselection *)
    val goalfea = fea_of_goal goal       
    val (stacsymweight, stacfeav, tacdict) = select_stacfeav goalfea
    val (thmsymweight, thmfeav) = select_thmfeav goalfea
    val (mcsymweight, mcfeav) = debug_t "select_mcfeav" select_mcfeav stacfeav      
    (* fast predictors *)
    fun stacpredictor g =
      stacknn_uniq stacsymweight (!hhs_maxselect_pred) stacfeav (fea_of_goal g)
    fun thmpredictor n g = 
      thmknn thmsymweight n thmfeav (fea_of_goal g)
    fun mcpredictor gl =
      mcknn mcsymweight (!hhs_mc_radius) mcfeav (fea_of_goallist gl)
    fun hammer pid goal = 
      (!hh_stac_glob) pid (thmsymweight,thmfeav) (!hhs_hhhammer_time) goal
  in
    debug_t "Search" 
      (imperative_search
         thmpredictor stacpredictor mcpredictor hammer tacdict) goal
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
    ProofError     => debug "Error: print_eval_status"
  | ProofSaturated => debug_proof "Proof status: Saturated"
  | ProofTimeOut   => debug_proof "Proof status: Time Out"
  | Proof s        => debug_proof ("Proof found: " ^ s)

(* integer_words return errors hopefully no other *)
fun eval_tactictoe name goal =
  if
    !test_eval_hook name andalso
    !hhs_eval_flag andalso 
    one_in_n () andalso 
    not (!hhs_noprove_flag andalso String.isPrefix "tactictoe_prove_" name)
  then
    if !hh_only_flag 
    then hh_eval goal handle _ => debug "Error: hh_eval" 
    else debug_eval_status (main_tactictoe goal)
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
andalso 
    not (mem (current_theory ())
     ["word_simp","wordSem","labProps",          "data_to_word_memoryProof","word_to_stackProof"])
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
    val (stacsymweight,stacfeav,tacdict) = hide_out select_stacfeav goalfea
    (* predicting *)
    fun stac_predictor g =
      stacknn stacsymweight (!hhs_maxselect_pred) stacfeav (fea_of_goal g)
    val stacl = map #1 (stac_predictor goal)
    (* executing tactics *)
    val memdict = dempty (list_compare goal_compare)
    (* printing tactics *)
  in
    try_tac tacdict memdict (!next_tac_number) goal stacl
  end



end (* struct *)
