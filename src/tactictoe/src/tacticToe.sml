(* ========================================================================== *)
(* FILE          : tacticToe.sml                                              *)
(* DESCRIPTION   : Automated theorem prover based on tactic selection         *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure tacticToe :> tacticToe =
struct

open HolKernel boolLib Abbrev
  tttTools tttLexer tttExec tttSetup
  tttInfix tttUnfold
  tttFeature tttPredict tttLearn
  tttTacticData tttThmData tttGoallistData
  tttMinimize tttSearch

val ERR = mk_HOL_ERR "tacticToe"

(* --------------------------------------------------------------------------
   Set parameters
   -------------------------------------------------------------------------- *)

fun set_timeout r = (ttt_search_time := Time.fromReal r)

(* --------------------------------------------------------------------------
   Initialization: import theory data
   -------------------------------------------------------------------------- *)

fun report_data () =
  let
    val s1 = int_to_string (dlength (!ttt_tacfea))
    val s2 = int_to_string (dlength (!ttt_thmfea))
    val s3 = int_to_string (dlength (!ttt_glfea))
  in
    debug (s1 ^ " tactics, " ^ s2 ^ " theorems, " ^ s3 ^ " lists of goals");
    if dlength (!ttt_glfea) = 0 
    then print_endline ("Loading " ^ s1 ^ " tactics, " ^ s2 ^ " theorems")
    else print_endline ("Loading " ^ s1 ^ " tactics, " ^ s2 ^ " theorems, " ^ 
           s3 ^ " lists of goals")
  end

fun import_ancestry () =
  let
    val thyl = ancestry (current_theory ())
    val _ = debug_t "import_tacdata" import_tacdata thyl
    val _ = debug_t "import_thmfea" import_thmfea thyl
    val _ = debug_t "import_glfea" import_glfea thyl
  in
    report_data ()
  end

(* --------------------------------------------------------------------------
   Importing databases.
   -------------------------------------------------------------------------- *)

val imported_theories = ref []

fun exists_theorydata () =
  let 
    val thyl = dict_sort String.compare (ancestry (current_theory ()))
    fun f thy = exists_file (ttt_tacfea_dir ^ "/" ^ thy)
  in
    filter f thyl
  end
  
fun init_tactictoe () =
  let
    val _ = mkDir_err ttt_code_dir
    val cthy = current_theory ()
    val _ = init_metis cthy
    val thyl = exists_theorydata ()
  in
    if !imported_theories <> thyl then
      (
      debug_t ("init_tactictoe " ^ cthy) import_ancestry ();
      hide_out QUse.use (tactictoe_dir ^ "/src/infix_file.sml");
      imported_theories := thyl
      )
    else ()
  end

(* --------------------------------------------------------------------------
   Parse non-abstracted tactic strings into tactic
   todo: remove the need for mk_tacdict
   -------------------------------------------------------------------------- *)

fun mk_tacdict stacl =
  let
    val (_,goodl) =
      partition (fn x => mem x (!ttt_tacerr) orelse is_absarg_stac x) stacl
    fun read_stac x = (x, tactic_of_sml x)
      handle _ => (debug ("Warning: bad tactic: " ^ x ^ "\n");
                   ttt_tacerr := x :: (!ttt_tacerr);
                   raise ERR "" "")
    val l = combine (goodl, tacticl_of_sml goodl)
            handle _ => mapfilter read_stac goodl 
  in
    dnew String.compare l
  end

(* --------------------------------------------------------------------------
   Preselection of theorems
   -------------------------------------------------------------------------- *)

fun select_thmfea gfea =
  if !ttt_metis_flag orelse !ttt_eprover_flag orelse !ttt_thmlarg_flag
  then
    let
      val (symweight,feav,revdict) =
        debug_t "all_thmfeav" all_thmfeav ()
      val l0 = debug_t "thmknn_wdep"
        thmknn_wdep (symweight,feav,revdict)
          (!ttt_presel_radius) gfea
      val dict = dnew String.compare feav
      fun f x = (x, snd (dfind x revdict))
        handle NotFound =>
          (debug ("dfind: " ^ x); raise ERR "dfind" x)
      val newfeav = debug_t "assoc_thmfea" (map f) l0
    in
      ((symweight,feav,revdict), newfeav)
    end
  else ((dempty Int.compare, [], dempty String.compare), [])

(* --------------------------------------------------------------------------
   Preselection of tactics
   -------------------------------------------------------------------------- *)

fun select_tacfea goalf =
  let
    val tacfea = dlist (!ttt_tacfea)
    val stacsymweight = debug_t "learn_tfidf"
      learn_tfidf tacfea
    val l0 = debug_t "stacknn"
      (stacknn stacsymweight (!ttt_presel_radius) tacfea) goalf
    val l1 = debug_t "add_stacdesc"
      add_stacdesc (!ttt_tacdep) (!ttt_presel_radius) l0
    val tacdict = debug_t "mk_tacdict"
      mk_tacdict (mk_fast_set String.compare (map #1 l1))
    fun filter_f (stac,_,_,_) = is_absarg_stac stac orelse dmem stac tacdict
    val l2 = filter filter_f l1
    fun f x = (x, dfind x (!ttt_tacfea))
    val l3 = map f l2
  in
    (stacsymweight, l3, tacdict)
  end

(* --------------------------------------------------------------------------
   Preselection of lists of goals
   -------------------------------------------------------------------------- *)

fun select_mcfeav tacfea =
  let
    fun f ((_,_,g,_),_) = (hash_goal g, ())
    val goal_dict = dnew Int.compare (map f tacfea)
    val mcfeav0 = map (fn (a,b) => (b,a)) (dlist (!ttt_glfea))
    fun filter_f ((b,n),nl) = dmem n goal_dict
    val mcfeav1 = filter filter_f mcfeav0
    val mcsymweight = debug_t "mcsymweight" learn_tfidf mcfeav0
  in
    (mcsymweight, mcfeav1)
  end

(* --------------------------------------------------------------------------
   Main function
   -------------------------------------------------------------------------- *)

fun main_tactictoe goal =
  let
    (* preselection *)
    val goalf = fea_of_goal goal
    val (stacsymweight, tacfea, tacdict) =
      debug_t "select_tacfea" select_tacfea goalf
    val ((pthmsymweight,pthmfeav,pthmrevdict), thmfeav) =
      debug_t "select_thmfea" select_thmfea goalf
    val (mcsymweight, mcfeav) =
      debug_t "select_mcfeav" select_mcfeav tacfea
    (* caches *)
    val gl_cache = ref (dempty (list_compare goal_compare))
    val thm_cache = ref (dempty (cpl_compare goal_compare Int.compare))
    val tac_cache = ref (dempty goal_compare)
    (* predictors *)
    fun tacpred g =
      dfind g (!tac_cache) handle NotFound =>
      let
        val l = fea_of_goal g
        val lbll = stacknn_uniq stacsymweight (!ttt_presel_radius) tacfea l
        val r = map #1 lbll
      in
        tac_cache := dadd g r (!tac_cache); r
      end
    fun thmpred n g =
      dfind (g,n) (!thm_cache) handle NotFound =>
      let val r = thmknn (pthmsymweight,thmfeav) n (fea_of_goal g) in
        thm_cache := dadd (g,n) r (!thm_cache); r
      end
    fun glpred gl =
      dfind gl (!gl_cache) handle NotFound =>
      let
        val nl = fea_of_goallist gl
        val r = mcknn mcsymweight (!ttt_mcev_radius) mcfeav nl
      in
        gl_cache := dadd gl r (!gl_cache); r
      end
    fun hammer pid goal =
      (!hh_stac_glob) pid (pthmsymweight,pthmfeav,pthmrevdict)
         (!ttt_eprover_time) goal
  in
    debug_t "search" (search thmpred tacpred glpred hammer tacdict) goal
  end

(* --------------------------------------------------------------------------
   Return values
   -------------------------------------------------------------------------- *)

fun status r = case r of
   ProofError     =>
   (print_endline "tactictoe: error"; FAIL_TAC "tactictoe: error")
 | ProofSaturated =>
   (print_endline "tactictoe: saturated"; FAIL_TAC "tactictoe: saturated")
 | ProofTimeOut   =>
   (print_endline "tactictoe: time out"; FAIL_TAC "tactictoe: time out")
 | Proof s        =>
   (print_endline s; hide_out tactic_of_sml s)

(* --------------------------------------------------------------------------
   Interface
   -------------------------------------------------------------------------- *)

fun tactictoe_aux goal = 
  (
  init_tactictoe ();
  status (hide_out main_tactictoe goal)
  )
  
fun ttt goal = (tactictoe_aux goal) goal

fun tactictoe term = tactictoe_aux ([],term)

(* --------------------------------------------------------------------------
   Prediction of the next tactic only
   -------------------------------------------------------------------------- *)

val next_tac_glob = ref []
val next_tac_number = ref 5
fun next n = List.nth (!next_tac_glob,n)

fun save_stac tac stac g gl =
  (
  next_tac_glob := !next_tac_glob @ [tac];
  print_endline (hide_out (minimize_stac 1.0 stac g) gl)
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
      val ro = SOME (hide_out (tttTimeout.timeOut 1.0 tac) goal)
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
    val _ = init_tactictoe ()
    val _ = next_tac_glob := []
    (* preselection *)
    val goalf = fea_of_goal goal
    val (stacsymweight,tacfea,tacdict) = hide_out select_tacfea goalf
    (* predicting *)
    fun stac_predictor g =
      stacknn stacsymweight (!ttt_presel_radius) tacfea (fea_of_goal g)
    val stacl = map #1 (stac_predictor goal)
    (* executing tactics *)
    val memdict = dempty (list_compare goal_compare)
    (* printing tactics *)
  in
    try_tac tacdict memdict (!next_tac_number) goal stacl
  end

(* --------------------------------------------------------------------------
   Evaluate Eprover
   -------------------------------------------------------------------------- *)

val eprover_eval_ref = ref 0

fun eval_eprover goal =
  let
    val _ = mkDir_err ttt_eproof_dir
    val (thmsymweight,thmfeav,revdict) = all_thmfeav ()
    val _ = incr eprover_eval_ref
    val index = !eprover_eval_ref + hash_string (current_theory ())
    fun hammer goal =
      (!hh_stac_glob) index (thmsymweight,thmfeav,revdict)
        (!ttt_eprover_time) goal
    val _ = debug_eproof ("eprover_eval " ^ int_to_string index)
    val (staco,t) = add_time hammer goal
      handle _ => (debug ("Error: hammer " ^ int_to_string index); (NONE,0.0))
  in
    debug_eproof ("Time: " ^ Real.toString t);
    case staco of
      NONE      => debug_eproof ("Proof status: Time Out")
    | SOME stac =>
      let
        val newstac = minimize_stac 1.0 stac goal []
        val tac = tactic_of_sml newstac
        val (b,t) = add_time (app_tac 2.0 tac) goal
      in
        if isSome b
          then debug_eproof ("Reconstructed: " ^ Real.toString t)
          else debug_eproof ("Reconstructed: None")
        ;
        debug_eproof ("Proof found: " ^ newstac)
      end
  end
  handle _ => debug "Error: eval_eprover"

(* --------------------------------------------------------------------------
   Evaluate TacticToe
   -------------------------------------------------------------------------- *)

fun debug_eval_status r =
  case r of
    ProofError     => debug_proof "Error: debug_eval_status"
  | ProofSaturated => debug_proof "Proof status: Saturated"
  | ProofTimeOut   => debug_proof "Proof status: Time Out"
  | Proof s        => debug_proof ("Proof found: " ^ s)

fun eval_tactictoe goal =
  (
  mkDir_err ttt_proof_dir;
  report_data ();
  init_tactictoe ();
  debug_eval_status (hide_out main_tactictoe goal)
  )


end (* struct *)
