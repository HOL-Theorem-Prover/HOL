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

fun set_timeout r =
  set_record_hook := (fn () => ttt_search_time := Time.fromReal r)

(* ---------------------------------------------------------------------------
   Preselection of theorems
   -------------------------------------------------------------------------- *)

fun select_thmfea gfea =
  if !ttt_metishammer_flag orelse !ttt_hhhammer_flag orelse !ttt_thmlarg_flag
  then
    let
      val (symweight,feav,revdict) =
        debug_t "all_thmfeav" all_thmfeav ()
      val l0 = debug_t "thmknn_wdep"
        thmknn_wdep (symweight,feav,revdict)
          (!ttt_maxselect_pred) gfea
      val dict = dnew String.compare feav
      fun f x = (x, snd (dfind x revdict))
        handle NotFound =>
          (debug ("dfind: " ^ x); raise ERR "dfind" x)
      val newfeav = debug_t "assoc_thmfea" (map f) l0
    in
      ((symweight,feav,revdict), newfeav)
    end
  else ((dempty Int.compare, [], dempty String.compare), [])

(* ----------------------------------------------------------------------
   Evaluating holyhammer
   ---------------------------------------------------------------------- *)

val hh_eval_ref = ref 0

fun hh_eval goal =
  let
    val (thmsymweight,thmfeav,revdict) = all_thmfeav ()
    val _ = incr hh_eval_ref
    val index = !hh_eval_ref + hash_string (current_theory ())
    fun hammer goal =
      (!hh_stac_glob) index (thmsymweight,thmfeav,revdict)
        (!ttt_hhhammer_time) goal
    val _ = debug ("hh_eval " ^ int_to_string index)
    val _ = debug_proof ("hh_eval " ^ int_to_string index)
    val (staco,t) = add_time hammer goal
      handle _ => (debug ("Error: hammer " ^ int_to_string index); (NONE,0.0))
  in
    debug_proof ("Time: " ^ Real.toString t);
    case staco of
      NONE      => debug_proof ("Proof status: Time Out")
    | SOME stac =>
      let
        val newstac = minimize_stac 1.0 stac goal []
        val tac = tactic_of_sml newstac
        val (b,t) = add_time (app_tac 2.0 tac) goal
      in
        if isSome b
          then debug_proof ("Reconstructed: " ^ Real.toString t)
          else debug_proof ("Reconstructed: None")
        ;
        debug_proof ("Proof found: " ^ newstac)
      end
  end

(* ----------------------------------------------------------------------
   Parse string tactic to HOL tactic.
   ---------------------------------------------------------------------- *)

fun mk_tacdict stacl =
  let
    (* val _ = app debug stacl *)
    val (_,goodl) =
      partition (fn x => mem x (!ttt_tacerr) orelse is_absarg_stac x) stacl
    fun read_stac x = (x, tactic_of_sml x)
      handle _ => (debug ("Warning: bad tactic: " ^ x ^ "\n");
                   ttt_tacerr := x :: (!ttt_tacerr);
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

fun report_data () =
  let
    val s1 = int_to_string (dlength (!ttt_tacfea))
    val s2 = int_to_string (dlength (!ttt_thmfea))
    val s3 = int_to_string (dlength (!ttt_glfea))
  in
    debug (s1 ^ " tactics, " ^ s2 ^ " theorems, " ^ s3 ^ " lists of goals")
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

(* remember which theories were loaded in the last call of tactictoe *)
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
    val _ = hide_out set_record cthy
    val new_thyl = exists_theorydata ()
  in
    if !imported_theories <> new_thyl
    then
      let
        val _ = debug_t ("init_tactictoe " ^ cthy) import_ancestry ()
        val s1 = int_to_string (dlength (!ttt_tacfea))
        val s2 = int_to_string (dlength (!ttt_thmfea))
        val s3 = int_to_string (dlength (!ttt_glfea))
      in
        hide_out QUse.use (tactictoe_dir ^ "/src/infix_file.sml");
        print_endline ("Loading " ^ s1 ^ " tactics, " ^
                       s2 ^ " theorems, " ^ s3 ^ " lists of goals");
        imported_theories := new_thyl
      end
    else ()
  end

(* ----------------------------------------------------------------------
   Preselection of tactics
   ---------------------------------------------------------------------- *)

fun select_tacfea goalf =
  let
    val tacfea = dlist (!ttt_tacfea)
    val stacsymweight = debug_t "learn_tfidf"
      learn_tfidf tacfea
    val l0 = debug_t "stacknn"
      (stacknn stacsymweight (!ttt_maxselect_pred) tacfea) goalf
    val l1 = debug_t "add_stacdesc"
      add_stacdesc (!ttt_tacdep) (!ttt_maxselect_pred) l0
    val tacdict = debug_t "mk_tacdict"
      mk_tacdict (mk_fast_set String.compare (map #1 l1))
    fun filter_f (stac,_,_,_) = is_absarg_stac stac orelse dmem stac tacdict
    val l2 = filter filter_f l1
    fun f x = (x, dfind x (!ttt_tacfea))
    val l3 = map f l2
  in
    (stacsymweight, l3, tacdict)
  end

fun select_mcfeav tacfea =
  if !ttt_mcrecord_flag then
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
  else (dempty Int.compare, [])

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
        val lbll = stacknn_uniq stacsymweight (!ttt_maxselect_pred) tacfea l
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
        val r = mcknn mcsymweight (!ttt_mc_radius) mcfeav nl
      in
        gl_cache := dadd gl r (!gl_cache); r
      end
    fun hammer pid goal =
      (!hh_stac_glob) pid (pthmsymweight,pthmfeav,pthmrevdict)
         (!ttt_hhhammer_time) goal
  in
    debug_t "search" (search thmpred tacpred glpred hammer tacdict) goal
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

fun eval_tactictoe name goal =
  if !hh_only_flag
  then hh_eval goal handle _ => debug "Error: hh_eval"
  else
    (report_data ();
     debug_eval_status (hide_out main_tactictoe goal))

fun tactictoe_aux goal =
  let
    val _ = init_tactictoe ()
    val r = hide_out main_tactictoe goal
  in
    tactic_of_status r
  end

fun ttt goal = (tactictoe_aux goal) goal

fun tactictoe term = tactictoe_aux ([],term)

(* ----------------------------------------------------------------------
   Predicting only the next tactic based on some distance measure.
   ---------------------------------------------------------------------- *)

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
      stacknn stacsymweight (!ttt_maxselect_pred) tacfea (fea_of_goal g)
    val stacl = map #1 (stac_predictor goal)
    (* executing tactics *)
    val memdict = dempty (list_compare goal_compare)
    (* printing tactics *)
  in
    try_tac tacdict memdict (!next_tac_number) goal stacl
  end

end (* struct *)
