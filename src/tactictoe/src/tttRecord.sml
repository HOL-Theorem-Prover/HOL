(* ========================================================================  *)
(* FILE          : tttRecord.sml                                             *)
(* DESCRIPTION   : Functions used in files written by tttUnfold              *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2017                                                      *)
(* ========================================================================= *)

structure tttRecord :> tttRecord =
struct

open HolKernel boolLib aiLib
  smlLexer smlTimeout smlExecute smlParser smlRedirect
  mlFeature mlThmData mlTacticData mlNearestNeighbor
  tttSetup tttLearn

val ERR = mk_HOL_ERR "tttRecord"

(* -------------------------------------------------------------------------
   Globals
   ------------------------------------------------------------------------- *)

val savestate_level = ref 0
val calls_glob = ref []
fun local_tag x = x
fun add_local_tag s = "( tttRecord.local_tag " ^ s ^ ")"
val tacdata_glob = ref empty_tacdata
val thmdata_glob = ref empty_thmdata
val pbl_glob = ref []
val record_tactic_time = ref 2.0
val record_proof_time = ref 20.0
val name_glob = ref ""

(* -------------------------------------------------------------------------
   Messages and profiling
   ------------------------------------------------------------------------- *)

val n_proof = ref 0
val n_proof_ignored = ref 0
val n_proof_parsed = ref 0
val n_proof_replayed = ref 0
val n_tactic_parsed = ref 0
val n_tactic_replayed = ref 0

(* profiling *)
val record_time = ref 0.0
val parse_time = ref 0.0
val replay_time = ref 0.0
val learn_time = ref 0.0
val tacfea_time = ref 0.0
val learn_tfidf_time = ref 0.0
val ttt_save_state_time = ref 0.0

fun info_thy thy =
  [
   "  " ^ its (!n_proof) ^ " proofs recognized " ^
   "(" ^ its (!n_proof_ignored) ^ " ignored",
   "    parsed: " ^ its (!n_proof_parsed) ^ " proofs " ^
   its (!n_tactic_parsed) ^ " tactics," ^
   " replayed: " ^ its (!n_proof_replayed) ^ " proofs " ^
   its (!n_tactic_replayed) ^ " tactics",
   "  Record time: " ^ rts_round 6 (!record_time) ^
   " (parse: " ^ rts_round 6 (!parse_time) ^
   ", replay: " ^ rts_round 6 (!replay_time) ^ ")",
   "  Learn time: " ^ rts_round 6 (!learn_time) ^
   " (tactic pred: " ^ rts_round 6 (!ortho_predstac_time) ^ "," ^
   " thm pred: " ^ rts_round 6 (!ortho_predthm_time) ^ "," ^
   " inter: " ^ rts_round 6 (!inter_time) ^ "," ^
   " dfind: " ^ rts_round 6 (!dfind_time) ^ "," ^
   " sum: " ^ rts_round 6 (!sum_time) ^ "," ^
   " tactic test: " ^ rts_round 6 (!ortho_teststac_time) ^ ")",
   "  Others: " ^  
   "(tactic data: " ^ rts_round 6 (!tacfea_time) ^ " " ^ 
   rts_round 6 (!learn_tfidf_time) ^ "," ^
   " thm data : " ^ rts_round 6 (!create_thmdata_time) ^ " " ^
   rts_round 6 (!add_cthy_time) ^ " " ^
   rts_round 6 (!add_namespace_time) ^ " " ^
   rts_round 6 (!thmdata_tfidf_time) ^ "," ^
   " savestate : " ^ rts_round 6 (!ttt_save_state_time) ^ ")"
  ]

fun write_info thy =
  let
    val infodir = HOLDIR ^ "/src/tactictoe/info"
    val _ = mkDir_err infodir
    val infol = info_thy thy
  in
    writel (infodir ^ "/" ^ thy) infol;
    app debug infol
  end

(* -------------------------------------------------------------------------
   Replaying a tactic
   ------------------------------------------------------------------------- *)

fun record_tactic (tac,stac) g =
  let val ((gl,v),t) = add_time (timeout (!record_tactic_time) tac) g in
    incr n_tactic_replayed;
    (if op_mem goal_eq g gl then () else
    calls_glob := 
      {
      stac = stac, ortho = stac, time = t,
      ig = g, ogl = gl, 
      loc = ((current_theory (), (!savestate_level) - 1), !name_glob),
      fea = fea_of_goal true g
      }
      :: !calls_glob);
    (gl,v)
  end
  handle Interrupt => raise Interrupt 
    |  _ => (debug ("error: recording tactic: " ^ stac); 
             raise ERR "record_tactic" stac)

(* -------------------------------------------------------------------------
   Replaying a proof
   ------------------------------------------------------------------------- *)

fun wrap_stac stac = String.concatWith " "
  ["( tttRecord.record_tactic","(",stac,",",mlquote stac,")",")"]

fun wrap_proofexp e = case e of
    ProofTactic stac => ProofTactic (wrap_stac stac)
  | ProofOther _ => e
  | ProofTactical _ => e
  | ProofInfix (s,(e1,e2)) => 
    ProofInfix (s,(wrap_proofexp e1, wrap_proofexp e2))

fun wrap_proof ostac =
  let
    val proofexp = extract_proofexp ostac
    val ntac = size_of_proofexp proofexp
    val _  = debug ("#tactics (proof): " ^ its ntac)
    val _  = n_tactic_parsed := (!n_tactic_parsed) + ntac
    val _  = debug ("#tactics (total): " ^ its (!n_tactic_parsed))
    val wstac = string_of_proofexp (wrap_proofexp proofexp)
  in
    (wstac, tactic_of_sml (!record_proof_time) wstac)
  end

fun app_wrap_proof name ostac goal =
  let
    val (wstac,wtac) = total_time parse_time wrap_proof ostac
    val _  = incr n_proof_parsed
  in
    let val (gl,v) = total_time replay_time
      (timeout (!record_proof_time) wtac) goal
    in
      if null gl
      then (incr n_proof_replayed; (gl,v))
      else (debug "open goals"; raise ERR "app_wrap_proof" "open goals")
    end
  end

(* --------------------------------------------------------------------------
   Globalizing sml values (with special case for theorems)
   --------------------------------------------------------------------------*)

fun fetch s reps =
  let val sthmo = thm_of_sml s in
    case sthmo of
      NONE =>
        (if reps = ""
         then (debug ("fetch_other: " ^ s); add_local_tag s)
         else reps)
    | SOME (_,thm) =>
    let val nameo = dbfetch_of_depid thm in
      case nameo of
        SOME x => x
      | NONE => (debug ("fetch_thm: " ^ s); add_local_tag s)
    end
  end

(* ----------------------------------------------------------------------
   Proof recording
   ---------------------------------------------------------------------- *)

fun start_record_proof name =
  (
  incr n_proof;
  calls_glob := [];
  name_glob := name;
  debug ("Name: " ^ its ((!savestate_level) - 1) ^ " " ^ name)
  )

fun end_record_proof name g =
  let
    val l1 = (rev (!calls_glob))
    val feal1 = List.concat (map #fea l1)
    val feal2 = mk_fast_set Int.compare feal1
    val (thmdata,tacdata) = (!thmdata_glob, !tacdata_glob)
    val tacfea = total_time tacfea_time 
      (map (fn x => (#ortho x,#fea x))) (#calls tacdata)
    val tacsymweight = 
      total_time learn_tfidf_time 
        (learn_tfidf_symfreq (length tacfea) feal2) (#symfreq tacdata)
    val l2 = 
      if !record_ortho_flag
      then map (orthogonalize (thmdata,tacdata,(tacsymweight,tacfea))) l1
      else l1
    val newtacdata = foldl ttt_update_tacdata tacdata l2
  in
    debug ("saving " ^ int_to_string (length l2) ^ " labels");
    tacdata_glob := newtacdata
  end

fun ttt_before_save_state () = 
  thmdata_glob := total_time create_thmdata_time create_thmdata ()

fun ttt_save_state () =
  (
  if !record_savestate_flag then
  let
    val savestate_dir = tactictoe_dir ^ "/savestate"
    val _ = mkDir_err savestate_dir
    val prefix = savestate_dir ^ "/" ^ current_theory () ^ "_" ^
      its (!savestate_level)
    val savestate_file = prefix ^ "_savestate"
    val _ = debug ("saving state to " ^ savestate_file)
  in
    if !savestate_level = 0
    then PolyML.SaveState.saveState savestate_file
    else PolyML.SaveState.saveChild (savestate_file,
                 ((!savestate_level) div 50) + 1)
  end
  else ()
  )

fun ttt_after_save_state () = incr savestate_level


fun save_goal g =
  let
    val savestate_dir = tactictoe_dir ^ "/savestate"
    val _ = mkDir_err savestate_dir
    val prefix = savestate_dir ^ "/" ^ current_theory () ^ "_" ^
      its ((!savestate_level) - 1)
    val _ = pbl_glob := prefix :: (!pbl_glob)
    val goal_file = prefix ^ "_goal"
    val _ = debug ("export goal to " ^ goal_file)
  in
    export_goal goal_file g
  end

fun record_proof name lflag tac1 tac2 (g:goal) =
  let
    val _ = save_goal g
    val _ = start_record_proof name
    val pflag = String.isPrefix "tactictoe_prove_" name
    val b2 = (not (!record_prove_flag) andalso pflag)
    val b3 = (not (!record_let_flag) andalso lflag)
    val result =
      if b2 orelse b3 then
        (debug "record proof: ignored"; incr n_proof_ignored; tac2 g)
      else
        let
          val (r,t) = add_time tac1 g
          val _ = record_time := !record_time + t;
          val _ = debug ("record time: " ^ Real.toString t)
          val _ = total_time learn_time (end_record_proof name) g
        in
          if null (fst r) then r
          else (debug "error: record_proof: not null"; tac2 g)
        end
        handle Interrupt => raise Interrupt
          | _ => (debug "error: record_proof: exception"; tac2 g)
  in
    result
  end

(* ----------------------------------------------------------------------
   Theory hooks
   ---------------------------------------------------------------------- *)

fun start_record_thy thy =
  (
  print_endline "importing tactic data";
  tacdata_glob := create_tacdata ()
  )

fun end_record_thy thy =
  (
  print_endline "recording successful";
  write_info thy;
  print_endline "exporting tactic data";
  ttt_export_tacdata thy (!tacdata_glob);
  if !record_savestate_flag
  then
    (mkDir_err (tactictoe_dir ^ "/savestate");
     writel (tactictoe_dir ^ "/savestate/" ^ thy ^ "_pbl") (rev (!pbl_glob)))
  else ();
  print_endline "export successful"
  )

end (* struct *)
