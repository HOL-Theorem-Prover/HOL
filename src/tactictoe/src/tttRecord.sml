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
  mlFeature mlThmData mlTacticData
  tttSetup tttLearn

val ERR = mk_HOL_ERR "tttRecord"

(* -------------------------------------------------------------------------
   Globals
   ------------------------------------------------------------------------- *)

val goalstep_glob = ref []
fun local_tag x = x
fun add_local_tag s = "( tttRecord.local_tag " ^ s ^ ")"
val tacdata_glob = ref empty_tacdata
val thmdata_glob = ref empty_thmdata
val pbl_glob = ref []
val record_tactic_time = ref 2.0
val record_proof_time = ref 20.0

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
   " tactic test: " ^ rts_round 6 (!ortho_teststac_time) ^ ")"
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
    goalstep_glob := ((stac,t,g,gl),v) :: !goalstep_glob;
    (gl,v)
  end
  handle Interrupt => raise Interrupt 
    |  _ => (debug ("Error recording tactic: " ^ stac); 
             raise ERR "record_tactic" stac)

(* -------------------------------------------------------------------------
   Replaying a proof
   ------------------------------------------------------------------------- *)

fun wrap_stac stac = String.concatWith " "
  ["( tttRecord.record_tactic","(",stac,",",mlquote stac,")",")"]

fun wrap_tacexp e = case e of
    SmlTactic stac => if is_tactic stac
                      then SmlTactic (wrap_stac stac)
                      else SmlTactic stac
  | SmlTactical _ => e
  | SmlInfix (s,(e1,e2)) => SmlInfix (s,(wrap_tacexp e1, wrap_tacexp e2))

fun wrap_proof ostac =
  let
    (* val _ =  debug ("original proof: " ^ ostac) *)
    val tacexp = extract_tacexp ostac
    val ntac = size_of_tacexp tacexp
    val _  = debug ("#tactics (proof): " ^ its ntac)
    val _  = n_tactic_parsed := (!n_tactic_parsed) + ntac
    val _  = debug ("#tactics (total): " ^ its (!n_tactic_parsed))
    val wstac = string_of_tacexp (wrap_tacexp tacexp)
    (* val _ = debug ("wrapped proof: " ^ wstac) *)
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

val savestate_level = ref 0

fun start_record_proof name =
  let val outname = "Name: " ^ its ((!savestate_level) - 1) ^ " " ^ name in
    debug outname; incr n_proof; goalstep_glob := []
  end

fun end_record_proof name g =
  let
    val l1 = map fst (rev (!goalstep_glob))
    val _ = if !thmlintac_flag then app save_thmlintac l1 else ()
    val (thmdata,tacdata) = (!thmdata_glob, !tacdata_glob)
    val l2 = if !ttt_ortho_flag
      then map (orthogonalize (thmdata,tacdata)) l1
      else l1
    val newtacdata = foldl ttt_update_tacdata tacdata l2
  in
    debug ("saving " ^ int_to_string (length l2) ^ " labels");
    tacdata_glob := newtacdata
  end

(* The value of 50 is a compromise between fast saveState/saveChild
   and fast loadState. Probably loading
   becomes too slow above 50 * 50 = 2500 savestates
   per theory. *)
fun ttt_save_state () =
  (
  if !ttt_savestate_flag then
  let
    val savestate_dir = tactictoe_dir ^ "/savestate"
    val _ = mkDir_err savestate_dir
    val prefix = savestate_dir ^ "/" ^ current_theory () ^
      its (!savestate_level)
    val savestate_file = prefix ^ "_savestate"
    val _ = debug ("saving state to " ^ savestate_file)
  in
    if !savestate_level = 0
    then PolyML.SaveState.saveState savestate_file
    else PolyML.SaveState.saveChild (savestate_file,
                 ((!savestate_level) div 50) + 1)
  end
  else ();
  incr savestate_level
  )

fun save_goal g =
  let
    val savestate_dir = tactictoe_dir ^ "/savestate"
    val _ = mkDir_err savestate_dir
    val prefix = savestate_dir ^ "/" ^ current_theory () ^
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
    val tptpname = escape ("thm." ^ current_theory () ^ "." ^ name)
    val _ = debug ("\nrecord_proof: " ^ tptpname)
    val _ = start_record_proof name
    val pflag = String.isPrefix "tactictoe_prove_" name
    val b2 = (not (!ttt_recprove_flag) andalso pflag)
    val b3 = (not (!ttt_reclet_flag) andalso lflag)
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
          else (debug "record_proof: error not null"; tac2 g)
        end
        handle Interrupt => raise Interrupt
          | _ => (debug "record_proof: error exception"; tac2 g)
  in
    result
  end

(* ----------------------------------------------------------------------
   Theory hooks
   ---------------------------------------------------------------------- *)

fun start_record_thy thy =
  (
  print_endline "importing tactic data";
  tacdata_glob := ttt_create_tacdata ()
  )

fun end_record_thy thy =
  (
  print_endline "recording successful";
  write_info thy;
  print_endline "exporting tactic data";
  ttt_export_tacdata thy (!tacdata_glob);
  if !ttt_savestate_flag
  then
    (mkDir_err (tactictoe_dir ^ "/savestate");
     writel (tactictoe_dir ^ "/savestate/" ^ thy ^ "_pbl") (rev (!pbl_glob)))
  else ();
  print_endline "export successful";
  if !ttt_ex_flag then
  (
  debug "exporting positive and negative examples";
  ttt_export_exl_human thy (!exl_glob);
  ttt_export_exl thy (!exl_glob);
  ttt_export_tptpexl thy (!exl_glob);
  debug "export successful"
  )
  else ()
  )

end (* struct *)
