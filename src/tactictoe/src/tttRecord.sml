(* ========================================================================  *)
(* FILE          : tttRecord.sml                                             *)
(* DESCRIPTION   : Functions used in files written by tttUnfold              *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2017                                                      *)
(* ========================================================================= *)

structure tttRecord :> tttRecord =
struct

open HolKernel boolLib aiLib
  smlLexer smlExecute smlParser smlRedirect
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
val record_proof_string_size = ref 50000
val name_glob = ref ""

(* Substrings that mark a reproduction string (reps) as dangerous to
   re-evaluate.  When `fetch s reps` is called for a local binding `s`
   that is not a global theorem (thm_of_sml returns NONE), returning reps
   verbatim would re-run the proof/definition it reproduces and re-store
   the result, causing a DUP crash (e.g. `SIMPLE_GUESS_FORALL_def` in
   quantHeuristics, whose reps re-runs `TotalDefn.located_qDefine`).
   Matching is by substring, so each entry also covers its prefixed and
   suffixed variants.  Keep this list shared with tttUnfold: every
   operation its rewriter watches is unsafe to replay here. *)
val dangerous_store_substrings = watched_store_operations

fun reps_is_dangerous reps =
  List.exists (fn sub => String.isSubstring sub reps)
    dangerous_store_substrings

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
    val infodir = tactictoe_dir_of () ^ "/log/info"
    val _ = app mkDir_err [OS.Path.dir infodir, infodir]
    val infol = info_thy thy
  in
    writel (infodir ^ "/" ^ thy) infol;
    app debug infol
  end

(* -------------------------------------------------------------------------
   Replaying a tactic
   ------------------------------------------------------------------------- *)

fun record_tactic (tac,stac) g =
  let
    val ((gl,v),t) = add_time tac g
    val _ =
      (incr n_tactic_replayed;
       if op_mem goal_eq g gl then () else
       calls_glob := (stac,g,gl) :: !calls_glob)
      handle Interrupt => raise Interrupt
           | e => debug ("error: recording tactic result: " ^ stac ^
                          ": " ^ exnMessage e)
  in
    (gl,v)
  end

(* -------------------------------------------------------------------------
   Replaying a proof
   ------------------------------------------------------------------------- *)

fun wrap_stac run_stac recorded_stac = String.concatWith " "
  ["( tttRecord.record_tactic","(",run_stac,",",mlquote recorded_stac,
   ")",")"]

(* Execute the exact source tactic.  The globalized version exists only to
   label the recorded call; executing it can change termination behaviour
   when unfolding replaces local aliases or theorem values. *)
fun wrap_proofexp run_exp recorded_exp = case (run_exp,recorded_exp) of
    (ProofTactic run_stac, ProofTactic recorded_stac) =>
      ProofTactic (wrap_stac run_stac recorded_stac)
  | (ProofOther _, _) => run_exp
  | (ProofTactical run_stac, _) => ProofTactical ("op " ^ run_stac)
  | (ProofInfix (s,(e1,e2)), ProofInfix (_,(r1,r2))) =>
      ProofInfix (s,(wrap_proofexp e1 r1, wrap_proofexp e2 r2))
  | _ => ProofTactic
      (wrap_stac (string_of_proofexp run_exp)
         (string_of_proofexp recorded_exp))

fun wrap_proof run_stac recorded_stac =
  let
    val _ = if not (is_tactic run_stac) then raise ERR "wrap_proof" "" else ()
    val run_exp = extract_proofexp (extract_smlexp run_stac)
    val recorded_exp = extract_proofexp (extract_smlexp recorded_stac)
    val ntac = size_of_proofexp run_exp
    val _  = debug ("#tactics (proof): " ^ its ntac)
    val _  = n_tactic_parsed := (!n_tactic_parsed) + ntac
    val _  = debug ("#tactics (total): " ^ its (!n_tactic_parsed))
    val wstac = string_of_proofexp (wrap_proofexp run_exp recorded_exp)
  in
    (wstac, tactic_of_sml_no_timeout wstac)
  end

fun app_wrap_proof name run_stac recorded_stac =
  if String.size run_stac > !record_proof_string_size orelse
     String.size recorded_stac > !record_proof_string_size then
    (fn _ =>
      (debug ("proof string too large: " ^ name);
       raise ERR "app_wrap_proof" name))
  else
    fn goal =>
      let
        val (wstac,wtac) = total_time parse_time
          (wrap_proof run_stac) recorded_stac
        val _ = incr n_proof_parsed
      in
        let val (gl,v) = total_time replay_time wtac goal
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
        if reps = "" then
          (debug ("fetch_other: " ^ s); add_local_tag s)
        else if reps_is_dangerous reps then
          (* reps would re-run a proof or definition (and re-store the
             result, causing a DUP) when s is a let-bound local that is
             not a global thm binding.  This happens for both theorem
             stores (`store_thm_at`) and definition forms
             (`located_qDefine`, `qDefine`, ...).  Prefer a safe
             local-tag placeholder so the surrounding tactic fails to
             replay cleanly and record_proof falls back to the raw
             tactic, instead of crashing the whole theory recording. *)
          (debug ("fetch_local: " ^ s); add_local_tag s)
        else reps
    | SOME (_,thm) =>
    let val nameo = dbfetch_of_depid thm in
      case nameo of
        SOME x => x
      | NONE => (debug ("fetch_thm: " ^ s); add_local_tag s)
    end
  end

(* ----------------------------------------------------------------------
   Recording
   ---------------------------------------------------------------------- *)

fun start_record_proof name =
  (
  incr n_proof; calls_glob := [];
  debug ("Name: " ^ its ((!savestate_level) - 1) ^ " " ^ name)
  )

fun end_record_proof name =
  let
    (* transforming into a call *)
    val precalls = number_snd 0 (rev (!calls_glob))
    val parentd = dregroup goal_compare (map_fst (fn (_,g,_) => g) precalls)
    fun find_parents gl =
      let fun f x = dfind x parentd handle NotFound => [] in
        mk_fast_set Int.compare (List.concat (map f gl))
      end
    fun init_call ((stac,g,gl),n) = ((g,gl),
      (
      (current_theory (), (!savestate_level) - 1, n),
      {stac= stac, ogl = find_parents gl, fea = fea_of_goal true g}
      ))
    val icalls1 = map init_call precalls
    (* Record the calls that the source proof actually made.  The former
       orthogonalization pass speculatively executed unrelated predicted
       tactics under very short Poly/ML thread timeouts.  Those workers can
       survive interruption and wedge a valid theory, and substituting a
       predicted tactic also makes the recording cease to describe the
       source proof. *)
    val icalls2 = map snd icalls1
    val newtacdata = foldl ttt_update_tacdata (!tacdata_glob) icalls2
  in
    debug ("saving " ^ int_to_string (length icalls2) ^ " calls");
    tacdata_glob := newtacdata
  end

(* ----------------------------------------------------------------------
   Thm data I/O
   ---------------------------------------------------------------------- *)

fun thmdata_dir () = tactictoe_dir_of () ^ "/thmdata"

val namethm_glob = ref (dempty String.compare)

local open SharingTables HOLsexp in
fun enc_thmdata_one enc_tm =
  pair_encode (String, list_encode enc_tm)
fun dec_thmdata_one dec_tm =
  pair_decode (string_decode, list_decode dec_tm)
fun enc_thmdata enc_tm = list_encode (enc_thmdata_one enc_tm)
fun dec_thmdata dec_tm = list_decode (dec_thmdata_one dec_tm)
fun tml_of_thmdata l = List.concat (map snd l)
end

fun tml_of_thm thm = let val (asl,w) = dest_thm thm in w :: asl end
fun goal_of_tml tml = (tl tml, hd tml)

fun write_thmdata file thmdata =
  write_tmdata (enc_thmdata, tml_of_thmdata) file (map_snd tml_of_thm thmdata)
fun read_thmdata file =
  map_snd goal_of_tml (read_tmdata dec_thmdata file)

fun thm_compare (thm1,thm2) = goal_compare (dest_thm thm1, dest_thm thm2)

fun export_thmdata () =
  let
    val _ = mkDir_err (thmdata_dir ())
    val thmidl = map fst (snd (create_thmdata ()))
    val file = thmdata_dir () ^ "/" ^ current_theory () ^ "_" ^
      its (!savestate_level)
    val set = dset (cpl_compare String.compare thm_compare)
      (dlist (!namethm_glob))
    fun test x = String.isPrefix (namespace_tag ^ "Theory") x
    val thmidl_namespace = filter test thmidl
    val namethm_curthy =
      map_fst (fn x => current_theory () ^ "Theory." ^ x)
        (DB.thms (current_theory ()))
    val l1 = namethm_curthy @ thml_of_namel thmidl_namespace
    val l2 = filter (fn x => not (dmem x set)) l1
    val tmp = file ^ "." ^ Portable.unique_tmp_suffix () ^ ".tmp"
  in
    ((write_thmdata tmp l2;
      OS.FileSys.rename {old = tmp, new = file})
     handle e => (remove_file tmp; raise e));
    namethm_glob := daddl l2 (!namethm_glob)
  end

(* ----------------------------------------------------------------------
   Savestates
   ---------------------------------------------------------------------- *)

fun savestate_dir () = tactictoe_dir_of () ^ "/savestate"

fun ttt_before_save_state () =
  (
  if !record_flag
    then thmdata_glob := total_time create_thmdata_time create_thmdata ()
    else ();
  if !export_thmdata_flag then export_thmdata () else ();
  if !record_savestate_flag
    then (mkDir_err (savestate_dir ()); PolyML.fullGC ())
    else ()
  )

fun ttt_save_state () =
  (
  if !record_savestate_flag then
  let
    val prefix = savestate_dir () ^ "/" ^ current_theory () ^ "_" ^
      its (!savestate_level)
    val savestate_file = prefix ^ "_savestate"
    val _ = debug ("saving state to " ^ savestate_file)
  in
    if !savestate_level = 0
    then PolyML.SaveState.saveState savestate_file
    else PolyML.SaveState.saveChild (savestate_file, !savestate_level)
  end
  else ()
  )

fun ttt_after_save_state () = incr savestate_level

fun save_goal lflag pflag g =
  let
    fun savestate_dir () = tactictoe_dir_of () ^ "/savestate"
    val _ = mkDir_err (savestate_dir ())
    val prefix = savestate_dir () ^ "/" ^ current_theory () ^ "_" ^
      its ((!savestate_level) - 1)
    val _ = pbl_glob := prefix :: (!pbl_glob)
    val goal_file = prefix ^ "_goal"
    val flags_file = prefix ^ "_flags"
    val _ = debug ("export goal to " ^ goal_file)
  in
    export_goal goal_file g;
    writel flags_file (map bts [lflag,pflag])
  end

(* ----------------------------------------------------------------------
   Recording (continued)
   ---------------------------------------------------------------------- *)

fun record_proof name lflag tac1 tac2 (g:goal) =
  let
    val pflag = String.isPrefix "tactictoe_prove_" name
    val _ = if !record_savestate_flag then save_goal lflag pflag g else ()
    val _ = start_record_proof name
    val b1 = (not (!record_flag))
    val b2 = (not (!record_prove_flag) andalso pflag)
    val b3 = (not (!record_let_flag) andalso lflag)
    val result =
      if b1 orelse b2 orelse b3 then
        (debug "record proof: ignored"; incr n_proof_ignored; tac2 g)
      else
        let
          val (r,t) = add_time tac1 g
          val _ = record_time := !record_time + t;
          val _ = debug ("record time: " ^ Real.toString t)
          val _ = total_time learn_time end_record_proof name
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
  namethm_glob := dempty String.compare;
  print_endline "importing tactic data";
  tacdata_glob := create_tacdata ()
  )

fun end_record_thy thy =
  (
  print_endline "recording successful";
  write_info thy;
  if !record_flag
  then
    (
    ttt_export_tacdata thy (!tacdata_glob);
    print_endline "exporting tactic data"
    )
  else ();
  if !record_savestate_flag
  then
    (mkDir_err (savestate_dir ());
     writel (savestate_dir () ^ "/" ^ thy ^ "_pbl") (rev (!pbl_glob)))
  else ();
  print_endline "export successful"
  )

end (* struct *)
