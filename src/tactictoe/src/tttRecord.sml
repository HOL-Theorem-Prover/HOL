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
    if op_mem goal_eq g gl then () else
    calls_glob := (stac,g,gl) :: !calls_glob;
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
    val _ = if not (is_tactic ostac) then raise ERR "wrap_proof" "" else ()
    val smlexp = extract_smlexp ostac
    val proofexp = extract_proofexp smlexp
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
    (* precompute symweight *)
    val feal1 = List.concat (map (#fea o snd o snd) icalls1)
    val feal2 = mk_fast_set Int.compare feal1
    val (thmdata,tacdata) = (!thmdata_glob, !tacdata_glob)
    val calld = #calld tacdata
    val tacfea = total_time tacfea_time
      (map (fn (_,x) => (#stac x, #fea x))) (dlist calld)
    val tacsymweight = total_time learn_tfidf_time
      (learn_tfidf_symfreq (dlength calld) feal2) (#symfreq tacdata)
    val icalls2 = if not (!record_ortho_flag) then map snd icalls1 else
      map (orthogonalize (thmdata,tacdata,(tacsymweight,tacfea))) icalls1
    val newtacdata = foldl ttt_update_tacdata tacdata icalls2
  in
    debug ("saving " ^ int_to_string (length icalls2) ^ " calls");
    tacdata_glob := newtacdata
  end

(* ----------------------------------------------------------------------
   Thm data I/O
   ---------------------------------------------------------------------- *)

val thmdata_dir = tactictoe_dir ^ "/thmdata"

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
    val _ = mkDir_err thmdata_dir
    val thmidl = map fst (snd (create_thmdata ()))
    val file = thmdata_dir ^ "/" ^ current_theory () ^ "_" ^
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
  in
    write_thmdata file l2;
    namethm_glob := daddl l2 (!namethm_glob)
  end

(* ----------------------------------------------------------------------
   Savestates
   ---------------------------------------------------------------------- *)

val savestate_dir = tactictoe_dir ^ "/savestate"

fun ttt_before_save_state () =
  (
  if !record_flag
    then thmdata_glob := total_time create_thmdata_time create_thmdata ()
    else ();
  if !export_thmdata_flag then export_thmdata () else ();
  if !record_savestate_flag
    then (mkDir_err savestate_dir; PolyML.fullGC ())
    else ()
  )

fun ttt_save_state () =
  (
  if !record_savestate_flag then
  let
    val prefix = savestate_dir ^ "/" ^ current_theory () ^ "_" ^
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
    val savestate_dir = tactictoe_dir ^ "/savestate"
    val _ = mkDir_err savestate_dir
    val prefix = savestate_dir ^ "/" ^ current_theory () ^ "_" ^
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
    (mkDir_err (tactictoe_dir ^ "/savestate");
     writel (tactictoe_dir ^ "/savestate/" ^ thy ^ "_pbl") (rev (!pbl_glob)))
  else ();
  print_endline "export successful"
  )

end (* struct *)
