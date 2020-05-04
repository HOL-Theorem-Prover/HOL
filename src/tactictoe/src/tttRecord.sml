(* ========================================================================  *)
(* FILE          : tttRecord.sml                                             *)
(* DESCRIPTION   : Functions used in files written by tttUnfold              *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2017                                                      *)
(* ========================================================================= *)

structure tttRecord :> tttRecord =
struct

open HolKernel boolLib aiLib
  smlLexer smlTimeout smlExecute smlTag smlParser smlRedirect
  mlFeature mlThmData mlTacticData
  tttSetup tttLearn

val ERR = mk_HOL_ERR "tttRecord"
fun debug s = debug_in_dir ttt_debugdir "tttRecord" s
val ttt_expdir = HOLDIR ^ "/src/tactictoe/experiment"
fun log s = debug_in_dir ttt_expdir "log" s

(* -------------------------------------------------------------------------
   Globals
   ------------------------------------------------------------------------- *)

val goalstep_glob = ref []
fun local_tag x = x
fun add_local_tag s = "( tttRecord.local_tag " ^ s ^ ")"
val tacdata_glob = ref empty_tacdata

(* -------------------------------------------------------------------------
   Messages and profiling
   ------------------------------------------------------------------------- *)

fun tactic_msg msg stac g =
  debug ("replay_tactic " ^ msg ^ ": " ^ stac)

fun proof_msg f_debug prefix msg thmname qtac final_stac =
  (
  f_debug thmname;
  f_debug (prefix ^ " " ^ msg ^ ":");
  f_debug ("  " ^ qtac);
  f_debug ("  " ^ final_stac);
  f_debug ""
  )

fun replay_msg msg thmname qtac final_stac =
  proof_msg debug "replay_proof" msg thmname qtac final_stac
fun parse_msg thmname qtac final_stac =
  proof_msg debug "" "parse_proof" thmname qtac final_stac
fun parse_err thmname qtac final_stac =
  (parse_msg thmname qtac final_stac; raise ERR "" "")

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
   "(" ^ its (!n_proof_ignored) ^ " ignored (contains let))",
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
    val infol = info_thy thy
  in
    mkDir_err infodir;
    writel (infodir ^ "/" ^ thy) infol;
    app print_endline infol
  end

(* -------------------------------------------------------------------------
   Replaying a tactic
   ------------------------------------------------------------------------- *)

fun tactic_err msg stac g =
  (tactic_msg msg stac g; raise ERR "record_tactic" "")

fun record_tactic (tac,stac) g =
  let 
    val ((gl,v),t) = add_time tac g 
  in
    incr n_tactic_replayed;
    goalstep_glob := ((stac,t,g,gl),v) :: !goalstep_glob;
    (gl,v)
  end

(* -------------------------------------------------------------------------
   Replaying a proof
   ------------------------------------------------------------------------- *)

fun wrap_tactics_in name qtac goal =
  let
    val success_flag = ref NONE
    val cthy = current_theory ()
    val final_stac_ref = ref ""
    fun mk_alttac qtac =
      let
        val _ = final_stac_ref := ""
        val s2 = number_stac qtac
        val ostac = partial_sml_lexer s2
        val l2 = extract_tacticl s2
        val _  = debug ("org tac number: " ^ int_to_string (length l2))
        val _  = n_tactic_parsed := (!n_tactic_parsed) + length l2
        val _  = print_endline (int_to_string (!n_tactic_parsed))
        val l3 = map_assoc drop_numbering l2
        fun mk_reps y =
          ["( tttRecord.record_tactic","("] @ y @
          [",", mlquote (String.concatWith " " y),")",")"]
        val l5 = map_snd mk_reps l3
        val ostac0 = fold_left replace_at l5 ostac
        val ostac1 = drop_numbering ostac0
        val final_stac = String.concatWith " " ostac1
        val _ = final_stac_ref := final_stac
        val final_tac = tactic_of_sml final_stac
      in
        (final_stac, final_tac)
      end
      handle Interrupt => raise Interrupt
           | _ => parse_err name qtac (!final_stac_ref)
    val (final_stac, final_tac)  =
      total_time parse_time (hide_out mk_alttac) qtac
  in
    incr n_proof_parsed;
    (
    let val (gl,v) =
      total_time replay_time (timeout (!ttt_recproof_time) final_tac) goal
    in
      if null gl
      then (success_flag := SOME (gl,v); incr n_proof_replayed)
      else replay_msg "opened goals" name qtac final_stac
    end
    handle
        Interrupt => raise Interrupt
      | FunctionTimeout => replay_msg "timed out" name qtac final_stac
      | _       => replay_msg "other error" name qtac final_stac
    );
    case (!success_flag) of SOME x => x | NONE => raise ERR "" ""
  end

(*---------------------------------------------------------------------------
  Globalizing theorems and create a new theorem if the value does not exists.
  ---------------------------------------------------------------------------*)

fun fetch s reps =
  let val sthmo = hide_out thm_of_sml s in
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
  let val outname = "\nName: " ^ int_to_string (!n_proof) ^ " " ^ name in
    debug outname; incr n_proof; goalstep_glob := []
  end

fun end_record_proof name g =
  let
    val l1 = map fst (rev (!goalstep_glob))
    val _ = if !thmlintac_flag then app save_thmlintac l1 else ()
    val (thmdata,tacdata) = (create_thmdata (), !tacdata_glob)
    val l2 = map (orthogonalize (thmdata,tacdata)) l1
    val newtacdata = foldl ttt_update_tacdata tacdata l2
  in
    debug ("Saving " ^ int_to_string (length l2) ^ " labels");
    tacdata_glob := newtacdata
  end

fun record_proof name lflag tac1 tac2 g =
  let
    val _ = start_record_proof name
    val pflag = String.isPrefix "tactictoe_prove_" name
    val b2 = (not (!ttt_recprove_flag) andalso pflag)
    val b3 = (not (!ttt_reclet_flag) andalso lflag)
    val eval_ignore = pflag orelse lflag orelse
                      not (isSome (!ttt_evalfun_glob))
    val result =
      if b2 orelse b3 then (incr n_proof_ignored; tac2 g) else
        let
          val _ = if eval_ignore then () else
            let 
              val tptpname = escape ("thm." ^ current_theory () ^ "." ^ name)
              val _ = log_eval ("Alt-Theorem: " ^ tptpname)
              val (thmdata,tacdata) = (create_thmdata (), !tacdata_glob) 
            in
              (valOf (!ttt_evalfun_glob)) (thmdata,tacdata)
              (current_theory (), name) g
            end
          val (r,t) = add_time tac1 g
          val _ = record_time := !record_time + t;
          val _ = debug ("Record time: " ^ Real.toString t)
          val _ = total_time learn_time (end_record_proof name) g
        in
          if null (fst r) then r
          else (debug "record_proof: not null"; tac2 g)
        end
        handle _ =>
          (debug "record_proof: exception"; tac2 g)
  in
    result
  end

(* ----------------------------------------------------------------------
   Theory hooks
   ---------------------------------------------------------------------- *)

fun start_record_thy thy = 
  (
  print_endline "Importing tactic data";
  tacdata_glob := ttt_create_tacdata ()
  )

fun end_record_thy thy =
  (
  print_endline "Recording successful";
  write_info thy;
  if not (!ttt_ttteval_flag orelse !ttt_hheval_flag) then 
  (
  print_endline "Exporting tactic data";
  ttt_export_tacdata thy (!tacdata_glob);
  print_endline "Export successful"
  )
  else ()
  ;
  if !ttt_ex_flag then
  (
  print_endline "Exporting positive and negative examples";
  ttt_export_exl_human thy (!exl_glob);
  ttt_export_exl thy (!exl_glob);
  ttt_export_tptpexl thy (!exl_glob);
  print_endline "Export successful"
  )
  else ()
  )

end (* struct *)
