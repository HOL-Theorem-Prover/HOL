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

val goalstep_glob = ref []
val tactictoe_step_counter = ref 0
val tactictoe_thm_counter = ref 0

fun local_tag x = x
fun add_local_tag s = "( tttRecord.local_tag " ^ s ^ ")"

(* -------------------------------------------------------------------------
   Error messages and profiling
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

val n_parse_glob = ref 0
val n_replay_glob = ref 0
val n_tactic_parse_glob = ref 0
val n_tactic_replay_glob = ref 0

val tactic_time = ref 0.0
val save_time = ref 0.0
val record_time = ref 0.0
val extract_time = ref 0.0
val number_time = ref 0.0
val exec_time = ref 0.0
val mkfinal_time = ref 0.0
val hide_time = ref 0.0
val replay_time = ref 0.0
val original_time = ref 0.0
val fetch_thm_time = ref 0.0

fun reset_profiling () =
  (
  fetch_thm_time := 0.0;
  tactic_time := 0.0;
  save_time := 0.0;
  record_time := 0.0;
  extract_time := 0.0;
  number_time := 0.0;
  exec_time := 0.0;
  mkfinal_time := 0.0;
  hide_time := 0.0;
  replay_time := 0.0;
  n_parse_glob := 0; n_replay_glob := 0;
  n_tactic_parse_glob := 0; n_tactic_replay_glob := 0;
  (* not part of profiling but is there for now *)
  tactictoe_step_counter := 0
  )

fun out_record_summary cthy =
  let
    fun f i s = debug (int_to_string i ^ " " ^ s)
    fun g s r = debug (s ^ ": " ^ Real.toString r)
  in
    f (!n_parse_glob)  "proofs parsed";
    f (!n_replay_glob) "proofs replayed";
    f (!n_tactic_parse_glob) "tactic parsed";
    f (!n_tactic_replay_glob) "tactic replayed";
    g "  Fetch thm" (!fetch_thm_time);
    g "  Parse" (!hide_time);
    g "    Hide" (!hide_time - !mkfinal_time);
    g "    Number" (!number_time);
    g "    Extract" (!extract_time);
    g "    Tactic_of_sml" (!exec_time);
    g "  Replay" (!replay_time);
    g "    Record" (!record_time);
    g "    Save" (!save_time);
    g "    Tactic" (!tactic_time)
  end

(* -------------------------------------------------------------------------
   Replaying a tactic
   ------------------------------------------------------------------------- *)

fun tactic_err msg stac g =
  (tactic_msg msg stac g; raise ERR "record_tactic" "")

fun record_tactic_aux (tac,stac) g =
  let val ((gl,v),t) = add_time tac g in
    tactic_time := (!tactic_time) + t;
    n_tactic_replay_glob := (!n_tactic_replay_glob) + 1;
    goalstep_glob := ((stac,t,g,gl),v) :: !goalstep_glob;
    (gl,v)
  end

fun record_tactic (tac,stac) g =
  total_time record_time (record_tactic_aux (tac,stac)) g

(* -------------------------------------------------------------------------
   Replaying a proof  ------------------------------------------------------------------------- *)

fun wrap_tactics_in name qtac goal =
  let
    val success_flag = ref NONE
    val cthy = current_theory ()
    val final_stac_ref = ref ""
    fun mk_alttac qtac =
      let
        val _ = final_stac_ref := ""
        val s2 = total_time number_time number_stac qtac
        val ostac = partial_sml_lexer s2
        val l2 = total_time extract_time extract_tacticl s2
        val _  = debug ("org tac number: " ^ int_to_string (length l2))
        val _  = n_tactic_parse_glob := (!n_tactic_parse_glob) + length l2;
        val l3 = map (fn x => (x, drop_numbering x)) l2
        fun mk_reps (x,y) =
          ["( tttRecord.record_tactic","("] @ y @
          [",", mlquote (String.concatWith " " y),")",")"]
        val l5 = map (fn (x,y) => (x, mk_reps (x,y))) l3
        val ostac0 = fold_left replace_at l5 ostac
        val ostac1 = drop_numbering ostac0
        val final_stac = String.concatWith " " ostac1
        val _ = final_stac_ref := final_stac
        val final_tac = total_time exec_time tactic_of_sml final_stac
      in
        (final_stac, final_tac)
      end
      handle Interrupt => raise Interrupt
        | _ => parse_err name qtac (!final_stac_ref)
    val (final_stac, final_tac)  =
      total_time hide_time (hide_out (total_time mkfinal_time mk_alttac)) qtac
  in
    print (int_to_string (!n_tactic_parse_glob) ^ "\n");
    incr n_parse_glob;
    (
    let
      val (gl,v) =
        total_time replay_time
        (timeout (!ttt_recproof_time) final_tac) goal
    in
      if null gl
        then (
             success_flag := SOME (gl,v);
             n_replay_glob := (!n_replay_glob + 1)
             )
      else replay_msg "opened goals" name qtac final_stac
    end
    handle
        Interrupt => raise Interrupt
      | FunctionTimeout => replay_msg "timed out" name qtac final_stac
      | _       => replay_msg "other error" name qtac final_stac
    );
    case (!success_flag) of
      SOME x => x
    | NONE   => raise ERR "" ""
  end

(*---------------------------------------------------------------------------
  Globalizing theorems and create a new theorem if the value does not exists.
  ---------------------------------------------------------------------------*)

(* replacement string is not used anymore for theorems *)
fun fetch_thm s reps =
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

val fetch = total_time fetch_thm_time fetch_thm

(* ----------------------------------------------------------------------
   Proof recording
   ---------------------------------------------------------------------- *)

val thm_counter = ref 0

fun start_record_proof name =
  let val outname = "\nName: " ^ int_to_string (!thm_counter) ^ " " ^ name in
    debug outname;
    incr thm_counter;
    goalstep_glob := []
  end

(* communication channel between the record calls *)
val tacdata_glob = ref empty_tacdata

fun end_record_proof name g =
  let
    val (thmdata,tacdata) = (create_thmdata (), !tacdata_glob)
    val l1 = map fst (rev (!goalstep_glob))
    fun f lbl = orthogonalize (thmdata,tacdata) lbl
    val l2 = map f l1
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
      if b2 orelse b3 then tac2 g else
        let
          val _ = if eval_ignore then () else
            let val (thmdata,tacdata) = (create_thmdata (), !tacdata_glob) in
              (valOf (!ttt_evalfun_glob)) (thmdata,tacdata) g
            end
          val (r,t) = add_time tac1 g
          val _ = debug ("Recording proof time: " ^ Real.toString t)
          val _ = end_record_proof name g
        in
          if null (fst r) then r
          else (debug "record_proof: not null"; tac2 g)
        end
        (* expected to catch interrupts *)
        handle _ => (debug "record_proof: exception"; tac2 g)
  in
    result
  end

(* ----------------------------------------------------------------------
   Theory hooks
   ---------------------------------------------------------------------- *)

fun start_record_thy thy =
  (tacdata_glob := empty_tacdata; reset_profiling ())

fun end_record_thy thy =
  (ttt_export_tacdata thy (!tacdata_glob); debug "record successful")


end (* struct *)
