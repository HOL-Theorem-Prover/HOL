(* =========================================================================  *)
(* FILE          : tttRecord.sml                                              *)
(* DESCRIPTION   : Record tactics, theorems and goal lists                    *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure tttRecord :> tttRecord =
struct

open HolKernel boolLib
tttTools tttLexer tttTimeout tttExec tttSetup
tttNumber tttExtract tttUnfold
tttThmData tttTacticData tttGoallistData
tttPredict tttLearn
tacticToe

val ERR = mk_HOL_ERR "tttRecord"

val goalstep_glob = ref []
val tactictoe_step_counter = ref 0
val tactictoe_thm_counter = ref 0

fun local_tag x = x
fun add_local_tag s = "( tttRecord.local_tag " ^ s ^ ")"

(*----------------------------------------------------------------------------
 * Error messages and profiling.
 *----------------------------------------------------------------------------*)

fun tactic_msg msg stac g =
  debug_replay ("replay_tactic " ^ msg ^ ": " ^ stac)

fun proof_msg f_debug prefix msg thmname qtac final_stac =
  (
  f_debug thmname;
  f_debug (prefix ^ " " ^ msg ^ ":");
  f_debug ("  " ^ qtac);
  f_debug ("  " ^ final_stac);
  f_debug ""
  )

fun replay_msg msg thmname qtac final_stac =
  proof_msg debug_replay "replay_proof" msg thmname qtac final_stac
fun parse_msg thmname qtac final_stac =
  proof_msg debug_parse "" "parse_proof" thmname qtac final_stac
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
  feature_time := 0.0;
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
    fun f i s = debug_record (int_to_string i ^ " " ^ s)
    fun g s r = debug_record (s ^ ": " ^ Real.toString r)
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
    g "    Tactic" (!tactic_time);
    g "    Feature" (!feature_time);
    f (length (!ttt_tacerr)) "bad tactics during evaluation"
  end

(* --------------------------------------------------------------------------
   Replaying a tactic.
   -------------------------------------------------------------------------- *)

fun tactic_err msg stac g =
  (tactic_msg msg stac g; raise ERR "record_tactic" "")

fun record_tactic_aux (tac,stac) g =
  let
    val ((gl,v),t) = add_time (timeOut (!ttt_rectac_time) tac) g
      handle TacTimeOut => tactic_err "timed out" stac g
            | x         => raise x
  in
    tactic_time := (!tactic_time) + t;
    n_tactic_replay_glob := (!n_tactic_replay_glob) + 1;
    goalstep_glob := ((stac,t,g,gl),v) :: !goalstep_glob;
    (gl,v)
  end

fun record_tactic (tac,stac) g =
  total_time record_time (record_tactic_aux (tac,stac)) g

(* --------------------------------------------------------------------------
   Replaying a proof: following code is legacy code (very ugly).
   -------------------------------------------------------------------------- *)

fun wrap_tactics_in name qtac goal =
  let
    val success_flag = ref NONE
    val cthy = current_theory ()
    val final_stac_ref = ref ""
    fun mk_alttac qtac =
      let
        val _ = final_stac_ref := ""
        val s2 = total_time number_time number_stac qtac
        val ostac = ttt_lex s2
        val l2 = total_time extract_time ttt_extract s2
        val _  = debug_proof ("Org tac number: " ^ int_to_string (length l2))
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
      handle _ => parse_err name qtac (!final_stac_ref)
    val (final_stac, final_tac)  =
      total_time hide_time (hide_out (total_time mkfinal_time mk_alttac)) qtac
  in
    print (int_to_string (!n_tactic_parse_glob) ^ "\n");
    incr n_parse_glob;
    (
    let
      val (gl,v) =
      total_time replay_time 
        (tttTimeout.timeOut (!ttt_recproof_time) final_tac) goal
    in
      if gl = []
        then (
             success_flag := SOME (gl,v);
             debug_proof ("Original proof time: " ^
                          Real.toString (!original_time));
             n_replay_glob := (!n_replay_glob + 1)
             )
      else replay_msg "opened goals" name qtac final_stac
    end
    handle
        TacTimeOut => replay_msg "timed out or other" name qtac final_stac
      | _          => replay_msg "other error" name qtac final_stac
    );
    case (!success_flag) of
      SOME x => x
    | NONE   => raise ERR "" ""
  end

(*----------------------------------------------------------------------------
  Globalizing theorems and create a new theorem if the value does not exists.
  ----------------------------------------------------------------------------*)

fun save_tactictoe_thm thm =
  let
    val name = "tactictoe_thm_" ^ int_to_string (!tactictoe_thm_counter)
    val _    = incr tactictoe_thm_counter
    val cthy = current_theory ()
  in
    ignore (save_thm (name,thm));
    String.concatWith " " ["(","DB.fetch",mlquote cthy,mlquote name,")"]
  end

fun depid_of_thm thm =
  (Dep.depid_of o Tag.dep_of o Thm.tag) thm
  handle HOL_ERR _ => raise ERR "depid_of_thm" ""

fun sml_of_thm thm =
  if can depid_of_thm thm then
    let
      val (thy,n) = depid_of_thm thm
      val thml = DB.thms thy
      val thmdict = dnew goal_compare (map (fn (a,b) => (dest_thm b,a)) thml)
      val goal = dest_thm thm
    in
      if dmem goal thmdict
      then
        let val name = dfind goal thmdict in
          SOME (String.concatWith " "
            ["(","DB.fetch",mlquote thy,mlquote name,")"])
        end
      else NONE
    end
  else NONE

(* replacement string is not used anymore for theorems *)
fun fetch_thm s reps =
  let val sthmo = hide_out thm_of_sml s in
    case sthmo of
      NONE =>
        (if reps = ""
        then (debug_record ("fetch_other: " ^ s); add_local_tag s)
        else reps)
    | SOME (_,thm) =>
    let val nameo = sml_of_thm thm in
      case nameo of
        SOME x => x
      | NONE => (debug_record ("fetch_thm: " ^ s); add_local_tag s)
    end
  end

val fetch = total_time fetch_thm_time fetch_thm

(* ----------------------------------------------------------------------
   Proof recording
   ---------------------------------------------------------------------- *)

val thm_counter = ref 0

fun start_record_proof name =
  let 
    val outname = "\nName: " ^ int_to_string (!thm_counter) ^ " " ^ name 
    val _ = update_thmfea (current_theory ())
  in
    debug_proof outname;
    debug_search outname;
    debug outname;
    incr thm_counter;
    goalstep_glob := []
  end

fun end_record_proof name g =
  let
    val lbl1 = map fst (rev (!goalstep_glob))
    fun noortho (stac,t,g,gl) = 
      case abstract_stac stac of
        SOME astac => [(stac,t,g,gl),(astac,t,g,gl)]
      | NONE => [(stac,t,g,gl)]
    fun ortho (stac,t,g,gl) = 
      [orthogonalize ((stac,t,g,gl), tttFeature.fea_of_goal g)]
    fun f lbl = if !ttt_ortho_flag then ortho lbl else noortho lbl
    val lbl2 = List.concat (map f lbl1)
  in
    debug_t ("Saving " ^ int_to_string (length lbl2) ^ " labels")
      (app update_tacdata) lbl2
  end

fun org_tac tac g =
  let val (gl,v) = tac g in
    if null gl then (gl,v)
    else (
         debug "Record error: org_tac: not null";
         ignore (tttExec.exec_sml "cache" "numSimps.clear_arith_caches ()");
         tac g
         )
  end
  handle _ =>
     (
     debug "Record error: org_tac";
     ignore (tttExec.exec_sml "cache" "numSimps.clear_arith_caches ()");
     tac g
     )

val fof_counter = ref 0

fun create_fof_wrap name pflag result =
  if !ttt_fof_flag andalso (not pflag orelse !ttt_evprove_flag) then 
    let
      val thm = (snd result) []
      val _ = update_create_fof ()
      val _ = incr fof_counter
      val is = int_to_string (!fof_counter)
      val newname = current_theory () ^ "__" ^ is ^ "__" ^ name 
    in
      (!create_fof_glob) newname thm
    end
  else ()

fun record_proof name lflag tac1 tac2 g =
  if !ttt_fof_flag then
    let 
      val pflag = String.isPrefix "tactictoe_prove_" name
      val result =  
        let val (r,t) = add_time (org_tac tac2) g in
          debug_proof ("Original proof time: " ^ Real.toString t);
          r
        end
      val _ = create_fof_wrap name pflag result
        handle _ => (debug "Error: create_fof_wrap"; ())
    in
      result
    end
  else
  let
    val _ = start_record_proof name
    val pflag = String.isPrefix "tactictoe_prove_" name
    val b2 = (not (!ttt_recprove_flag) andalso pflag)
    val b3 = (not (!ttt_reclet_flag) andalso lflag)
    val _ = 
      if !ttt_eval_flag andalso 
        (not pflag orelse !ttt_evprove_flag) andalso 
        (not lflag orelse !ttt_evlet_flag)
      then eval_tactictoe g 
      else ()
    val _ = 
      if !eprover_eval_flag andalso 
        (not pflag orelse !ttt_evprove_flag) andalso 
        (not lflag orelse !ttt_evlet_flag)
      then eval_eprover g 
      else ()
    val result =
      if b2 orelse b3 orelse (not (!ttt_record_flag))
      then
        let val (r,t) = add_time (org_tac tac2) g in
          debug_proof ("Original proof time: " ^ Real.toString t);
          r
        end
      else
        let
          val (r,t) = add_time tac1 g
          val _ = debug_proof ("Recording proof time: " ^ Real.toString t)
          val _ = end_record_proof name g
        in
          if null (fst r) then r
          else (debug "Record error: try_record_proof: not null"; 
                org_tac tac2 g)
        end
        handle _ => (debug "Record error: try_record_proof"; org_tac tac2 g)
  in
    result
  end

(*----------------------------------------------------------------------------
  Theory hooks
  ----------------------------------------------------------------------------*)

fun clean_subdirl thy dir subdirl =
  let
    fun clean_sub x =
      (mkDir_err (dir ^ "/" ^ x); erase_file (dir ^ "/" ^ x ^ "/" ^ thy))
  in
    mkDir_err dir;
    app clean_sub subdirl
  end

fun clean_dir thy dir = (mkDir_err dir; erase_file (dir ^ "/" ^ thy))
  
fun start_record_thy thy =
  (
  mkDir_err ttt_code_dir;
  mkDir_err ttt_proof_dir; clean_dir thy ttt_proof_dir;
  mkDir_err ttt_eproof_dir; clean_dir thy ttt_eproof_dir;
  (* Hack to record bool *)
  if thy = "ConseqConv"
  then (clean_tttdata ();
        clean_subdirl "bool" ttt_search_dir ["debug","search","proof"];
        mkDir_err ttt_thmfea_dir;
        debug_t "export_thmfea" export_thmfea "bool")
  else ();
  clean_tttdata ();
  reset_profiling ();
  (* Proof search *)
  clean_subdirl thy ttt_search_dir ["debug","search","proof"];
  mkDir_err ttt_tacfea_dir;
  mkDir_err ttt_thmfea_dir;
  mkDir_err ttt_glfea_dir;
  (* Tactic scripts recording *)
  clean_subdirl thy ttt_record_dir ["parse","replay","record"]
  )

fun end_record_thy thy =
  (
  if !ttt_eval_flag orelse !eprover_eval_flag 
  then debug "EvalSuccessful"
  else 
    (
    debug_t "export_tacdata" export_tacdata thy;
    debug_t "export_thmfea" export_thmfea thy;
    debug "RecordSuccessful"
    )  
  )

end (* struct *)
