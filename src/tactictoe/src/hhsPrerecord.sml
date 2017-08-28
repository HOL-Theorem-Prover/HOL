(* =========================================================================  *)
(* FILE          : hhsPrererecord.sml                                         *)
(* DESCRIPTION   : Record tactics and their given goals (or their features)   *)
(* machine learning programs                                                  *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsPrerecord :> hhsPrerecord =
struct

open HolKernel boolLib hhsTools hhsLexer hhsData hhsNumber hhsExtract hhsUnfold 
hhsTimeout hhsData hhsOnline

val ERR = mk_HOL_ERR "hhsPrerecord"

(*----------------------------------------------------------------------------
 * Error messages
 *----------------------------------------------------------------------------*)

val hidden_file = tactictoe_dir ^ "/hidden"

fun tactic_msg msg stac g = 
  (
  debug_replay ("Tactic " ^ msg ^ ": " ^ stac); 
  debug_replay ("  on " ^ string_of_goal g)
  )

fun proof_msg f_debug prefix msg thmname qtac final_stac =
  (
  f_debug thmname;
  f_debug (prefix ^ msg ^ ":");
  f_debug ("  " ^ qtac);
  f_debug ("  " ^ final_stac);
  f_debug ""
  )

fun replay_msg msg thmname qtac final_stac = 
  proof_msg debug_replay "Proof " msg thmname qtac final_stac
fun parse_msg thmname qtac final_stac = 
  proof_msg debug_parse "" "Parse" thmname qtac final_stac
fun parse_err thmname qtac final_stac = 
  (parse_msg thmname qtac final_stac; raise ERR "hhs_record" "")
  
(*----------------------------------------------------------------------------
 * Profiling
 *----------------------------------------------------------------------------*)

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
  n_tactic_parse_glob := 0; n_tactic_replay_glob := 0
  )

fun mk_summary cthy =
  let  
    val file = tactictoe_dir ^ "/record_log/" ^ cthy ^ "/summary"
    fun f i s = append_endline file (int_to_string i ^ " " ^ s) 
    fun g s r = append_endline file (s ^ ": " ^ Real.toString r)
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
    g "    Feature" (!feature_time)
  end

(* --------------------------------------------------------------------------
   Replaying a tactic.
   -------------------------------------------------------------------------- *)

fun tactic_err msg stac g = (tactic_msg msg stac g; raise ERR "hhs_record" "")

fun hhs_record_aux (tac,stac) g =
  let
    val ((gl,v),t) = add_time (timeOut 2.0 tac) g 
      handle TacTimeOut => tactic_err "timed out" stac g
            | x         => raise x
  in
    tactic_time := (!tactic_time) + t;
    n_tactic_replay_glob := (!n_tactic_replay_glob) + 1;
    total_time save_time save_lbl (stac,t,g,gl);
    (gl,v)
  end

fun hhs_record (tac,stac) g =
  total_time record_time (hhs_record_aux (tac,stac)) g

(* --------------------------------------------------------------------------
   Replaying a proof
   -------------------------------------------------------------------------- *)

fun hhs_prerecord_aux thmname qtac goal = 
  let
    val success_flag = ref NONE
    val cthy = current_theory ()
    val final_stac_ref = ref ""
    fun mk_final_tac qtac = 
      let
        val _ = final_stac_ref := ""
        val s2 = total_time number_time number_stac qtac
        val ostac = hhs_lex s2
        val l2 = total_time extract_time hhs_extract s2
        val _  = debug_proof ("Original tactic number: " ^ int_to_string (length l2))
        val _  = n_tactic_parse_glob := (!n_tactic_parse_glob) + length l2;
        val l3 = map (fn x => (x, drop_numbering x)) l2
        fun mk_reps (x,y) =
          ["( hhsPrerecord.hhs_record","("] @ y @ 
          [",", mlquote (String.concatWith " " y),")",")"]
        val l5 = map (fn (x,y) => (x, mk_reps (x,y))) l3
        val ostac0 = fold_left replace_at l5 ostac
        val ostac1 = drop_numbering ostac0
        val final_stac = String.concatWith " " ostac1
        val _ = final_stac_ref := final_stac
        val final_tac = 
          total_time exec_time hhsExec.tactic_of_sml final_stac         
      in
        (final_stac, final_tac)
      end
      handle _ => parse_err thmname qtac (!final_stac_ref)
    val (final_stac, final_tac)  = 
      total_time hide_time (hhsRedirect.hide hidden_file
       (total_time mkfinal_time mk_final_tac)) qtac
  in
    print (int_to_string (!n_tactic_parse_glob) ^ "\n");
    incr n_parse_glob;
    (
    let
      val (gl,v) = 
      total_time replay_time (hhsTimeout.timeOut 10.0 final_tac) goal
    in
      if gl = []
        then (
             success_flag := SOME (gl,v);
             n_replay_glob := (!n_replay_glob + 1)
             )
      else replay_msg "opened goals" thmname qtac final_stac         
    end
    handle 
        TacTimeOut => replay_msg "timed out or other" thmname qtac final_stac
      | _          => replay_msg "other error" thmname qtac final_stac
    );
    (* save_hht cthy thmname goal; *)
    case (!success_flag) of 
      SOME x => x
    | NONE => raise ERR "" ""
  end

fun hhs_prerecord thmname qtac goal = 
  (
  debug_proof "";
  debug_proof thmname; 
  debug_search thmname;
  debug thmname;
  (tacticToe.eval_tactictoe goal handle _ => debug ("Error: eval_tactictoe"))
  ;
  hhs_prerecord_aux thmname qtac goal
  )
  
end (* struct *)
