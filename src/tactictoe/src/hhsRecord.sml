(* =========================================================================  *)
(* FILE          : hhsPrererecord.sml                                         *)
(* DESCRIPTION   : Record tactics and their given goals (or their features)   *)
(* machine learning programs                                                  *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsRecord :> hhsRecord =
struct

open HolKernel boolLib hhsTools hhsLexer hhsData hhsNumber hhsExtract hhsUnfold 
hhsTimeout hhsData tacticToe hhsPredict hhsExec hhsMetis

val ERR = mk_HOL_ERR "hhsRecord"

val prev_proof = ref []
val prev_topgoal = ref NONE
val tactictoe_step_counter = ref 0
val tactictoe_thm_counter = ref 0

(*----------------------------------------------------------------------------
 * Error messages and profiling
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
  prev_proof := [];
  prev_topgoal := NONE;
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
    g "    Feature" (!feature_time)
  end

(* --------------------------------------------------------------------------
   Replaying a tactic.
   -------------------------------------------------------------------------- *)

val stacset = ref (dempty String.compare)
val newstac_flag = ref false

fun update_stacset () =
  let val l = map (#1 o fst) (dlist (!hhs_stacfea)) in 
    stacset := dnew String.compare (map (fn x => (x,())) l) 
  end
  
fun tactic_err msg stac g = 
  (tactic_msg msg stac g; raise ERR "record_tactic" "")

fun record_tactic_aux (tac,stac) g =
  let
    val ((gl,v),t) = add_time (timeOut 2.0 tac) g 
      handle TacTimeOut => tactic_err "timed out" stac g
            | x         => raise x
  in
    if not (!newstac_flag) 
    then newstac_flag := dmem stac (!stacset)
    else ()
    ;
    tactic_time := (!tactic_time) + t;
    n_tactic_replay_glob := (!n_tactic_replay_glob) + 1;
    total_time save_time save_lbl (stac,t,g,gl);
    prev_proof := (g,gl,v) :: !prev_proof;
    (gl,v)
  end

fun record_tactic (tac,stac) g =
  total_time record_time (record_tactic_aux (tac,stac)) g

(* --------------------------------------------------------------------------
   Replaying a proof
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
        val ostac = hhs_lex s2
        val l2 = total_time extract_time hhs_extract s2
        val _  = debug_proof ("Org tac number: " ^ int_to_string (length l2))
        val _  = n_tactic_parse_glob := (!n_tactic_parse_glob) + length l2;
        val l3 = map (fn x => (x, drop_numbering x)) l2
        fun mk_reps (x,y) =
          ["( hhsRecord.record_tactic","("] @ y @ 
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
    val hidden_file = hhs_code_dir ^ "/hidden"
    val (final_stac, final_tac)  =   
      total_time hide_time (hhsRedirect.hide hidden_file
       (total_time mkfinal_time mk_alttac)) qtac
  in
    print (int_to_string (!n_tactic_parse_glob) ^ "\n");
    incr n_parse_glob;
    (
    let
      val (gl,v) = 
      total_time replay_time (hhsTimeout.timeOut 20.0 final_tac) goal
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
    (* save_hht cthy thmname goal; *)
    case (!success_flag) of 
      SOME x => x
    | NONE   => raise ERR "" ""
  end

(* --------------------------------------------------------------------------
   Recording intermediate goals as theorems in the database
   -------------------------------------------------------------------------- *)

fun save_tactictoe_step thm =
  let 
    val name = "tactictoe_step_" ^ int_to_string (!tactictoe_step_counter)
  in
    if uptodate_thm thm 
    then (save_thm (name,thm); incr tactictoe_step_counter)
    else ()
  end

fun tactictoe_prove proved (g,gl,v) =
  let
    val thml = map (fn x => dfind x (!proved)) gl
    val thm = v thml
    fun test x = goal_compare (dest_thm x, dest_thm thm) = EQUAL
    val thyl = current_theory () :: ancestry (current_theory ())
  in
    proved := dadd g thm (!proved);
    if null (DB.matchp test thyl)
    then ()
    else save_tactictoe_step thm
  end

fun add_prev_proof_aux proved l =
  let
    fun is_provable proved (g,gl,v) = all (fn x => dmem x (!proved)) gl
    val (l0,l1) = List.partition (is_provable proved) l
  in 
    if null l0 then () else
    (
    ignore (mapfilter (tactictoe_prove proved) l0);
    add_prev_proof_aux proved l1
    )
  end
  
fun add_prev_proof () =
  if !hhs_recproof_flag andalso isSome (!prev_topgoal)
  then
    (
    let val proved = ref (dempty strict_goal_compare) in
      add_prev_proof_aux proved (!prev_proof);
      if dmem (valOf (!prev_topgoal)) (!proved) 
        then ()
        else debug "Warning: prev_proof";
      prev_proof := [];
      prev_topgoal := NONE
    end
    )
  else ()

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

fun depid_of_thm thm = (Dep.depid_of o Tag.dep_of o Thm.tag) thm

fun name_of_thm thm =
  let 
    val (thy,n) = depid_of_thm thm
    val thml = DB.thms thy
    val thmdict = dnew goal_compare (map (fn (a,b) => (dest_thm b,a)) thml)
    val name = dfind (dest_thm thm) thmdict
  in
    String.concatWith " " ["(","DB.fetch",mlquote thy,mlquote name,")"]
  end
  handle _ => save_tactictoe_thm thm 

fun fetch_thm_aux s reps =
  let val file = hhs_code_dir ^ "/fetch_thm" in
    hhsRedirect.hide file string_of_sml ("hhsRecord.name_of_thm " ^ s)
    handle _ => (if reps = "" then (debug_record ("fetch: " ^ s); s) else reps)
  end
  
val fetch = total_time fetch_thm_time fetch_thm_aux

(*----------------------------------------------------------------------------
  Tactical proofs hooks
  ----------------------------------------------------------------------------*)

fun start_record name goal =
  (
  debug_proof ("\n" ^ name);
  debug_search ("\n" ^ name);
  debug ("\n" ^ name);
  prev_topgoal := SOME goal;
  newstac_flag := false;
  (eval_tactictoe goal handle _ => debug "Error: eval_tactictoe");
  update_stacset ()
  )

fun end_record () =
  (
  if !newstac_flag then debug_proof "Non-covered" else debug_proof "Covered";
  (add_prev_proof () handle _ => debug "Error: add_prev_proof")
  )

val hhs_record_flag = ref true

fun try_record_proof name tac1 tac2 g =
  (
  start_record name g;
  let 
    fun try_tac g =
      if !hhs_record_flag 
      then (tac1 g handle _ => (debug "Error: try_record_proof"; tac2 g))
      else tac2 g
    val (r,t) = add_time try_tac g
  in
    debug_proof ("Recording proof: " ^ Real.toString t);
    end_record (); 
    r
  end
  )

(*----------------------------------------------------------------------------
  Theory hooks
  ----------------------------------------------------------------------------*)

fun clean_subdirl cthy dir subdirl =
  let 
    fun clean_sub x = 
      (mkDir_err (dir ^ "/" ^ x); erase_file (dir ^ "/" ^ x ^ "/" ^ cthy))
  in
    mkDir_err dir;
    app clean_sub subdirl 
  end 

fun clean_dir cthy dir = (mkDir_err dir; erase_file (dir ^ "/" ^ cthy))

fun start_thy cthy =
  (
  clean_feadata ();
  reset_profiling ();
  (* Proof search *)
  clean_subdirl cthy hhs_search_dir ["debug","search","proof"];
  (* Features storage *)
  clean_dir cthy hhs_feature_dir;
  clean_dir cthy hhs_mdict_dir;
  (* Tactic scripts recording *)
  clean_subdirl cthy hhs_record_dir ["parse","replay","record"] 
  )

fun end_thy cthy = 
  (
  debug_t "export_feavl" (export_feavl cthy) (!hhs_cthyfea);
  debug_t "export_mdict" export_mdict cthy;
  out_record_summary cthy;
  debug_proof ("Bad stac: " ^ (int_to_string (length (!hhs_badstacl))))
  )

end (* struct *)
