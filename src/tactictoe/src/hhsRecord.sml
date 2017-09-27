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
hhsTimeout hhsData tacticToe hhsPredict hhsExec hhsMetis hhsLearn

val ERR = mk_HOL_ERR "hhsRecord"

val goalstep_glob = ref []
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
   Recording in interactive mode
   -------------------------------------------------------------------------- *)

fun set_irecord () = 
  (
  (* recording *)
  hhs_norecord_flag := false;
  hhs_eval_flag := false;
  hhs_internalthm_flag := false;
  hhs_norecprove_flag := false;
  hhs_nolet_flag := false;
  hhs_goalstep_flag := false;
  (* learning *)
  hhs_noslowlbl_flag := false;
  hhs_ortho_flag := false;
  hhs_ortho_number := 20;
  hhs_ortho_metis := false;
  hhsSearch.hhs_selflearn_flag := false;
  hhs_succrate_flag := false;
  (* export *)
  hhs_thmortho_flag := false
  )

fun set_erecord () =
  (
  (* recording *)
  hhs_norecord_flag := false;
  hhs_eval_flag := true;
  hhs_internalthm_flag := true;
  hhs_norecprove_flag := true;
  hhs_nolet_flag := true;
  hhs_goalstep_flag := false;
  (* learning *)
  hhs_noslowlbl_flag := false;
  hhs_ortho_flag := true;
  hhs_ortho_number := 20;
  hhs_ortho_metis := true;
  hhsSearch.hhs_selflearn_flag := false;
  hhs_succrate_flag := false;
  (* export *)
  hhs_thmortho_flag := true
  )

(* --------------------------------------------------------------------------
   Replaying a tactic.
   -------------------------------------------------------------------------- *)

fun tactic_err msg stac g = 
  (tactic_msg msg stac g; raise ERR "record_tactic" "")

fun record_tactic_aux (tac,stac) g =
  let
    val ((gl,v),t) = add_time (timeOut 2.0 tac) g 
      handle TacTimeOut => tactic_err "timed out" stac g
            | x         => raise x
  in
    tactic_time := (!tactic_time) + t;
    n_tactic_replay_glob := (!n_tactic_replay_glob) + 1;
    total_time save_time save_lbl (stac,t,g,gl);
    goalstep_glob := (stac,g,gl,v) :: !goalstep_glob;
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
    val (final_stac, final_tac)  =   
      total_time hide_time (hide_out (total_time mkfinal_time mk_alttac)) qtac
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

fun tactictoe_prove proved (_,g,gl,v) =
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

fun save_goalstep_aux proved l =
  let
    fun is_provable proved (_,g,gl,v) = all (fn x => dmem x (!proved)) gl
    val (l0,l1) = List.partition (is_provable proved) l
  in 
    if null l0 then () else
    (
    ignore (mapfilter (tactictoe_prove proved) l0);
    save_goalstep_aux proved l1
    )
  end
  
fun save_goalstep g l =
  if !hhs_goalstep_flag then
    let val proved = ref (dempty strict_goal_compare) in
      save_goalstep_aux proved l;
      if dmem g (!proved) then () else debug "Warning: add_goalstep"
    end
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
  handle e => 
    if !hhs_internalthm_flag 
    then save_tactictoe_thm thm 
    else raise e

fun fetch_thm_aux s reps =
  let val file = hhs_code_dir ^ "/" ^ current_theory () ^ "_fetch_thm" in
    if is_thm s
    then hide_out string_of_sml ("hhsRecord.name_of_thm " ^ s) handle _ => s 
    else (if reps = "" then (debug_record ("fetch: " ^ s); s) else reps)
  end
  
val fetch = total_time fetch_thm_time fetch_thm_aux

(*----------------------------------------------------------------------------
  Tactical proofs hooks
  ----------------------------------------------------------------------------*)

val start_stacset = ref (dempty String.compare)

fun create_stacset () =
  let val l = map (#1 o fst) (dlist (!hhs_stacfea)) in 
    dnew String.compare (map (fn x => (x,())) l) 
  end
  
val start_tokenset = ref (dempty String.compare)

fun create_tokenset () =
  let 
    val l = List.concat (map (hhs_lex o #1 o fst) (dlist (!hhs_stacfea)))
  in 
    dnew String.compare (map (fn x => (x,())) l) 
  end  

fun start_record name goal =
  (
  if !hhs_eval_flag then init_tactictoe () else ();
  debug_proof ("\n" ^ name);
  debug_search ("\n" ^ name);
  debug ("\n" ^ name);
  start_stacset := create_stacset ();
  if !hhs_after_flag
  then start_tokenset := create_tokenset ()
  else ()
  ;
  (* recording goal steps *)
  goalstep_glob := [];
  (* evaluation *)
  if !hhs_after_flag
  then ()
  else (eval_tactictoe name goal handle _ => debug "Error: eval_tactictoe")
  )

fun filter_stacfea f dict =
  (
  debug (int_to_string (dlength dict));
  init_stacfea_ddict [];
  app update_stacfea_ddict (filter f (dlist dict));
  debug (int_to_string (dlength (!hhs_stacfea)))
  )

val thm_cache = ref (dempty String.compare)
fun is_thm_cache x = 
  dfind x (!thm_cache) handle _ =>
  let val b = is_thm x in
    thm_cache := dadd x b (!thm_cache);
    b
  end
  
val string_cache = ref (dempty String.compare)
fun is_string_cache x = 
  dfind x (!string_cache) handle _ =>
  let val b = is_string x in
    string_cache := dadd x b (!string_cache);
    b
  end
  
val tactic_cache = ref (dempty String.compare)
fun is_tactic_cache x = 
  dfind x (!tactic_cache) handle _ =>
  let val b = is_tactic x in
    tactic_cache := dadd x b (!tactic_cache);
    b
  end    

val mtoken_dict = ref (dempty String.compare)
val mtactic_dict = ref (dempty String.compare)
  
fun end_record name g =
  let 
    val _ = debug "End record"
    val _ = thm_cache := dempty String.compare
    val _ = string_cache := dempty String.compare
    val _ = tactic_cache := dempty String.compare
    val _ = mtoken_dict := dempty String.compare
    val _ = mtactic_dict := dempty String.compare
    val stacl = map #1 (!goalstep_glob)
    val goall = map #2 (!goalstep_glob)
    fun is_true _ = true
    
    fun etest_wrap etest itest fea =
      let 
        fun itest_wrap itest x = 
          if itest x 
          then true 
          else (mtoken_dict := dadd x () (!mtoken_dict); false)
        val stac = ((#1 o fst) fea)
        val l = hhs_lex stac 
      in
        if etest fea andalso all (itest_wrap itest) l
        then true
        else (mtactic_dict := dadd stac () (!mtactic_dict); false)  
      end
     
    fun f1 ((stac,_,x,_),_) = mem stac stacl andalso mem x goall
    val ef1 = etest_wrap f1 is_true
    fun f2 ((stac,_,_,_),_) = dmem stac (!start_stacset)
    val ef2 = etest_wrap f2 is_true
    fun f3 x = dmem x (!start_tokenset)
    val ef3 = etest_wrap is_true f3
    fun f6 x = dmem x (!start_tokenset) orelse is_tactic_cache x
    val ef6 = etest_wrap is_true f6
    fun f7 x = dmem x (!start_tokenset) orelse 
               is_thm_cache x orelse is_string_cache x
    val ef7 = etest_wrap is_true f7       
    fun f8 x = 
      dmem x (!start_tokenset) orelse 
      is_thm_cache x orelse is_string_cache x orelse is_tactic_cache x
    val ef8 = etest_wrap is_true f8
    fun f9 x = 
      (
      dmem x (!start_tokenset) orelse 
      is_thm_cache x orelse 
      (is_string_cache x andalso can (split_string "(*") x)
      )
    val ef9 = etest_wrap is_true f9
    fun f10 x = 
      (
      dmem x (!start_tokenset) orelse 
      is_thm_cache x orelse 
        (
        is_string_cache x andalso 
        not (can (split_string "(*") x)
        )
      )
    val ef10 = etest_wrap is_true f10
    
    val mem_hhs_stacfea = !hhs_stacfea
    val dict = mem_hhs_stacfea
    val mem_hhs_cthyfea = !hhs_cthyfea
    val mem_hhs_ddict = !hhs_ddict
    val mem_hhs_ndict = !hhs_ndict
  in
    if !hhs_aftersmall_flag  then filter_stacfea ef1 dict else ();
    if !hhs_aftertac_flag    then filter_stacfea ef2 dict else ();
    if !hhs_aftertoken_flag  then filter_stacfea ef3 dict else ();
    if !hhs_aftertactic_flag then filter_stacfea ef6 dict else ();
    if !hhs_afterall_flag    then filter_stacfea ef7 dict else ();
    if !hhs_afterall2_flag   then filter_stacfea ef8 dict else ();
    if !hhs_afterthm2_flag   then filter_stacfea ef9 dict else ();
    if !hhs_afterthmthm_flag then filter_stacfea ef10 dict else ();
    
    if !hhs_after_flag
    then (eval_tactictoe name g handle _ => debug "Error: eval_tactictoe")
    else ()
    ;
    if !hhs_after_flag
      then 
        (
        hhs_stacfea := mem_hhs_stacfea;
        hhs_cthyfea := mem_hhs_cthyfea;
        hhs_ddict := mem_hhs_ddict;
        hhs_ndict := mem_hhs_ndict;
        debug ("mtactic_dict " ^ int_to_string (dlength (!mtactic_dict)));
        app debug (map fst (dlist (!mtactic_dict)));
        debug ("mtoken_dict " ^ int_to_string (dlength (!mtoken_dict)));
        app debug (map fst (dlist (!mtoken_dict)))
        )
      else ()
    ;
    if all (fn x => dmem x (!start_stacset)) stacl 
    then debug_proof "Covered"
    else debug_proof "Non-covered"
    ;
    (save_goalstep g (!goalstep_glob) handle _ => debug "Error: save_goalstep")
  end

fun try_record_proof name lflag tac1 tac2 g =
  let 
    val _  = set_erecord () (* to be removed *)
    val b1 = !hhs_norecord_flag
    val b2 = 
      (!hhs_norecprove_flag andalso String.isPrefix "tactictoe_prove_" name)
    val b3 = (!hhs_nolet_flag andalso lflag)           
    val (r,t) =
      if b1 orelse b2 orelse b3
      then add_time tac2 g
      else
        (
        let        
           val _ = start_record name g
           val rt = add_time tac1 g
           val _ = end_record name g
         in 
           rt
         end
        handle _ => (debug "Error: try_record_proof"; add_time tac2 g)
        )
  in    
    debug_proof ("Recording proof: " ^ Real.toString t);
    r
  end

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
