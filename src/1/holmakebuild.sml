structure holmakebuild =
struct

local

open Feedback

val holmake_tag = "tactic-failed"

(* Access Globals refs at runtime (not captured at load time)
   because the refs are set by hol.ML after holmakebuild.uo is loaded. *)
val dumpheap = Globals.holmake_dumpheap_flag
val g_flag = Globals.holmake_g_flag
val allow_cheat = Globals.holmake_allow_cheat
val tactic_timeout_secs = Globals.holmake_tactic_timeout
val current_thm_name = Globals.holmake_current_thm

(* Tactic timeout and heap save operations.
   PolyRuntime provides thread-based timeout on Poly/ML and no-op stubs on mosml.
   See src/portableML/{poly,mosml}/concurrent/PolyRuntime.sml *)
exception TacticTimeout = PolyRuntime.TacticTimeout
val tactic_timeout = PolyRuntime.tactic_timeout

(* Wrapper exception to prevent double-catching by nested HOL_ERR handlers.
   Carries the goalstate for diagnostics and the original exception. *)
exception ProofFailed of goalFrag.goalstate option * exn

(* Checkpoint directory: matches hol_state_at layout
   .hol/cursor_checkpoints/<thm>_{context|end_of_proof}.save *)
fun checkpoint_dir () = let
  val hol_dir = OS.Path.concat (OS.FileSys.getDir (), ".hol")
  val dir = OS.Path.concat (hol_dir, "cursor_checkpoints")
in
  if OS.FileSys.access (dir, []) then dir
  else ((OS.FileSys.mkDir hol_dir) handle OS.SysErr _ => ();
        OS.FileSys.mkDir dir;
        dir)
end

fun context_checkpoint_path name =
  OS.Path.concat (checkpoint_dir (), name ^ "_context.save")
fun end_of_proof_checkpoint_path name =
  OS.Path.concat (checkpoint_dir (), name ^ "_end_of_proof.save")

fun delete_checkpoint path =
  if OS.FileSys.access (path, []) then
    (OS.FileSys.remove path; ())
  else ()

(* Eager cache cleaning: delete stale checkpoints before rebuild *)
fun clean_checkpoints name =
  (delete_checkpoint (context_checkpoint_path name);
   delete_checkpoint (end_of_proof_checkpoint_path name))

(* Save context checkpoint: theory state after store_thm.
   Matches hol_state_at TheoremCheckpoint.context_path. *)
fun save_context_checkpoint name =
  if !dumpheap then let
    val path = context_checkpoint_path name
    val _ = delete_checkpoint path
  in
    PolyRuntime.save_heap path;
    HOL_MESG ("Saved context checkpoint: " ^ name)
  end
  else ()

(* Save end_of_proof checkpoint: proof replay state after all tactics.
   Matches hol_state_at TheoremCheckpoint.end_of_proof_path.
   Contains goalfrag proof history for hol4-mcp navigation. *)
fun save_end_of_proof_checkpoint name =
  if !dumpheap andalso !g_flag then let
    val path = end_of_proof_checkpoint_path name
    val _ = delete_checkpoint path
  in
    PolyRuntime.save_heap path;
    HOL_MESG ("Saved proof checkpoint: " ^ name)
  end
  else ()

(* Handle a proof failure: print goalstate, then CHEAT or re-raise. *)
fun handle_proof_failure name g (gs_opt, e) =
  (if !g_flag then
     case gs_opt of
       SOME gs =>
         HOL_MESG ("*** Proof of \"" ^ name ^ "\" failed at goal:\n" ^
                   HOLPP.pp_to_string 10000 (goalFrag.pp_goalstate) gs)
     | NONE => ();
   if !allow_cheat then
     (HOL_MESG ("*** Proof of \n  " ^ Parse.term_to_string (#2 g) ^
                "\n*** failed (used CHEAT).\n");
      HOL_MESG (exn_to_string e);
      Thm.mk_oracle_thm holmake_tag g)
   else raise e)

(* Parse a tactic string to a tac_expr.  Uses the full HOL source parser
   so term quotations and infix operators are handled correctly. *)
fun parseTacticBlockFromString s = let
  val fed = ref false
  fun read _ = if !fed then "" else (fed := true; s)
  val result = HOLSourceParser.parseSML "" read
    (fn _ => fn _ => fn _ => ())
    HOLSourceParser.initialScope
  val dec = #parseDec result ()
in
  case dec of
    SOME (HOLSourceAST.DecExp e) => TacticParse.parseTacticBlock e
  | NONE => TacticParse.parseTacticBlock (HOLSourceAST.ExpEmpty 0)
  | _ => raise Fail ("parseTacticBlockFromString: expected expression")
end

(* Execute an SML string in the current namespace.
   Used for fragment-stepped proof execution where each fragment
   becomes an SML command like "proofManagerLib.ef(goalFrag.expand(tac))". *)
val eval_sml_string = PolyRuntime.eval_sml_string

(* Execute a single fragment step via proofManagerLib.ef.
   Returns true on success, false on failure. *)
fun step_frag (frag_type, frag_text) =
  case frag_type of
    "open" => let
      val ftac =
        if String.isPrefix "open_nth_goal " frag_text then
          goalFrag.open_nth_goal
            (Option.valOf (Int.fromString
              (String.substring (frag_text, 15, String.size frag_text - 15))))
        else if String.isPrefix "open_split_lt " frag_text then
          goalFrag.open_split_lt
            (Option.valOf (Int.fromString
              (String.substring (frag_text, 14, String.size frag_text - 14))))
        else case frag_text of
          "open_paren" => goalFrag.open_paren
        | "open_then1" => goalFrag.open_then1
        | "open_first" => goalFrag.open_first
        | "open_repeat" => goalFrag.open_repeat
        | "open_tacs_to_lt" => goalFrag.open_tacs_to_lt
        | "open_null_ok" => goalFrag.open_null_ok
        | "open_last_goal" => goalFrag.open_last_goal
        | "open_head_goal" => goalFrag.open_head_goal
        | "open_select_lt" => goalFrag.open_select_lt
        | "open_first_lt" => goalFrag.open_first_lt
        | _ => raise Fail ("unknown open frag: " ^ frag_text)
    in (proofManagerLib.ef ftac; true) handle HOL_ERR _ => false end
  | "mid" => let
      val ftac = case frag_text of
        "next_first" => goalFrag.next_first
      | "next_tacs_to_lt" => goalFrag.next_tacs_to_lt
      | "next_split_lt" => goalFrag.next_split_lt
      | "next_select_lt" => goalFrag.next_select_lt
      | _ => raise Fail ("unknown mid frag: " ^ frag_text)
    in (proofManagerLib.ef ftac; true) handle HOL_ERR _ => false end
  | "close" => let
      val ftac = case frag_text of
        "close_paren" => goalFrag.close_paren
      | "close_first" => goalFrag.close_first
      | "close_repeat" => goalFrag.close_repeat
      | "close_first_lt" => goalFrag.close_first_lt
      | _ => raise Fail ("unknown close frag: " ^ frag_text)
    in (proofManagerLib.ef ftac; true) handle HOL_ERR _ => false end
  | "expand" =>
      let val cmd = "proofManagerLib.ef(goalFrag.expand(" ^ frag_text ^ "))"
      in (eval_sml_string cmd; true) handle HOL_ERR _ => false end
  | "expand_list" =>
      let val cmd = "proofManagerLib.ef(goalFrag.expand_list(" ^ frag_text ^ "))"
      in (eval_sml_string cmd; true) handle HOL_ERR _ => false end
  | _ => raise Fail ("unknown frag type: " ^ frag_type)

(* Look up tactic text stored by HOLSourceExpand for a given theorem name.
   Returns (source_text, has_proof_attrs). *)
fun lookup_tactic_text name =
  case List.find (fn (n, _, _) => n = name) (!HOLSourceExpand.holmake_tactic_text) of
    SOME (_, src, has_attrs) => SOME (src, has_attrs)
  | NONE => NONE

(* Recover from proof state corruption after timeout/failure.
   Drops all proof state and attempts to read current goalstate. *)
fun recover_goalstate () =
  (case proofManagerLib.status () of
     Manager.PRFS (Manager.PF (Manager.GOALFRAG h, _) :: _) =>
       SOME (History.project (fn gs => gs) h)
   | _ => NONE)
  handle _ => NONE

fun drop_all_safe () = ((proofManagerLib.drop_all (); ()) handle _ => ())

(* Fragment-stepped prover: applies each tactic fragment as a separate
   proofManagerLib.ef() step, creating per-fragment history entries.
   This produces navigable checkpoints for hol4-mcp.
   Used when both -g and --dumpheap are active. *)
fun fragment_stepped_prover (g, tac: Abbrev.tactic) = let
  val name = !current_thm_name
  val _ = current_thm_name := ""
  val timeout = !tactic_timeout_secs
  val _ = if name <> "" then clean_checkpoints name else ()
  fun do_proof () =
    case (if name = "" then NONE else lookup_tactic_text name) of
      NONE =>
        (* No tactic text — fall back to one-shot goalfrag *)
        (proofManagerLib.set_goalfrag g;
         tactic_timeout timeout (fn () => proofManagerLib.expand tac) ();
         let val thm = proofManagerLib.top_thm () in
           save_end_of_proof_checkpoint name;
           proofManagerLib.drop_all ();
           save_context_checkpoint name;
           thm
         end)
    | SOME (source_text, has_proof_attrs) =>
        if has_proof_attrs orelse source_text = "" then
          (* Proof attrs present or no source text — fall back to one-shot.
             Proof[exclude_simps ...] wraps the tactic with
             with_simpset_updates, which source text alone misses. *)
          (proofManagerLib.set_goalfrag g;
           tactic_timeout timeout (fn () => proofManagerLib.expand tac) ();
           let val thm = proofManagerLib.top_thm () in
             save_end_of_proof_checkpoint name;
             proofManagerLib.drop_all ();
             save_context_checkpoint name;
             thm
           end)
        else let
          val _ = proofManagerLib.set_goalfrag g
          val tree = parseTacticBlockFromString source_text
          val steps = TacticStep.step_plan source_text tree
          fun run_steps [] =
                let val thm = proofManagerLib.top_thm () in
                  save_end_of_proof_checkpoint name;
                  proofManagerLib.drop_all ();
                  save_context_checkpoint name;
                  thm
                end
            | run_steps ((_, ftype, ftext) :: rest) =
                let val ok = (tactic_timeout timeout step_frag (ftype, ftext);
                              true)
                             handle TacticTimeout t =>
                               raise ProofFailed (NONE, mk_HOL_ERR "holmakebuild"
                                 "fragment_stepped_prover"
                                 ("tactic timeout (" ^
                                  Real.fmt (StringCvt.FIX (SOME 1)) t ^
                                  "s): " ^ ftype ^ " " ^
                                  String.substring (ftext, 0,
                                    Int.min (String.size ftext, 60))))
                             | HOL_ERR _ => false
                in if ok then run_steps rest
                   else raise ProofFailed (NONE, mk_HOL_ERR "holmakebuild"
                     "fragment_stepped_prover"
                     ("fragment failed: " ^ ftype ^ " " ^
                      String.substring (ftext, 0,
                        Int.min (String.size ftext, 60))))
                end
        in
          run_steps steps
          handle e as HOL_ERR _ => raise ProofFailed (NONE, e)
               | TacticTimeout t => raise ProofFailed (NONE,
                   mk_HOL_ERR "holmakebuild" "fragment_stepped_prover"
                     ("tactic timeout (" ^
                      Real.fmt (StringCvt.FIX (SOME 1)) t ^ "s)"))
        end
in
  do_proof ()
  handle ProofFailed (gs_opt, e) =>
    let val gs_opt' = case gs_opt of
                        SOME _ => gs_opt
                      | NONE => recover_goalstate ()
    in
      drop_all_safe ();
      handle_proof_failure name g (gs_opt', e)
    end
  | TacticTimeout t =>
    let val e = mk_HOL_ERR "holmakebuild" "fragment_stepped_prover"
                  ("tactic timeout (" ^
                   Real.fmt (StringCvt.FIX (SOME 1)) t ^ "s)")
    in
      drop_all_safe ();
      handle_proof_failure name g (recover_goalstate (), e)
    end
end

(* Goalfrag-based prover with VALID, failure diagnostics, and checkpoints.
   Used when -g is active without --dumpheap. *)
fun goalfrag_prover (g, tac: Abbrev.tactic) = let
  val name = !current_thm_name
  val _ = current_thm_name := ""
  val timeout = !tactic_timeout_secs
  val _ = if name <> "" then clean_checkpoints name else ()
in
  (let
    val _ = proofManagerLib.set_goalfrag g
    val _ = tactic_timeout timeout (fn () => proofManagerLib.expand tac) ()
    val thm = proofManagerLib.top_thm ()
  in
    save_end_of_proof_checkpoint name;
    proofManagerLib.drop_all ();
    save_context_checkpoint name;
    thm
  end
  handle e as HOL_ERR _ => raise ProofFailed (NONE, e)
       | TacticTimeout t => raise ProofFailed (NONE,
           mk_HOL_ERR "holmakebuild" "goalfrag_prover"
             ("tactic timeout (" ^ Real.fmt (StringCvt.FIX (SOME 1)) t ^ "s)")))
  handle ProofFailed (gs_opt, e) =>
    let val gs_opt' = case gs_opt of
                        SOME _ => gs_opt
                      | NONE => recover_goalstate ()
    in
      drop_all_safe ();
      handle_proof_failure name g (gs_opt', e)
    end
end

(* basic_prover: original behavior with optional checkpointing *)
fun basic_prover (g, tac: Abbrev.tactic) = let
  val name = !current_thm_name
  val _ = current_thm_name := ""
  val _ = if name <> "" then clean_checkpoints name else ()
  val thm = Tactical.TAC_PROOF (g, tac)
in
  if name <> "" then save_context_checkpoint name else ();
  thm
end
  handle (e as HOL_ERR _) =>
    if !allow_cheat then
      (HOL_MESG ("*** Proof of \n  " ^ Parse.term_to_string (#2 g) ^
                 "\n*** failed (used CHEAT).\n");
       HOL_MESG (exn_to_string e);
       Thm.mk_oracle_thm holmake_tag g)
    else raise e

in

val () = if !g_flag andalso !dumpheap then
           Tactical.set_prover fragment_stepped_prover
         else if !g_flag then
           Tactical.set_prover goalfrag_prover
         else
           Tactical.set_prover basic_prover

end

end
