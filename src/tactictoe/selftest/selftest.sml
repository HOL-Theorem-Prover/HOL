open HolKernel boolLib tacticToe tttEval
open tttSetup tttUnfold tttSearch tttRecord
open testutils

val _ = print "\n"

fun check msg b =
  (tprint msg; if b then OK () else die "FAILED")

fun passok msg f =
  (tprint msg; f (); OK ())
  handle e => die ("FAILED: " ^ exnMessage e)

fun expect_holerr msg structname msgsub f =
  shouldfail
    {printarg = K msg, printresult = K "", testfn = f,
     checkexn = check_HOL_ERRexn
       (fn (st,_,m) => st = structname andalso String.isSubstring msgsub m)}
    ()

fun proves msg tm =
  (tprint msg;
   let val th = tactictoe tm in
     if aconv (concl th) tm then OK ()
     else die ("FAILED: conclusion mismatch: " ^
               term_to_string (concl th))
   end)
  handle e => die ("FAILED: " ^ exnMessage e)

fun ttt_closes msg tm =
  (tprint msg;
   let val (gl,_) = ttt ([],tm) in
     if null gl then OK ()
     else die ("FAILED: " ^ Int.toString (length gl) ^
               " subgoals remain")
   end)
  handle e => die ("FAILED: " ^ exnMessage e)

val relative_cache_dir = ".hol/relative-tactictoe-cache"
val expected_relative_cache_dir = OS.Path.mkAbsolute
  {path = relative_cache_dir, relativeTo = OS.FileSys.getDir ()}
val _ = set_tactictoe_cache_dir relative_cache_dir
val _ = check "relative cache root is normalized at configuration time"
  (tactictoe_dir_of () = expected_relative_cache_dir)

val cache_dir = HOLDIR ^ "/src/tactictoe/selftest/.hol/tactictoe-cache"
val _ = set_tactictoe_cache_dir cache_dir
val tacdata_file = tttManifest.current_tacdata_file
fun datafile () = tacdata_file "ConseqConv"

fun read_file file =
  let val ins = TextIO.openIn file in
    TextIO.inputAll ins before TextIO.closeIn ins
  end

val manifest_roundtrip_cache = cache_dir ^ "-manifest-roundtrip"
val manifest_roundtrip =
  let
    val prov = tttManifest.current_provenance ()
    val empty_entry : tttManifest.entry =
      {thy = "missing_script", data_hash = "failed", src_hash = "",
       anc_version = 0, anc_hash = "empty-ancestor-hash", recorded_at = ~1,
       failed = true, tacdata_version = #tacdata_version prov,
       tactictoe_version = #tactictoe_version prov}
    val valid_entry : tttManifest.entry =
      {thy = "present_script", data_hash = "failed", src_hash = "source-hash",
       anc_version = 0, anc_hash = "empty-ancestor-hash", recorded_at = ~1,
       failed = true, tacdata_version = #tacdata_version prov,
       tactictoe_version = #tactictoe_version prov}
    fun cleanup () = aiLib.run_cmd
      ("rm -rf " ^ aiLib.shell_quote manifest_roundtrip_cache)
    fun restore () = (set_tactictoe_cache_dir cache_dir; cleanup ())
    val result =
      ((cleanup ();
        set_tactictoe_cache_dir manifest_roundtrip_cache;
        tttManifest.write_manifest prov [empty_entry,valid_entry];
        case tttManifest.read_manifest () of
          NONE => false
        | SOME m =>
            length (#entries m) = 2 andalso
            List.exists (fn e => #thy e = "missing_script" andalso
              #src_hash e = "") (#entries m))
       handle e => (restore (); raise e))
  in
    result before restore ()
  end

val _ = check "manifest round-trips an empty source hash"
  manifest_roundtrip

val atomic_file = "ttt_writel_atomic_selftest"
val _ = passok "atomic write accepts a bare filename"
  (fn () =>
    (aiLib.writel_atomic atomic_file ["atomic"];
     if read_file atomic_file = "atomic\n" then ()
     else raise Fail "atomic-write content mismatch")
    before aiLib.remove_file atomic_file)

val redirect_file = "ttt_hide_in_file_selftest"
val _ = passok "output redirection accepts a bare filename"
  (fn () =>
    (if smlRedirect.hide_in_file redirect_file (fn x => x + 1) 1 = 2 andalso
        OS.FileSys.access (redirect_file, [])
     then () else raise Fail "bare redirection failed")
    before aiLib.remove_file redirect_file)

val _ = check "parallel workers inherit configured cache root"
  (String.isSubstring cache_dir (#reflect_globals (record_extspec ())))

val worker_includes =
  let
    val saved = !loadPath
    val marker = OS.FileSys.fullPath "."
  in
    (loadPath := marker :: saved;
     #self_dir (record_extspec ()))
    before loadPath := saved
  end

val _ = check "parallel workers inherit caller load paths"
  (String.isSubstring (OS.FileSys.fullPath ".") worker_includes)

val worker_settings =
  let
    val saved = (!record_prove_flag, !record_let_flag,
      !learn_abstract_term, !record_tactic_time, !record_proof_time)
  in
    (record_prove_flag := false;
     record_let_flag := true;
     learn_abstract_term := true;
     record_tactic_time := 3.25;
     record_proof_time := 4.5;
     #reflect_globals (record_extspec ()))
    before
      (record_prove_flag := #1 saved;
       record_let_flag := #2 saved;
       learn_abstract_term := #3 saved;
       record_tactic_time := #4 saved;
       record_proof_time := #5 saved)
  end

val _ = check "parallel workers inherit recording settings"
  (List.all (fn s => String.isSubstring s worker_settings)
    ["record_prove_flag := false", "record_let_flag := true",
     "learn_abstract_term := true", "record_tactic_time := 3.25",
     "record_proof_time := 4.5"])

fun example_spec self reflect : (unit,int,int) smlParallel.extspec =
  let val base = smlParallel.examplespec in
    { self_dir = #self_dir base,
      self = self,
      parallel_dir = #parallel_dir base,
      reflect_globals = reflect,
      function = #function base,
      write_param = #write_param base,
      read_param = #read_param base,
      write_arg = #write_arg base,
      read_arg = #read_arg base,
      write_result = #write_result base,
      read_result = #read_result base }
  end

val dead_worker_spec = example_spec "smlParallel.examplespec"
  "raise Fail \"worker startup selftest\""

val _ = check "parallel boss detects terminated worker"
  ((smlTimeout.timeout 10.0
      (fn () => ignore
        (smlParallel.parmap_queue_extern 2 dead_worker_spec () [1,2])) () ;
    false)
   handle e =>
     String.isSubstring "external worker" (exnMessage e) andalso
     String.isSubstring "startup" (exnMessage e))

val dead_job_self = String.concat
  ["(let val e = smlParallel.examplespec in ",
   "{self_dir = #self_dir e, self = #self e, ",
   "parallel_dir = #parallel_dir e, ",
   "reflect_globals = #reflect_globals e, ",
   "function = (fn () => fn (_ : int) => ",
   "raise Fail \"worker job selftest\"), ",
   "write_param = #write_param e, read_param = #read_param e, ",
   "write_arg = #write_arg e, read_arg = #read_arg e, ",
   "write_result = #write_result e, read_result = #read_result e} end)"]

val dead_job_spec = example_spec dead_job_self "()"

val _ = check "parallel boss detects worker termination during job"
  ((smlTimeout.timeout 10.0
      (fn () => ignore
        (smlParallel.parmap_queue_extern 2 dead_job_spec () [1,2])) () ;
    false)
   handle e =>
     String.isSubstring "external worker" (exnMessage e) andalso
     String.isSubstring "during job" (exnMessage e))

val cancelled_job_marker = cache_dir ^ "-cancelled-worker-finished"
val cancelled_job_self = String.concat
  ["(let val e = smlParallel.examplespec in ",
   "{self_dir = #self_dir e, self = #self e, ",
   "parallel_dir = #parallel_dir e, ",
   "reflect_globals = #reflect_globals e, ",
   "function = (fn () => fn (_ : int) => ",
   "(OS.Process.sleep (Time.fromSeconds 20); aiLib.writel ",
   Portable.mlquote cancelled_job_marker, " [\"finished\"]; 0)), ",
   "write_param = #write_param e, read_param = #read_param e, ",
   "write_arg = #write_arg e, read_arg = #read_arg e, ",
   "write_result = #write_result e, read_result = #read_result e} end)"]
val cancelled_job_spec = example_spec cancelled_job_self "()"

val _ = aiLib.remove_file cancelled_job_marker
val cancelled_parallel_call =
  ((smlTimeout.timeout 5.0
      (fn () => ignore (smlParallel.parmap_queue_extern 2
        cancelled_job_spec () [1,2])) () ;
    false)
   handle smlTimeout.FunctionTimeout => true | _ => false)
val _ = OS.Process.sleep (Time.fromReal 0.25)
val _ = check "interrupting parallel boss terminates external workers"
  (cancelled_parallel_call andalso
   not (OS.FileSys.access (cancelled_job_marker, [])))
val _ = aiLib.remove_file cancelled_job_marker

val _ = check "tacticToe public API type-checks"
  (let
     val _ : tactic = ttt
     val _ : term -> thm = tactictoe
     val _ : tnn -> tactic = ttt_tnn
     val _ : tnn -> term -> thm = tactictoe_tnn
     val _ : unit -> unit = clean_ttt_tacdata_cache
     val _ : real -> unit = set_timeout
     val _ : unit -> tactic = suggest
     val _ : tttSearch.searchtree option ref = searchtree_glob
     val _ : int option ref = suggest_depth
     val _ : string list ref = prioritize_stacl
   in true end)

val _ = check "TacticToe recording API type-checks"
  (let
     val _ : string -> unit = ttt_record_thy
     val _ : unit -> unit = ttt_record
     val _ : unit -> unit = ttt_clean_record
     val _ : unit -> unit = ttt_clean_savestate
     val _ : unit -> unit = ttt_record_savestate
     val _ : record_option list -> unit = ttt_record_opts
     val _ : record_config -> unit = ttt_record_cfg
     val _ : record_scope ->
       {stale : (string * reason) list, up_to_date : string list} =
       ttt_record_plan
     val _ : unit -> tttManifest.manifest option = tttManifest.read_manifest
   in true end)

val saved_search_time = !ttt_search_time
val saved_metis_radius = !ttt_metis_radius
val saved_presel_radius = !ttt_presel_radius
val saved_prioritize = !prioritize_stacl
val saved_hh_use = !hh_use
val saved_suggest_depth = !suggest_depth

val _ = check "set_timeout writes ttt_search_time"
  (set_timeout 7.5; Real.== (!ttt_search_time, 7.5))

val _ = check "set_timeout accepts zero"
  (set_timeout 0.0; Real.== (!ttt_search_time, 0.0))

val _ = check "integer parameters are mutable"
  (let
     val m0 = !ttt_metis_radius
     val p0 = !ttt_presel_radius
   in
     ttt_metis_radius := m0 + 1;
     ttt_presel_radius := p0 * 2;
     !ttt_metis_radius = m0 + 1 andalso
     !ttt_presel_radius = p0 * 2
   end)

val _ = check "miscellaneous tacticToe refs are mutable"
  (prioritize_stacl := [];
   hh_use := true;
   suggest_depth := SOME 4;
   null (!prioritize_stacl) andalso !hh_use andalso
   !suggest_depth = SOME 4)

val _ =
  (ttt_search_time := saved_search_time;
   ttt_metis_radius := saved_metis_radius;
   ttt_presel_radius := saved_presel_radius;
   prioritize_stacl := saved_prioritize;
   hh_use := saved_hh_use;
   suggest_depth := saved_suggest_depth)

val plan0 = ttt_record_plan (Theories ["ConseqConv"])
val covered0 = map fst (#stale plan0) @ #up_to_date plan0

val _ = check "record plan covers ConseqConv"
  (List.exists (fn thy => thy = "ConseqConv") covered0)

val _ = check "record plan has non-empty scope"
  (not (null covered0))

val _ = passok "read_manifest is callable before recording"
  (fn () => ignore (tttManifest.read_manifest ()))

val _ = check "sha1_string is deterministic"
  (let
     val h1 = aiLib.sha1_string "tactictoe\n"
     val h2 = aiLib.sha1_string "tactictoe\n"
     val h3 = aiLib.sha1_string "tactictoe changed\n"
   in
     h1 = h2 andalso h1 <> h3 andalso size h1 = 40
   end)

val _ = check "ancestor identity hash is deterministic"
  (let
     val h1 = tttManifest.ancestry_hash "ConseqConv"
     val h2 = tttManifest.ancestry_hash "ConseqConv"
   in h1 = h2 andalso size h1 = 40 end)

val _ = check "ancestor identity accepts indexed source hashes"
  (let
     val hashes = map (fn thy => (thy,tttManifest.source_hash thy))
       (tttManifest.ttt_ancestry "ConseqConv")
     val index = aiLib.dnew String.compare hashes
     val indexed = tttManifest.ancestry_hash_from
       (fn thy => aiLib.dfind thy index) "ConseqConv"
   in indexed = tttManifest.ancestry_hash "ConseqConv" end)

val _ = check "stale holderless lock is reclaimed"
  (let
     val lockdir = tttManifest.tacdata_dir () ^ "/.locks"
     val lock = lockdir ^ "/marker.lock"
     fun cleanup () = aiLib.run_cmd ("rm -rf " ^ aiLib.shell_quote lock)
     val result =
       ((cleanup ();
         app aiLib.mkDir_err [tttManifest.tacdata_dir (), lockdir];
         HOLFileSys.mkDir lock;
         OS.FileSys.setTime
           (lock, SOME (Time.- (Time.now (), Time.fromSeconds 10)));
         ttt_record_opts
           [Scope (Theories ["marker"]), Force true,
            MaxLockAge Time.zeroTime];
         not (OS.FileSys.access (lock, [])))
        handle e => (cleanup (); raise e))
   in
     result before cleanup ()
   end)

val _ = check "stale held lock is reclaimed under registry lock"
  (let
     val lockdir = tttManifest.tacdata_dir () ^ "/.locks"
     val lock = lockdir ^ "/marker.lock"
     fun cleanup () = aiLib.run_cmd ("rm -rf " ^ aiLib.shell_quote lock)
     val result =
       ((cleanup ();
         app aiLib.mkDir_err [tttManifest.tacdata_dir (), lockdir];
         HOLFileSys.mkDir lock;
         aiLib.writel (lock ^ "/holder") ["abandoned"];
         OS.FileSys.setTime
           (lock, SOME (Time.- (Time.now (), Time.fromSeconds 10)));
         ttt_record_opts
           [Scope (Theories ["marker"]), Force true,
            MaxLockAge Time.zeroTime];
         not (OS.FileSys.access (lock, [])))
        handle e => (cleanup (); raise e))
   in
     result before cleanup ()
   end)

val _ = passok "record ConseqConv tactic data"
  (fn () => ttt_record_opts [Scope (Theories ["ConseqConv"])])

val _ = check "ConseqConv tactic data exists"
  (mlTacticData.exists_tacdata_thy "ConseqConv" andalso
   OS.FileSys.access (datafile (), []))

val _ = check "ConseqConv tactic data is non-empty"
  (Position.toInt (OS.FileSys.fileSize (datafile ())) > 0)

val conseqconv_recording_script =
  tactictoe_dir_of () ^ "/log/scripts/ConseqConv"

val _ = check "one-theory tactic recording keeps the up-to-date fast path"
  (let
     val saved = (!record_flag, !record_savestate_flag,
       !export_thmdata_flag)
     fun restore () =
       (record_flag := #1 saved;
        record_savestate_flag := #2 saved;
        export_thmdata_flag := #3 saved)
     val result =
       ((record_flag := true;
         record_savestate_flag := false;
         export_thmdata_flag := false;
         aiLib.remove_file conseqconv_recording_script;
         ttt_record_thy "ConseqConv";
         not (OS.FileSys.access (conseqconv_recording_script, [])))
        handle e => (restore (); raise e))
   in
     result before restore ()
   end)

val _ = check "one-theory theorem-data export bypasses tactic freshness"
  (let
     val saved = (!record_flag, !record_savestate_flag,
       !export_thmdata_flag)
     val thmdata_dir = tactictoe_dir_of () ^ "/thmdata"
     fun restore () =
       (record_flag := #1 saved;
        record_savestate_flag := #2 saved;
        export_thmdata_flag := #3 saved;
        aiLib.clean_dir thmdata_dir)
     val result =
       ((aiLib.clean_dir thmdata_dir;
         record_flag := false;
         record_savestate_flag := false;
         export_thmdata_flag := true;
         ttt_record_thy "ConseqConv";
         List.exists (String.isPrefix "ConseqConv_")
           (aiLib.listDir thmdata_dir))
        handle e => (restore (); raise e))
   in
     result before restore ()
   end)

val _ = check "batch tactic-data resolution preserves per-theory results"
  (case tttManifest.tacdata_files_for_thys_in
      (tttManifest.read_manifest ()) ["ConseqConv","no_such_theory_for_ttt"] of
     [("ConseqConv",SOME file),("no_such_theory_for_ttt",NONE)] =>
       file = datafile ()
   | _ => false)

val _ = passok "record dry-run over ConseqConv"
  (fn () => ttt_record_opts
    [Scope (Theories ["ConseqConv"]), DryRun true])

val _ = passok "forced record dry-run over ConseqConv"
  (fn () => ttt_record_opts
    [Scope (Theories ["ConseqConv"]), Force true, DryRun true])

open metisTools ConseqConvTheory

val _ = set_timeout 10.0

val _ = proves "tactictoe proves T" T
val _ = proves "tactictoe proves not-F" ``~F``
val _ = proves "tactictoe proves T and T" ``T /\ T``
val _ = proves "tactictoe proves T or F" ``T \/ F``
val _ = proves "tactictoe proves all x. x = x" ``!x:bool. x = x``
val _ = proves "tactictoe proves all x. x implies x"
  ``!x:bool. x ==> x``

val _ = ttt_closes "ttt closes T" T
val _ = ttt_closes "ttt closes not-F" ``~F``
val _ = ttt_closes "ttt closes all x. x = x" ``!x:bool. x = x``

val _ = expect_holerr "tactictoe rejects non-bool terms"
  "tacticToe" "type bool expected"
  (fn () => ignore (tactictoe ``(1 + 1):num``))

val _ = expect_holerr "ttt rejects non-bool conclusions"
  "tacticToe" "type bool expected"
  (fn () => ignore (ttt ([], ``(1 + 1):num``)))

val _ = expect_holerr "ttt rejects non-bool assumptions"
  "tacticToe" "type bool expected"
  (fn () => ignore (ttt ([``(1 + 1):num``], T)))

val _ = set_timeout 2.0
val _ = searchtree_glob := NONE
val _ = (ttt ([],T); ()) handle _ => ()

val tree = !searchtree_glob
val _ = check "searchtree_glob is populated by ttt" (isSome tree)

val _ =
  case tree of
    NONE => die "FAILED: no search tree"
  | SOME stree =>
      let
        val visl = vistreel_of_searchtree stree
        val total = List.foldl
          (fn (v,acc) => acc + length_vistree v) 0 visl
      in
        check "search-tree view has nodes"
          (not (null visl) andalso total > 0);
        passok "print_vistree does not raise"
          (fn () => List.app print_vistree visl);
        passok "suggest_proof does not raise"
          (fn () => ignore (suggest_proof stree))
      end

val _ = passok "suggest with bounded depth does not raise"
  (fn () =>
    let val old = !suggest_depth in
      suggest_depth := SOME 3;
      ignore (suggest ());
      suggest_depth := old
    end)

val _ = passok "clean_ttt_tacdata_cache after search"
  (fn () => clean_ttt_tacdata_cache ())

val _ = passok "ttt works after cleaning in-memory tactic cache"
  (fn () => ignore (ttt ([],T)))

val _ = check "find_script locates ConseqConvScript.sml"
  (String.isSuffix "ConseqConvScript.sml" (find_script "ConseqConv"))

val _ = check "nonexistent tactic data is reported absent"
  (not (mlTacticData.exists_tacdata_thy "no_such_theory_for_ttt"))

open ttt_regressionTheory

fun rewrite_record_raw thy =
  let
    val _ = ttt_rewrite_thy thy
    val scriptorg = find_script thy
    val tttsml =
      tactictoe_scratch_dir_of () ^ "/scripts/" ^
      OS.Path.base scriptorg ^ "_ttt.sml"
    val _ = smlExecScripts.exec_tttrecord_in_dir (OS.Path.dir scriptorg) tttsml
  in
    tactictoe_dir_of () ^ "/log/scripts/" ^ thy
  end

val regression_script =
  (tprint "record rewriter regression tactic data";
   read_file (rewrite_record_raw "ttt_regression") before OK ())

val regression_data = read_file (tacdata_file "ttt_regression")

val _ = check "Q_TAC quotation step is recorded"
  (String.isSubstring "Q_TAC" regression_data andalso
   String.isSubstring "SUFF_TAC" regression_data andalso
   String.isSubstring "QUOTE" regression_data)

val _ = check "expanded proof wrapper is removed before recording"
  (not (String.isSubstring "HOL__GOAL__" regression_data) andalso
   not (String.isSubstring "HOL__GOAL__" regression_script))

val _ = check "attributed theorem is recorded under its bare name"
  (String.isSubstring
     "tttRecord.app_wrap_proof \"ATTR_REGRESSION\"" regression_script andalso
   String.isSubstring
     "tttRecord.record_proof \"ATTR_REGRESSION\"" regression_script)

(* Both root theories already have same-identity output at this point. *)
val _ = passok "parallel forced re-record replaces same-identity data"
  (fn () => ttt_record_opts
    [Scope (Theories ["sat", "marker"]),
     Parallel 2, Force true])

val _ = passok "parallel forced re-record leaves data up-to-date"
  (fn () => ttt_record_opts
    [Scope (Theories ["sat", "marker"]), DryRun true])

open arithmeticTheory dividesTheory gcdTheory

fun proves_by msg tm tac =
  (tprint msg;
   let val th = TAC_PROOF (([],tm), tac) in
     if aconv (concl th) tm then OK ()
     else die ("FAILED: conclusion mismatch: " ^
               term_to_string (concl th))
   end)
  handle e => die ("FAILED: " ^ exnMessage e)

val proof_theories = ["arithmetic", "divides", "gcd"]

val _ = passok "record proof.sml tactic data"
  (fn () => ttt_record_opts [Scope (Theories proof_theories)])

val _ = passok "proof.sml data is up-to-date after recording"
  (fn () => ttt_record_opts
    [Scope (Theories proof_theories), DryRun true])

val _ = clean_ttt_tacdata_cache ()
val _ = set_timeout 60.0

val _ = proves_by "sqrt2 example: even square implies even number"
  ``(divides 2 (a * a)) ==> divides 2 a``
  (REWRITE_TAC [divides_def] THEN ttt)

val _ = proves "sqrt2 example: equation gives even square"
  ``(a * a = 2 * (b * b)) ==> divides 2 (a * a)``

val _ = proves "sqrt2 example: equation gives even a"
  ``(a * a = 2 * (b * b)) ==> divides 2 a``

val _ = proves "sqrt2 example: even a gives four divides square"
  ``divides 2 a ==> divides (2 * 2) (a * a)``

val _ = proves "sqrt2 example: cancel common factor in divisibility"
  ``divides (2 * x) (2 * y) ==> divides x y``

val _ = proves "sqrt2 example: common divisibility reaches gcd"
  ``(divides 2 a /\ divides 2 b) ==> divides 2 (gcd a b)``

val _ = proves "sqrt2 example: one is not even"
  ``~((x = 1) /\ divides 2 x)``

val _ = proves "sqrt2 example: coprime gcd is not even"
  ``~(gcd a b = 1 /\ divides 2 (gcd a b))``

open listTheory rich_listTheory

val demo_theories = ["arithmetic", "list", "rich_list", "indexedLists"]

val _ = passok "record ttt_demo tactic data"
  (fn () => ttt_record_opts [Scope (Theories demo_theories)])

val _ = clean_ttt_tacdata_cache ()
val _ = set_timeout 30.0

val _ = proves "demo example: linear arithmetic"
  ``(2 * x + 1 = 3) ==> (x = 1)``

val _ = proves "demo example: constant map is replicate"
  ``(!n. f n = c) ==> (MAP f ls = REPLICATE (LENGTH ls) c)``
