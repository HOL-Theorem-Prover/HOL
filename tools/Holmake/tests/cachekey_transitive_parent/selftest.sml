(* Regression test for "stale parent" cachekey bug.
   See README.md for the underlying mechanism.

   The test reports OK when the bug is ABSENT (i.e. when consumeScript
   builds cleanly after parent has changed and outer has been cleaned),
   which is the case now that the bug is fixed.  A failure means it has
   returned: the die() carries the captured link_parents text from
   Holmake's logs, which is the signature to look for. *)

open testutils

val op++ = OS.Path.concat
val testRoot = OS.FileSys.getDir ()
val innerDir = testRoot ++ "inner"
val outerDir = testRoot ++ "outer"
val holmake = Globals.HOLDIR ++ "bin" ++ "Holmake"
val cacheDir = testRoot ++ ".cache-iso"

(* Use an in-test isolated cache directory so the test cannot disturb
   ~/.cache/HOL.  --cache-dir is forwarded explicitly on every Holmake
   invocation. *)
fun cacheArgs () = ["--cache-dir=" ^ cacheDir]

fun rm_rf path =
    let
      fun rm p =
          if OS.FileSys.isDir p handle OS.SysErr _ => false then
            (let val strm = OS.FileSys.openDir p
                 fun loop () =
                     case OS.FileSys.readDir strm of
                         NONE => OS.FileSys.closeDir strm
                       | SOME f => (rm (p ++ f); loop ())
             in loop () end;
             OS.FileSys.rmDir p handle OS.SysErr _ => ())
          else
            (OS.FileSys.remove p handle OS.SysErr _ => ())
    in rm path end

fun ensureDir d =
    if OS.FileSys.isDir d handle OS.SysErr _ => false then ()
    else OS.FileSys.mkDir d handle OS.SysErr _ => ()

fun in_dir d f =
    let val saved = OS.FileSys.getDir ()
        val _ = OS.FileSys.chDir d
        val r = f () handle e => (OS.FileSys.chDir saved; raise e)
    in OS.FileSys.chDir saved; r end

(* Run Holmake in [dir] with [args].  Capture combined stdout/stderr to
   [logfile].  Returns (status, log_contents). *)
fun run_holmake_in dir args logfile =
    let
      val argv = holmake :: (cacheArgs () @ args)
      val status =
          in_dir dir (fn () =>
            Systeml.systeml_out {outfile = logfile} argv)
      val log =
          let val strm = TextIO.openIn logfile
              val s = TextIO.inputAll strm
          in TextIO.closeIn strm; s end
          handle IO.Io _ => ""
    in (status, log) end

fun writeFile path content =
    let val out = TextIO.openOut path
    in TextIO.output (out, content); TextIO.closeOut out end

val parentV1 =
"open HolKernel Parse boolLib\n\
\\n\
\val _ = new_theory \"parent\";\n\
\val parent_thm = save_thm(\"parent_thm\", TRUTH);\n\
\val _ = export_theory();\n"

val parentV2 =
"open HolKernel Parse boolLib\n\
\\n\
\val _ = new_theory \"parent\";\n\
\(* Different content -> different parentTheory.dat hash. *)\n\
\val parent_thm = save_thm(\"parent_thm\", DISCH_ALL (ASSUME ``T``));\n\
\val _ = export_theory();\n"

val parentScript = innerDir ++ "parentScript.sml"

fun fresh_cache () = (rm_rf cacheDir; ensureDir cacheDir)

(* Force a full clean of both halves of the test world before/after. *)
fun nukeBuildArtifacts () =
    (rm_rf (innerDir ++ ".hol");
     rm_rf (outerDir ++ ".hol");
     rm_rf (outerDir ++ "qux"))

val logfile = testRoot ++ ".selftest-step.log"
val publicationGuard = outerDir ++ ".check-cache-publication"

fun readFile path =
    let val ins = TextIO.openIn path
        val text = TextIO.inputAll ins
    in TextIO.closeIn ins; text end

(* Save the child's manifest before changing its indirectly imported parent.
   Later install it under the NEW key, forcing validation to do the work. *)
fun childManifest () =
    let val dir = cacheDir ++ "key"
        val ds = OS.FileSys.openDir dir
        fun loop () =
            case OS.FileSys.readDir ds of
                NONE => raise Fail "No wrapping_child cache manifest"
              | SOME name =>
                  let val text = readFile (dir ++ name)
                  in if String.isSubstring "wrapping_childTheory.dat" text
                     then text else loop () end
        val text = loop ()
                   handle e => (OS.FileSys.closeDir ds; raise e)
    in OS.FileSys.closeDir ds; text end

(* ------------------------------------------------------------------ *)
val _ = tprint "cachekey_transitive_parent reproducer"

val _ = fresh_cache ()
val _ = nukeBuildArtifacts ()

fun mustSucceed (status, log, what) =
    if OS.Process.isSuccess status then ()
    else die (what ^ " failed:\n" ^ log)

(* parentScript.sml is generated rather than stored under version
   control: the steps below rewrite it, so a tracked copy would be
   reported as modified for the duration of every run, and would be
   left modified by any run killed before it could restore it.  Remove
   it on the way out; step 1 writes it afresh each time. *)
fun discard_parent () =
    (OS.FileSys.remove parentScript handle OS.SysErr _ => ();
     OS.FileSys.remove publicationGuard handle OS.SysErr _ => ())

val _ =
  let
    val _ = discard_parent ()
    (* Step 1: Build with parent v1.  Establishes the (buggy) cachekey
       for wrapping_child in the cache. *)
    val _ = writeFile parentScript parentV1
    val (s1a, log1a) = run_holmake_in innerDir [] logfile
    val _ = mustSucceed (s1a, log1a, "Step 1 inner v1 build")
    val (s1b, log1b) = run_holmake_in outerDir [] logfile
    val _ = mustSucceed (s1b, log1b, "Step 1 outer v1 build")
    val staleManifest = childManifest ()

    (* Step 2: Change parent's content; rebuild inner only. *)
    val _ = writeFile parentScript parentV2
    val _ = rm_rf (innerDir ++ ".hol")
    val (s2, log2) = run_holmake_in innerDir [] logfile
    val _ = mustSucceed (s2, log2, "Step 2 inner v2 build")

    (* Step 3: Clean outer (this is what activates the bug -- the
       additional_theories augmentation in Holmake.sml requires the
       generated wrapping_childTheory.sml to exist on disk, which it
       doesn't after cleanAll, so the cachekey is computed without
       parent in scope).  Then rebuild outer.  If consumeScript runs
       cleanly, the cachekey is correctly tracking parent.  If it
       fails with link_parents, the bug is present. *)
    val _ = rm_rf (outerDir ++ ".hol")
    val _ = rm_rf (outerDir ++ "qux")
    val (keyStatus, keyLog) =
        run_holmake_in outerDir ["--cachekey", "wrapping_childTheory"] logfile
    val _ = mustSucceed (keyStatus, keyLog, "Computing current child key")
    val keys = List.filter
        (fn s => size s = 40 andalso CharVector.all Char.isHexDigit s)
        (String.tokens Char.isSpace keyLog)
    val key = case keys of [k] => k
                        | _ => raise Fail ("Unexpected cachekey: " ^ keyLog)
    val _ = writeFile (cacheDir ++ "key" ++ key) staleManifest
    val _ = writeFile publicationGuard ""
    val (s3, log3) = run_holmake_in outerDir ["--verbose"] logfile

    (* BuildCommand redirects cache diagnostics into the theory's log,
       not Holmake's outer progress output. *)
    val childLog = readFile
        (outerDir ++ ".hol" ++ "logs" ++ "wrapping_childTheory")
        handle IO.Io _ => "(child theory log unavailable)"
    val ok = OS.Process.isSuccess s3 andalso
             String.isSubstring "Cache hit ignored: parent hashes" childLog
  in
    if ok then (discard_parent (); OK ())
    else
      let
        val link_parents_present =
            String.isSubstring "link_parents" log3
        val why =
            if link_parents_present then
              "Stale wrapping_child.dat fetched from cache; consume's \
              \link_parents check failed against current parent.  \
              \This IS the bug under test (expected until fixed)."
            else
              "outer rebuild failed, or the forced stale cache hit was \
              \not explicitly rejected by parent validation."
      in
        discard_parent ();
        die ("Stale-cache validation regression.\n  " ^ why ^
             "\n  --- captured outer log ---\n" ^ log3 ^
             "\n  --- child theory log ---\n" ^ childLog)
      end
  end
  handle e => (discard_parent (); raise e)
