(* Regression test for issue #381 (first step): export_theory is idempotent
   on no-op rebuilds.  If re-running fooScript.sml produces a Theory.dat
   whose content matches the existing file, the existing file (and its
   mtime) must be left alone, so that Holmake's timestamp-based dep-check
   does not cascade a rebuild to descendant theories. *)

open testutils

val op++ = OS.Path.concat
val Holmake = Globals.HOLDIR ++ "bin" ++ "Holmake"
val holstate_args =
    if Systeml.ML_SYSNAME = "poly" then
      ["--holstate", Globals.HOLDIR ++ "bin" ++ "hol.state0"]
    else []

fun run_holmake args =
    Systeml.systeml ([Holmake] @ holstate_args @ args)

fun run_holmake_out args =
    let val tmp = OS.FileSys.tmpName ()
        val res = Systeml.systeml_out {outfile = tmp}
                                      ([Holmake] @ holstate_args @ args)
    in
      OS.FileSys.remove tmp handle OS.SysErr _ => ();
      res
    end

fun write_file path contents =
    let val strm = TextIO.openOut path
    in TextIO.output(strm, contents); TextIO.closeOut strm end

val baseScript_v1 =
    "Theory base[bare]\n\
    \Ancestors bool\n\
    \Theorem base_thm = TRUTH\n"

(* Add a comment.  Same theory content, but the script file's bytes change
   (and so will its mtime), so Holmake will still rerun it. *)
val baseScript_v1_comment =
    "(* a comment that doesn't change the exported theory *)\n\
    \Theory base[bare]\n\
    \Ancestors bool\n\
    \Theorem base_thm = TRUTH\n"

(* A real content change: adds a new theorem. *)
val baseScript_v2 =
    "Theory base[bare]\n\
    \Ancestors bool\n\
    \Theorem base_thm = TRUTH\n\
    \Theorem base_thm2 = TRUTH\n"

val childScript =
    "Theory child[bare]\n\
    \Ancestors base\n\
    \Theorem child_thm = base_thm\n"

(* Work in a subdirectory shared with other tests' layout; restore at end. *)
val _ = HOLFileSys.chDir "subdir"

(* --- helpers -------------------------------------------------------- *)

fun dat_path thy = thy ^ "Theory.dat"

fun mtime_of f =
    if HOLFileSys.access(f, [HOLFileSys.A_READ]) then
      SOME (HOLFileSys.modTime f)
    else NONE

fun mtime_to_string NONE = "<missing>"
  | mtime_to_string (SOME t) = Time.toString t

(* On fast machines / coarse filesystems, distinct events may share the
   same mtime.  Sleep long enough that a subsequent file-write will have a
   strictly-greater mtime than any file just written.  1s is the coarsest
   filesystem resolution we expect to see in practice. *)
fun sleep_for_mtime () = OS.Process.sleep (Time.fromMilliseconds 1100)

(* --- setup: clean baseline build ------------------------------------ *)

val _ = run_holmake ["cleanAll"]
val _ = write_file "baseScript.sml" baseScript_v1
val _ = write_file "childScript.sml" childScript

val _ = tprint "Setup: initial build of baseTheory+childTheory"
val _ =
    if OS.Process.isSuccess (run_holmake_out ["childTheory"]) andalso
       HOLFileSys.access (dat_path "base", [HOLFileSys.A_READ]) andalso
       HOLFileSys.access (dat_path "child", [HOLFileSys.A_READ]) then OK()
    else die "initial build failed"

val base_t0  = valOf (mtime_of (dat_path "base"))
val child_t0 = valOf (mtime_of (dat_path "child"))

(* --- Scenario A: comment-only edit of baseScript.sml ---------------- *)

val _ = tprint "Comment-only edit to baseScript.sml: baseTheory.dat mtime \
                \is preserved"
val _ = sleep_for_mtime ()
val _ = write_file "baseScript.sml" baseScript_v1_comment
val _ = OS.FileSys.setTime ("baseScript.sml", NONE) (* ensure mtime advances *)

val _ =
    if OS.Process.isSuccess (run_holmake_out ["childTheory"]) then ()
    else die "rebuild after comment edit failed"

val base_t1 = valOf (mtime_of (dat_path "base"))
val _ =
    if Time.compare (base_t1, base_t0) = EQUAL then OK()
    else die ("baseTheory.dat mtime changed unexpectedly: " ^
              Time.toString base_t0 ^ " -> " ^ Time.toString base_t1)

val _ = tprint "Comment-only edit: childTheory.dat mtime is preserved \
                \(no cascade)"
val child_t1 = valOf (mtime_of (dat_path "child"))
val _ =
    if Time.compare (child_t1, child_t0) = EQUAL then OK()
    else die ("childTheory.dat mtime changed unexpectedly: " ^
              Time.toString child_t0 ^ " -> " ^ Time.toString child_t1)

(* --- Scenario B: real content change to baseScript.sml -------------- *)

val _ = tprint "Adding a theorem to baseScript.sml: baseTheory.dat is \
                \rewritten"
val _ = sleep_for_mtime ()
val _ = write_file "baseScript.sml" baseScript_v2
val _ = OS.FileSys.setTime ("baseScript.sml", NONE)

val _ =
    if OS.Process.isSuccess (run_holmake_out ["childTheory"]) then ()
    else die "rebuild after content change failed"

val base_t2 = valOf (mtime_of (dat_path "base"))
val _ =
    if Time.compare (base_t2, base_t1) = GREATER then OK()
    else die ("baseTheory.dat mtime did not advance: " ^
              Time.toString base_t1 ^ " -> " ^ Time.toString base_t2)

val _ = tprint "Adding a theorem to baseScript.sml: childTheory.dat is \
                \rebuilt (cascade)"
val child_t2 = valOf (mtime_of (dat_path "child"))
val _ =
    if Time.compare (child_t2, child_t1) = GREATER then OK()
    else die ("childTheory.dat mtime did not advance: " ^
              Time.toString child_t1 ^ " -> " ^ Time.toString child_t2)

(* --- Scenario C: touch-only (no content change) --------------------- *)

val _ = tprint "Touching baseScript.sml (no content change): baseTheory.dat \
                \mtime is preserved"
val _ = sleep_for_mtime ()
val _ = OS.FileSys.setTime ("baseScript.sml", NONE)

val _ =
    if OS.Process.isSuccess (run_holmake_out ["childTheory"]) then ()
    else die "rebuild after touch failed"

val base_t3 = valOf (mtime_of (dat_path "base"))
val _ =
    if Time.compare (base_t3, base_t2) = EQUAL then OK()
    else die ("baseTheory.dat mtime changed after mere touch: " ^
              Time.toString base_t2 ^ " -> " ^ Time.toString base_t3)

(* --- cleanup -------------------------------------------------------- *)

val _ = run_holmake ["cleanAll"]
val _ = write_file "baseScript.sml" baseScript_v1
val _ = HOLFileSys.chDir ".."
