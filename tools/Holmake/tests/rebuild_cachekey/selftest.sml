(* Test: --rebuild=cachekey (the default) skips script invocations when
   a theory target's inputs haven't changed (as measured by the
   recursive content hash recorded in a sibling .cachekey stamp file).
   --rebuild=mtime restores the traditional timestamp-based decision. *)

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

(* A byte-different version of baseScript.sml used only to simulate an
   edit that is never actually built. *)
val baseScript_stash =
    "Theory base[bare]\n\
    \Ancestors bool\n\
    \(* transient edit *)\n\
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

val _ = HOLFileSys.chDir "subdir"

(* --- helpers -------------------------------------------------------- *)

fun dat_path thy = thy ^ "Theory.dat"

fun mtime_of f =
    if HOLFileSys.access(f, [HOLFileSys.A_READ]) then
      SOME (HOLFileSys.modTime f)
    else NONE

(* On coarse filesystems, distinct events may share the same mtime.

   Sleep long enough that a subsequent file-write has a strictly
   greater mtime. *)
fun sleep_for_mtime () = OS.Process.sleep (Time.fromMilliseconds 1100)

(* The real FS path of a .hol/objs/-resident file. *)
fun fs_path_of holpath =
    case HFS_NameMunge.HOLtoFS holpath of
        SOME {fullfile, ...} => fullfile
      | NONE => holpath

fun stamp_path thy =
    let val datFS = fs_path_of (dat_path thy)
        val {base, ...} = OS.Path.splitBaseExt datFS
    in base ^ ".cachekey" end

fun timeToString (SOME t) = Time.toString t
  | timeToString NONE = "<missing>"

fun expect_same_mtime label f before_ =
    let val after_ = mtime_of f
    in
      case (before_, after_) of
          (SOME b, SOME a) =>
          if Time.compare (a, b) = EQUAL then OK()
          else die (label ^ ": " ^ f ^ " mtime changed " ^
                    Time.toString b ^ " -> " ^ Time.toString a)
        | _ => die (label ^ ": " ^ f ^ " missing (before=" ^
                    timeToString before_ ^ ", after=" ^ timeToString after_ ^
                    ")")
    end

fun expect_greater_mtime label f before_ =
    let val after_ = mtime_of f
    in
      case (before_, after_) of
          (SOME b, SOME a) =>
          if Time.compare (a, b) = GREATER then OK()
          else die (label ^ ": " ^ f ^ " mtime did not advance " ^
                    Time.toString b ^ " -> " ^ Time.toString a)
        | _ => die (label ^ ": " ^ f ^ " missing")
    end

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

val base_t0  = mtime_of (dat_path "base")
val child_t0 = mtime_of (dat_path "child")

val _ = tprint "Setup: cachekey stamps exist for base and child"
val _ =
    if OS.FileSys.access(stamp_path "base", [OS.FileSys.A_READ]) andalso
       OS.FileSys.access(stamp_path "child", [OS.FileSys.A_READ]) then OK()
    else die ("Expected stamps: " ^ stamp_path "base" ^ ", " ^
              stamp_path "child")

(* --- Scenario 1: Holmake twice, no changes -------------------------- *)
(* This is a basic sanity check that Holmake is idempotent when nothing
   has changed.  It doesn't discriminate cachekey from mtime logic --
   both would say "up-to-date" here, because the script's mtime hasn't
   advanced.  Scenarios 2 and 3 are the real tests of the cachekey
   short-circuit. *)

val _ = tprint "Second Holmake with no changes: baseTheory.dat mtime preserved"
val _ = sleep_for_mtime ()
val _ = ignore (run_holmake_out ["childTheory"])
val _ = expect_same_mtime "Holmake-twice" (dat_path "base") base_t0

val _ = tprint "Second Holmake with no changes: childTheory.dat mtime preserved"
val _ = expect_same_mtime "Holmake-twice" (dat_path "child") child_t0

(* --- Scenario 2: touch-only (no byte change) ------------------------ *)

val _ = tprint "Touch baseScript.sml (no byte change): baseTheory.dat \
                \mtime preserved"
val _ = sleep_for_mtime ()
val _ = OS.FileSys.setTime ("baseScript.sml", NONE)
val _ = ignore (run_holmake_out ["childTheory"])
val _ = expect_same_mtime "touch" (dat_path "base") base_t0

val _ = tprint "Touch baseScript.sml: childTheory.dat mtime preserved \
                \(no cascade)"
val _ = expect_same_mtime "touch" (dat_path "child") child_t0

(* --- Scenario 3: edit-without-building then revert ------------------ *)

val _ = tprint "Edit-and-revert without intermediate build: baseTheory.dat \
                \mtime preserved"
val _ = sleep_for_mtime ()
val _ = write_file "baseScript.sml" baseScript_stash
val _ = sleep_for_mtime ()
val _ = write_file "baseScript.sml" baseScript_v1
val _ = ignore (run_holmake_out ["childTheory"])
val _ = expect_same_mtime "edit-revert" (dat_path "base") base_t0

val _ = tprint "Edit-and-revert: childTheory.dat mtime preserved"
val _ = expect_same_mtime "edit-revert" (dat_path "child") child_t0

(* --- Scenario 4: real content change (negative control) ------------- *)

val _ = tprint "Adding a theorem to baseScript.sml: baseTheory.dat rebuilt"
val _ = sleep_for_mtime ()
val _ = write_file "baseScript.sml" baseScript_v2
val _ = OS.FileSys.setTime ("baseScript.sml", NONE)
val _ = ignore (run_holmake_out ["childTheory"])
val _ = expect_greater_mtime "real-change" (dat_path "base") base_t0

val _ = tprint "Adding a theorem: childTheory.dat cascade-rebuilt"
val _ = expect_greater_mtime "real-change" (dat_path "child") child_t0

(* Record the post-change mtime as a new baseline for scenario 5. *)
val base_t2 = mtime_of (dat_path "base")

(* --- Scenario 5: --rebuild=mtime escape hatch ----------------------- *)
(* A touch under the cachekey strategy does not advance .dat mtime
   (tested above).  Under --rebuild=mtime it should. *)

val _ = tprint "--rebuild=mtime: touch baseScript.sml does advance \
                \baseTheory.dat mtime"
val _ = sleep_for_mtime ()
val _ = OS.FileSys.setTime ("baseScript.sml", NONE)
val _ = ignore (run_holmake_out ["--rebuild=mtime", "childTheory"])
val _ = expect_greater_mtime "rebuild=mtime" (dat_path "base") base_t2

(* --- Scenario 6: missing target forces rebuild (safety check) ------- *)
(* Even with the stamp present and inputs unchanged, deleting the .dat
   should force a rebuild; we mustn't skip based on stamp alone. *)

val _ = tprint "Deleting baseTheory.dat forces a rebuild despite valid stamp"
val _ = HOLFileSys.remove (dat_path "base")
val _ = ignore (run_holmake_out ["childTheory"])
val _ =
    if HOLFileSys.access (dat_path "base", [HOLFileSys.A_READ]) then OK()
    else die "baseTheory.dat was not rebuilt"

(* --- cleanup -------------------------------------------------------- *)

val _ = run_holmake ["cleanAll"]
val _ = write_file "baseScript.sml" baseScript_v1
val _ = HOLFileSys.chDir ".."
