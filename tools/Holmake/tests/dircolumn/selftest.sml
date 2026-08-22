(* End-to-end checks on how the parallel builder names directories.

   Two kinds of line are covered.  The directory column of the
   per-target completion lines (see tools/Holmake/poly/MB_Monitor.sml)
   names the source tree a directory belongs to -- with the directory's
   holpathdb registration, "$(dcTreeA)" -- only when the directories
   being built span more than one tree.  testdir has both
   configurations: treeA and treeB carry a holproject.toml each and so
   are two trees, while same/d1 and same/d2 are plain directories
   under HOLDIR and so are one.

   The per-directory "Finished <dir>" lines (see
   tools/Holmake/poly/multibuild.sml) go through that same renderer, so
   a directory is named the same way whether it is being reported
   finished or carrying a target -- the cases below check the two
   agree rather than pinning a spelling.  These lines once named every
   directory "." (hmdir.curdir() stored a relpath relative to whatever
   the cwd was while the directory was scanned, and they print after
   that chdir is undone), and once came out before the completion line
   of the target that finished the directory.
*)

open testutils

infix ++
val op++ = OS.Path.concat
val holmake = Systeml.HOLDIR ++ "bin" ++ "Holmake"

fun readfile f =
    let val is = TextIO.openIn f
    in TextIO.inputAll is before TextIO.closeIn is
    end

fun scrub f = ignore (OS.FileSys.remove f) handle OS.SysErr _ => ()

(* Run Holmake to completion in dir, having thrown away the products
   named, and return the lines it printed.  The products are plain
   files made by the fixture's own `touch' recipes, so there is no need
   to go through cleanAll (which wouldn't reach the sibling tree
   anyway).

   The column is the first thing sacrificed to a narrow terminal, so
   the width has to be pinned for the assertions below to mean
   anything: stdin comes from /dev/null so Holmake's `stty size' probe
   fails, leaving COLUMNS to answer for it. *)
fun hm_in (dir, products) =
    let
      val _ = List.app scrub products
      val d0 = OS.FileSys.getDir()
      val _ = OS.FileSys.chDir dir
      val cmd = "COLUMNS=100 " ^ holmake ^
                " --no-cache < /dev/null > output 2>&1"
      val res = OS.Process.system cmd
      val out = readfile "output"
      val _ = OS.FileSys.chDir d0
    in
      if OS.Process.isSuccess res then String.fields (fn c => c = #"\n") out
      else (die ("Holmake in " ^ dir ^ " failed:\n" ^ out); [])
    end

(* the line naming tgt that also carries a verdict *)
fun is_completion tgt l =
    String.isSubstring tgt l andalso String.isSubstring "OK" l andalso
    not (String.isSubstring "Starting work" l)

(* the completion line for tgt: there should be exactly one *)
fun completion_line tgt lines =
    case List.filter (is_completion tgt) lines of
        [l] => l
      | [] => (die ("no completion line for " ^ tgt); "")
      | _ => (die ("multiple completion lines for " ^ tgt); "")

val finished_pfx = "Finished "

(* the directory a "Finished <dir>" line names; the line runs
   "Finished ", the directory, an optional "[#theories: n]" and the
   right-aligned elapsed time *)
fun finished_dir l =
    if String.isPrefix finished_pfx l then
      case String.tokens Char.isSpace
                         (String.extract (l, size finished_pfx, NONE))
       of
          d :: _ => SOME d
        | [] => NONE
    else NONE

fun finished_dirs lines = List.mapPartial finished_dir lines

fun position p lines =
    let
      fun go _ [] = NONE
        | go i (l :: ls) = if p l then SOME i else go (i + 1) ls
    in
      go 0 lines
    end

fun testcase what fixture check =
    let
      val lines = hm_in fixture
    in
      tprint what;
      case check lines of
          NONE => OK()
        | SOME msg => die msg
    end

val _ = OS.FileSys.chDir "testdir"

val _ = testcase
          "Multi-tree build names each target's tree"
          ("treeB", ["treeA" ++ "dcA.out", "treeB" ++ "dcB.out"])
          (fn lines =>
              let
                val a = completion_line "dcA.out" lines
                val b = completion_line "dcB.out" lines
              in
                if String.isSubstring "$(dcTreeA)" a andalso
                   String.isSubstring "$(dcTreeB)" b
                then NONE
                else SOME ("no holpath prefixes in:\n" ^ a ^ "\n" ^ b)
              end)

val _ = testcase
          "Single-tree build leaves the tree name off"
          ("same", ["same" ++ "d1" ++ "dcC.out",
                    "same" ++ "d2" ++ "dcD.out"])
          (fn lines =>
              let
                val c = completion_line "dcC.out" lines
                val d = completion_line "dcD.out" lines
              in
                if String.isSubstring "$(" c orelse
                   String.isSubstring "$(" d
                then SOME ("holpath prefix in single-tree build:\n" ^
                           c ^ "\n" ^ d)
                else if String.isSubstring "same/d1" c andalso
                        String.isSubstring "same/d2" d
                then NONE
                else SOME ("directory column missing from:\n" ^ c ^ "\n" ^ d)
              end)

(* the directory column of tgt's completion line, which runs the
   target, the directory, the time and the verdict, none of them
   containing a space *)
fun column_dir tgt lines =
    case String.tokens Char.isSpace (completion_line tgt lines) of
        _ :: d :: _ => d
      | _ => (die ("no directory column for " ^ tgt); "")

(* A directory's report and the column of a target in it name the same
   directory, so the two strings must be equal.  Comparing them rather
   than pinning a spelling keeps these cases honest whichever way the
   shared renderer names things -- and equality matters: a report of
   "d1" would still be a substring of a column reading ".../same/d1". *)
fun agreement_failures tgts lines =
    let
      fun chk tgt =
          let
            val d = column_dir tgt lines
          in
            if List.exists (fn l => finished_dir l = SOME d) lines then NONE
            else SOME ("no report names " ^ d ^ " for " ^ tgt ^ "; got " ^
                       String.concatWith ", " (finished_dirs lines))
          end
    in
      List.mapPartial chk tgts
    end

val _ = testcase
          "Each directory is reported the way its targets are named"
          ("same", ["same" ++ "d1" ++ "dcC.out",
                    "same" ++ "d2" ++ "dcD.out"])
          (fn lines =>
              case agreement_failures ["dcC.out", "dcD.out"] lines of
                  [] =>
                  (* and the two are told apart: reporting each of them
                     as "." was the original defect *)
                  (case finished_dirs lines of
                       [d1, d2] => if d1 <> d2 then NONE
                                   else SOME ("both reported as " ^ d1)
                     | ds => SOME ("expected two reports, got " ^
                                   Int.toString (length ds)))
                | msgs => SOME (String.concatWith "; " msgs))

val _ = testcase
          "Reports across trees are named by tree, as the columns are"
          ("treeB", ["treeA" ++ "dcA.out", "treeB" ++ "dcB.out"])
          (fn lines =>
              case agreement_failures ["dcA.out", "dcB.out"] lines of
                  [] => if List.all (String.isPrefix "$(")
                                    (finished_dirs lines)
                        then NONE
                        else SOME ("expected holpath names, got: " ^
                                   String.concatWith ", "
                                                     (finished_dirs lines))
                | msgs => SOME (String.concatWith "; " msgs))

(* A directory is finished when its last target is, so its line must
   come after that target's.  The count is crossed inside the job's
   `update', which ProcessMultiplexor runs before handing the monitor
   the Terminated message that prints the target line, so reporting
   from there put the two the wrong way round. *)
val _ = testcase
          "A directory is reported finished after its last target"
          ("same", ["same" ++ "d1" ++ "dcC.out",
                    "same" ++ "d2" ++ "dcD.out"])
          (fn lines =>
              let
                fun outoforder tgt =
                    let
                      val d = column_dir tgt lines
                      fun names l = finished_dir l = SOME d
                    in
                      case (position (is_completion tgt) lines,
                            position names lines) of
                          (SOME t, SOME f) =>
                          if t < f then NONE
                          else SOME ("the report for " ^ tgt ^
                                     "'s directory precedes it")
                        | (NONE, _) => SOME ("no completion line for " ^ tgt)
                        | (_, NONE) => SOME ("no report for " ^ tgt ^
                                             "'s directory")
                    end
              in
                case List.mapPartial outoforder ["dcC.out", "dcD.out"] of
                    [] => NONE
                  | msgs => SOME (String.concatWith "; " msgs)
              end)
