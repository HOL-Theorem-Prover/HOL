(* End-to-end check on the directory column of the per-target
   completion lines the parallel builder prints (see
   tools/Holmake/poly/MB_Monitor.sml).

   The column names the source tree a directory belongs to -- with the
   directory's holpathdb registration, "$(dcTreeA)" -- only when the
   directories being built span more than one tree.  testdir has both
   configurations: treeA and treeB carry a holproject.toml each and so
   are two trees, while same/d1 and same/d2 are plain directories
   under HOLDIR and so are one.
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

(* the completion line for tgt: the one line naming it that also
   carries a verdict *)
fun completion_line tgt lines =
    case List.filter (fn l => String.isSubstring tgt l andalso
                              String.isSubstring "OK" l andalso
                              not (String.isSubstring "Starting work" l))
                     lines
     of
        [l] => l
      | [] => (die ("no completion line for " ^ tgt); "")
      | _ => (die ("multiple completion lines for " ^ tgt); "")

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
