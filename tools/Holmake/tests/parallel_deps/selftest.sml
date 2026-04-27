open testutils

infix ++
val op++ = OS.Path.concat

fun exists p = HOLFileSys.access(p, [OS.FileSys.A_READ])
fun die_missing p = die ("Expected build product missing: " ^ p)

val holmake = Globals.HOLDIR ++ "bin" ++ "Holmake"
val depchain_dir = ".." ++ "depchain1" ++ "dir3"
val holstate0 = Globals.HOLDIR ++ "bin" ++ "hol.state0"

fun holmake_args args =
    [holmake] @
    (if Systeml.ML_SYSNAME = "poly" then ["--holstate", holstate0] else []) @
    args

fun run_holmake desc args =
    let
      val _ = tprint desc
      val res = Systeml.systeml (holmake_args args)
    in
      if OS.Process.isSuccess res then OK()
      else die ("Holmake failed while " ^ desc)
    end

val products =
    [".." ++ "dir2" ++ "dir1" ++ "baseTheory.ui",
     ".." ++ "dir2" ++ "dir1" ++ "baseTheory.uo",
     ".." ++ "dir2" ++ "baseLib.ui",
     ".." ++ "dir2" ++ "baseLib.uo",
     "nextTheory.ui",
     "nextTheory.uo",
     "lastTheory.ui",
     "lastTheory.uo"]

val here = HOLFileSys.getDir()

val _ = HOLFileSys.chDir depchain_dir
val _ = run_holmake "cleaning cross-directory dependency chain"
                    ["-r", "cleanAll"]
val _ = run_holmake "building cross-directory dependency chain with -j2"
                    ["--jobs=2", "lastTheory.uo"]
val _ = app (fn p => if exists p then () else die_missing p) products
val _ = HOLFileSys.chDir here
