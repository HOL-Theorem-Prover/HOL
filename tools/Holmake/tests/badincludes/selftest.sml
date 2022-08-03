open testutils

infix ++
val op++ = OS.Path.concat

val hm = Globals.HOLDIR ++ "bin" ++ "Holmake"

fun inDir d f x =
    let
      val d0 = OS.FileSys.getDir ()
      val _ = OS.FileSys.chDir d handle _ => die ("Bad dir "^d)
      val res = Exn.capture f x
    in
      OS.FileSys.chDir d0;
      Exn.release res
    end

fun pResult (Mosml.Success s) = "Succeeded with: \"" ^ String.toString s ^ "\""
  | pResult (Mosml.Failure s) = "Failed with: \"" ^ String.toString s ^ "\""

fun t P msg args = (
  tprint msg;
  require_msg (check_result P) pResult (Mosml.run hm args) ""
)

open Mosml
fun succeed_and is (Success s) = List.all (fn i => String.isSubstring i s) is
  | succeed_and _ _ = false
fun fail_and is (Failure s) = List.all (fn i => String.isSubstring i s) is
  | fail_and _ _ = false

val _ = inDir "dir1"
              (t (fail_and ["dir2"]) "Bad INCLUDES line in a Holmakefile") []
val _ = inDir "dir3"
              (t (fail_and ["dir2"]) "Bad -I line in c/line to Holmake")
              ["-I", "../dir2"]
val _ = inDir "warnincs"
              (t (succeed_and ["Repeated definition", "FOO"])
                 "Repeated definition of variable") []
val _ = inDir "dieincs"
              (t (fail_and ["Can't redefine", "INCLUDES"])
                 "Repeated definition of INCLUDES") []

val _ = inDir "selfloopdir"
              (t (fail_and ["INCLUDES chain"]) "INCLUDES self-loop") []
val _ = inDir "onesteploopdir"
              (t (fail_and ["INCLUDES chain"]) "INCLUDES one-step-loop") []
val _ = inDir "nestedloopdir"
              (t (fail_and ["INCLUDES chain"]) "More complex INCLUDES loop") []
val _ = inDir "loopish_but_ok"
              (t (succeed_and [if Systeml.ML_SYSNAME = "poly" then "Finished"
                               else "Yay"])
                 "INCLUDES DAG OK")
              ["-r"]
