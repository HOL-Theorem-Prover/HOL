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

fun okres _ (Mosml.Success s) = false
  | okres i (Mosml.Failure s) = String.isSubstring i s

fun pResult (Mosml.Success s) = "Succeeded with: \"" ^ String.toString s ^ "\""
  | pResult (Mosml.Failure s) = "Failed with: \"" ^ String.toString s ^ "\""

fun t msg args = (
  tprint msg;
  require_msg (check_result (okres "../dir2")) pResult (Mosml.run hm args) ""
)

val _ = inDir "dir1" (t "Bad INCLUDES line in a Holmakefile") []
val _ = inDir "dir3" (t "Bad -I line in c/line to Holmake") ["-I", "../dir2"]
