(* Moscow ML implementation of munger creation program *)

val (exeopt, toload0, staticp) = mkmkcline.read_cline()

val toload = map (fn s => s ^ ".uo") toload0
val exe = case exeopt of
            NONE => "munge.exe"
          | SOME s => s

infix ++
fun (p1 ++ p2) = OS.Path.concat (p1, p2)

open Systeml

val _ = systeml
            ([MOSMLDIR ++ "mosmlc"] @
             (if Systeml.isUnix andalso staticp then ["-standalone"] else []) @
             ["-o", exe, "-I", HOLDIR ++ "sigobj",
              "-I", HOLDIR ++ "src" ++ "TeX"] @
             toload @
             [HOLDIR ++ "src" ++ "TeX" ++ "mosmlmunge.uo"])




