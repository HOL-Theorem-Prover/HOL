(* Moscow ML implementation of munger creation program *)

val toload = map (fn s => s ^ ".uo") (CommandLine.arguments())

infix ++
fun (p1 ++ p2) = OS.Path.concat (p1, p2)

open Systeml

val _ = systeml
            ([MOSMLDIR ++ "mosmlc"] @
             (if Systeml.isUnix then ["-standalone"] else []) @
             ["-o", "munge", "-I", HOLDIR ++ "sigobj",
              "-I", HOLDIR ++ "src" ++ "TeX"] @
             toload @
             [HOLDIR ++ "src" ++ "TeX" ++ "mosmlmunge.uo"])




