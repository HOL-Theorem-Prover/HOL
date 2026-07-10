val _ = OS.FileSys.chDir "testproj"

infix ++
val op++ = OS.Path.concat

fun die s = (TextIO.output(TextIO.stdErr, "Failure: " ^ s ^ "\n");
             OS.Process.exit OS.Process.failure)

val _ = OS.Process.system(Systeml.HOLDIR ++ "bin" ++ "Holmake" ^ " --json > graph.json")

val jfile = JSONParser.parseFile "graph.json"
              handle Fail s => die ("JSONParser error: " ^ s)

val _ = OS.Process.exit OS.Process.success
