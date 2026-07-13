open testutils

val _ = OS.FileSys.chDir "testproj"

infix ++
val op++ = OS.Path.concat

val _ = tprint "Generating JSON graph"
val _ = require (check_result OS.Process.isSuccess) OS.Process.system
                (Systeml.HOLDIR ++ "bin" ++ "Holmake" ^ " --json > graph.json")

val _ = tprint "Loading JSON-encoded dep. graph"
fun checkjson j = let
  open JSON
in
  case j of
      ARRAY objs => length objs = 3
    | _ => false
end
val _ = require (check_result checkjson)
                JSONParser.parseFile "graph.json"
