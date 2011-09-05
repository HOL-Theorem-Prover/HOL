(* this is an -*- sml -*- file*)
val heapname = "hol.builder";
local
val pd = !PolyML.Compiler.printDepth;
infix ++
fun p1 ++ p2 = OS.Path.concat (p1,p2)
in
val _ = PolyML.print_depth 0;
val _ = loadPath := (Systeml.HOLDIR ++ "src/boss") :: (!loadPath)
val _ = app load ["optionTheory", "pairLib", "sumTheory",
                  "numTheory", "arithmeticTheory", "Arith",
                  "numLib", "mesonLib", "BasicProvers",
                  "Datatype", "listTheory", "bossLib"];
val _ = PolyML.print_depth pd;
fun main () =
  (List.app use (CommandLine.arguments ());
   PolyML.rootFunction ());
val _ = PolyML.shareCommonData main;
val _ = PolyML.export ("hol.builder", main);
end;
