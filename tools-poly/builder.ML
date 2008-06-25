local
val pd = !PolyML.Compiler.printDepth;
in
val _ = PolyML.print_depth 0;
val _ = app load ["optionTheory", "pairLib", "sumTheory",
                  "numTheory", "arithmeticTheory", "Arith",
                  "numLib", "mesonLib", "BasicProvers",
                  "SingleStep", "Datatype",
                  "listTheory", "bossLib"];
val _ = PolyML.print_depth pd;
fun main () =
  (List.app use (CommandLine.arguments ());
   PolyML.rootFunction ());
val _ = PolyML.shareCommonData main;
val _ = PolyML.export ("hol.builder", main);
end;
