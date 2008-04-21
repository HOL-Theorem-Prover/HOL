local
val pd = PolyML.get_print_depth ();
in
val _ = PolyML.print_depth 0;
val _ = use "prelude.ML";
val _ = app load ["optionTheory", "pairLib", "sumTheory",
                  "numTheory", "arithmeticTheory", "Arith",
                  "numLib", "mesonLib", "BasicProvers",
                  "SingleStep", "Datatype",
                  "listTheory", "bossLib"];
val _ = PolyML.print_depth pd;
end;
open bossLib;
fun main () = (prelude_main (); PolyML.rootFunction());
val _ = PolyML.shareCommonData main;
val _ = PolyML.export ("hol.noquote", main);
