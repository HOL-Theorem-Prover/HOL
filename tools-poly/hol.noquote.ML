val _ = use "prelude.ML";
val _ = app load ["optionTheory", "pairLib", "sumTheory",
                  "numTheory", "arithmeticTheory", "Arith",
                  "numLib", "mesonLib", "BasicProvers",
                  "SingleStep", "Datatype",
                  "listTheory", "bossLib"];
open bossLib;
fun main () = (prelude_main (); PolyML.rootFunction());
val _ = PolyML.export ("hol.noquote", main);

