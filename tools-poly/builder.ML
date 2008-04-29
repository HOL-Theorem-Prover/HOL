local
val pd = PolyML.get_print_depth ();
in
val _ = PolyML.print_depth 0;
val _ = app load ["optionTheory", "pairLib", "sumTheory",
                  "numTheory", "arithmeticTheory", "Arith",
                  "numLib", "mesonLib", "BasicProvers",
                  "SingleStep", "Datatype",
                  "listTheory", "bossLib"];
val _ = PolyML.print_depth pd;
val _ = PolyML.shareCommonData PolyML.rootFunction;
val _ = PolyML.export ("hol.builder", PolyML.rootFunction);
end;
