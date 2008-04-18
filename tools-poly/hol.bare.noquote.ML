val _ = use "prelude.ML";
fun main () = (prelude_main (); PolyML.rootFunction());
val _ = PolyML.shareCommonData main;
val _ = PolyML.export ("hol.bare.noquote", main);
