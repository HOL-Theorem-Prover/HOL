local
val pd = PolyML.get_print_depth ();
in
val _ = PolyML.print_depth 0;
val _ = use "prelude.ML";
val _ = PolyML.print_depth pd;
end;
fun main () = (prelude_main (); PolyML.rootFunction());
val _ = PolyML.shareCommonData main;
val _ = PolyML.export ("hol.bare.noquote", main);
