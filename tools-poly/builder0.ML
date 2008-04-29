local
val pd = PolyML.get_print_depth ();
in
val _ = PolyML.print_depth 0;
val _ = use "poly/poly-init2.ML";
val _ = PolyML.print_depth pd;
end;
val _ = loadPath := (OS.Path.concat (Systeml.HOLDIR, "sigobj")) :: (!loadPath);
val _ = app load ["boolLib", "goalstackLib", "Arbrat"];
val _ = PolyML.shareCommonData PolyML.rootFunction;
val _ = PolyML.export ("hol.builder0", PolyML.rootFunction);
