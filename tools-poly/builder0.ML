local
val pd = !PolyML.Compiler.printDepth;
in
val _ = PolyML.print_depth 0;
val _ = use "poly/poly-init2.ML";
val _ = PolyML.print_depth pd;
end;
local
val _ = loadPath := (OS.Path.concat (Systeml.HOLDIR, "sigobj")) :: (!loadPath);
val _ = app load ["boolLib", "proofManagerLib", "Arbrat"];
fun main () = 
  (List.app use (CommandLine.arguments ());
   PolyML.rootFunction ());
in
val _ = PolyML.shareCommonData main;
val _ = PolyML.export ("hol.builder0", main);
end;
