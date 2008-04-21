(* this is an -*- sml -*- file *)
val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;
val _ = use "quote-filter.sml";
val _ = PolyML.shareCommonData main;
val _ = PolyML.export("unquote", main);
