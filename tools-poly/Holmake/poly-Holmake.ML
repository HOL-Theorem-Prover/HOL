val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;
val _ = use "poly/poly-init.ML";

structure BasicIO = SML90;

fun useH f = 
  (use ("Holmake/" ^ f ^ ".sig");
   use ("Holmake/" ^ f ^ ".sml"));

val _ = useH "Systeml";
val _ = useH "internal_functions";
val _ = useH "Holmake_types";
val _ = useH "ReadHMF";

fun u f = use ("mlyacc/mlyacclib/" ^ f ^ ".sml");
val _ = u "MLY_base-sig";
val _ = u "MLY_join";
val _ = u "MLY_lrtable";
val _ = u "MLY_stream";
val _ = u "MLY_parser2";

val _ = useH "Parser.grm";
val _ = use "Holmake/Lexer.lex.sml";

val _ = use "Holmake/Holdep.sml";
val _ = use "Holmake/Holmake.sml";

val _ = PolyML.shareCommonData Holmake.main;
val _ = PolyML.export ("Holmake/Holmake", Holmake.main);

