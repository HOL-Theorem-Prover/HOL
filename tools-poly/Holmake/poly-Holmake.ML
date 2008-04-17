use "poly/poly-init.ML";

structure BasicIO = SML90;

fun useH f = 
  (use ("Holmake/" ^ f ^ ".sig");
   use ("Holmake/" ^ f ^ ".sml"));

useH "Systeml";
useH "internal_functions";
useH "Holmake_types";
useH "ReadHMF";

fun u f = use ("mlyacc/mlyacclib/" ^ f ^ ".sml");
u "MLY_base-sig";
u "MLY_join";
u "MLY_lrtable";
u "MLY_stream";
u "MLY_parser2";

useH "Parser.grm";
use "Holmake/Lexer.lex.sml";

use "Holmake/Holdep.sml";
use "Holmake/Holmake.sml";

val _ = PolyML.export ("Holmake/Holmake", Holmake.main);

