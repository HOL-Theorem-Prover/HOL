fun u f = use ("mlyacclib/" ^ f ^ ".sml");

u "MLY_base-sig";
u "MLY_join";
u "MLY_lrtable";
u "MLY_stream";
u "MLY_parser2";

fun u f = use ("src/" ^ f ^ ".sml");

u "utils-sig";
u "utils";
u "sigs";
u "verbose";
u "hdr";
u "yacc-grm-sig";
u "yacc-grm";
u "yacc.lex";
u "parse";
u "core";
u "coreutils";
u "graph";
u "look";
u "lalr";
u "mklrtable";
u "grammar";
u "mkprstruct";
u "shrink";
u "absyn-sig";
u "yacc";
u "absyn";
u "link";
u "main";


fun main () = main.main (CommandLine.arguments ());

val _ = PolyML.export ("mlyacc", main);


