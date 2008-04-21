fun u f = use ("mlyacclib/" ^ f ^ ".sml");

val _ = u "MLY_base-sig";
val _ = u "MLY_join";
val _ = u "MLY_lrtable";
val _ = u "MLY_stream";
val _ = u "MLY_parser2";

fun u f = use ("src/" ^ f ^ ".sml");

val _ = u "utils-sig";
val _ = u "utils";
val _ = u "sigs";
val _ = u "verbose";
val _ = u "hdr";
val _ = u "yacc-grm-sig";
val _ = u "yacc-grm";
val _ = u "yacc.lex";
val _ = u "parse";
val _ = u "core";
val _ = u "coreutils";
val _ = u "graph";
val _ = u "look";
val _ = u "lalr";
val _ = u "mklrtable";
val _ = u "grammar";
val _ = u "mkprstruct";
val _ = u "shrink";
val _ = u "absyn-sig";
val _ = u "yacc";
val _ = u "absyn";
val _ = u "link";
val _ = u "main";

fun main () = main.main (CommandLine.arguments ());

val _ = PolyML.shareCommonData main;
val _ = PolyML.export ("mlyacc", main);


