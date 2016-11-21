app load ["regexpLib"];

val justifyDefault = regexpLib.SML;

fun succeed() = OS.Process.terminate OS.Process.success
fun fail()    = OS.Process.terminate OS.Process.failure;

fun stdOut_print s = let open TextIO in output(stdOut,s); flushOut stdOut end;
fun stdErr_print s = let open TextIO in output(stdErr,s); flushOut stdErr end;

fun spread s [] = []
  | spread s [x] = [x]
  | spread s (h1::t) = h1::s::spread s t;

fun bool_to_C true = 1
  | bool_to_C false = 0;

fun arrayString intList = 
 String.concat
   (("{"::spread "," (map Int.toString intList)) @ ["}"]);

fun twoDarrayString intLists = 
  let val arrays = map arrayString intLists
  in String.concat
      (("{"::spread ",\n " arrays) @ ["};"])
  end;

fun Cfile name quote (_,finals,table) = 
 let val nstates = List.length finals
     val finals = map bool_to_C finals
 in String.concat
 ["/*---------------------------------------------------------------------------\n",
  " * -- DFA ", name, " is the compiled form of regexp\n",
  " * --\n",
  " * --   ", quote, "\n",
  " *---------------------------------------------------------------------------*/\n",
  "\n",
  "int ACCEPTING_",name," [", Int.toString nstates,"] = ",arrayString finals, ";\n",
  "\n",
  "unsigned long DELTA_",name," [",Int.toString nstates,"] [256] = \n",
  twoDarrayString table, 
  "\n\n",
  "int match_",name,"(unsigned char *s, int len) {\n",
  "  int state, i;\n",
  "\n",
  "  state = 0;\n",
  "\n",
  "  for (i = 0; i < len; i++) { \n",
  "    state = DELTA_",name,"[state] [s[i]];\n",
  "   }\n",
  "\n",
  "  return ACCEPTING_",name,"[state];\n",
  "}\n"
 ]
 end;

fun deconstruct {certificate, final, matchfn, start, table} = 
 let fun toList V = List.map (curry Vector.sub V) (upto 0 (Vector.length V - 1))
 in (start, toList final, toList (Vector.map toList table))
 end;

(*---------------------------------------------------------------------------*)
(* Map to C and write to stdOut                                              *)
(*---------------------------------------------------------------------------*)

fun quote_to_C justify name q = 
 let val regexp = Regexp_Type.fromString q
     val _ = stdErr_print "Parsed regexp, now constructing DFA (can take time) ..."
     val result = regexpLib.matcher justify regexp
     val _ = stdErr_print "done. Generating C file.\n"
     val (start,finals,table) = deconstruct result
     val Cstring = Cfile name q (start,finals,table)
 in 
   stdOut_print Cstring
 ; succeed()
 end

(*---------------------------------------------------------------------------*)
(* Parse, transform, write to C files.                                    *)
(*---------------------------------------------------------------------------*)

fun parse_args args = 
 let fun printHelp() = stdErr_print 
          ("Usage: regexp2c [-dfagen (HOL | SML)] <name> <quotation>\n")
     val fail = fn () => (printHelp(); fail())
 in case args 
     of ["-dfagen","SML",name,quote] => (regexpLib.SML,name,quote)
      | ["-dfagen","HOL",name,quote] => (regexpLib.HOL,name,quote)
      | [name,quote] => (justifyDefault, name,quote)
      | otherwise => fail()
 end

fun main () = 
 let val _ = stdErr_print "regexp2c: \n"
     val (justify,name,quote) = parse_args(CommandLine.arguments())
     val _ = stdErr_print "command line args parsed.\n"
 in 
   quote_to_C justify name quote
 end;

val _ = PolyML.export("regexp2c",main);
