val _ = PolyML.SaveState.loadState "../../../bin/hol.state";

val _ = load "regexpLib";

open Lib regexpMisc;

val justifyDefault = regexpLib.SML;

fun bool_to_C true = 1
  | bool_to_C false = 0;

fun finalsString list =
 let val spreadList = spreadln {sep=",", ln="\n  ", width=31} (map Int.toString list)
 in
   String.concat ("{" :: spreadList @ ["}"])
 end;

fun array256String intList =
 let val spreadList = spreadln {sep=",", ln="\n   ", width=31} (map Int.toString intList)
 in
   String.concat ("{":: spreadList @ ["}"])
 end

fun twoDarrayString intLists =
  let val arrays = map array256String intLists
  in String.concat
      (("{"::spread ",\n " arrays) @ ["};"])
  end;

fun Cfile name quote (_,finals,table) =
 let val nstates = List.length finals
     val finals = map bool_to_C finals
 in String.concat
 ["/*---------------------------------------------------------------------------\n",
  " * DFA ", name, " is the compiled form of regexp\n",
  " *\n",
  " *    ", quote, "\n",
  " * \n",
  " * Number of states in DFA: ",Int.toString nstates, "\n",
  " *\n",
  " *---------------------------------------------------------------------------*/\n",
  "\n",
  "int ACCEPTING_",name," [", Int.toString nstates,"] =\n ",finalsString finals, ";\n",
  "\n",
  "unsigned long DELTA_",name," [",Int.toString nstates,"] [256] = \n ",
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

fun string_to_C justify name s =
 let val regexp = Regexp_Type.fromString s
     val _ = stdErr_print "Parsed regexp, now constructing DFA ... "
     val result = regexpLib.matcher justify regexp
     val _ = stdErr_print "done. Generating C.\n"
     val (start,finals,table) = deconstruct result
     val Cstring = Cfile name s (start,finals,table)
 in
   stdOut_print Cstring
 ; regexpMisc.succeed()
 end

(*---------------------------------------------------------------------------*)
(* Parse, transform, write out C.                                            *)
(*---------------------------------------------------------------------------*)

fun parse_args () =
 let fun printHelp() = stdErr_print
          ("Usage: regexp2c [-dfagen (HOL | SML)] <name> <quotation>\n")
 in case CommandLine.arguments()
     of ["-dfagen","SML",name,string] => SOME (regexpLib.SML,name,string)
      | ["-dfagen","HOL",name,string] => SOME (regexpLib.HOL,name,string)
      | [name,string] => SOME(justifyDefault, name,string)
      | otherwise     => (printHelp(); NONE)
 end

fun main () =
 let val _ = stdErr_print "regexp2c: \n"
 in case parse_args()
    of NONE => regexpMisc.fail()
     | SOME (justify,name,string) => string_to_C justify name string
 end;

