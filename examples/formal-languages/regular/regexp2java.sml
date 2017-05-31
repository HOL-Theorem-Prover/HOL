val _ = PolyML.SaveState.loadState "../../../bin/hol.state";

val _ = load "regexpLib";

open Lib regexpMisc;

val justifyDefault = regexpLib.SML;

fun dest_string str =
 if String.size str = 0
   then (stdErr_print "name parameter is an empty string"; regexpMisc.fail())
   else
     let val c = String.sub(str,0)
         val t = String.substring(str,1,String.size str - 1)
     in (c,t)
     end

fun Upper str =
 let open Char
     val (c,t) = dest_string str
 in if isUpper c then str
    else String.concat [toString(toUpper c), t]
 end;

fun finalsString list =
 let val spreadList = spreadln {sep=",", ln="\n    ", width=10} (map Bool.toString list)
 in
   String.concat ("{" :: spreadList @ ["}"])
 end;

fun array256String intList =
 let val spreadList = spreadln {sep=",", ln="\n     ", width=31} (map Int.toString intList)
 in
   String.concat ("{":: spreadList @ ["}"])
 end

fun twoDarrayString intLists =
  let val arrays = map array256String intLists
  in String.concat
      (("   {"::spread ",\n    " arrays) @ ["};"])
  end;

fun Javafile name quote (_,finals,table) =
 let val nstates = List.length finals
 in String.concat
 ["/*---------------------------------------------------------------------------\n",
  " -- DFA ", name, " is the compiled form of regexp\n",
  " --\n",
  " --   ", quote, "\n",
  " --\n",
  " -- Number of states in DFA: ",Int.toString nstates, "\n",
  " --\n",
  " *---------------------------------------------------------------------------*/\n",
  "\n",
  "public class ", Upper name, " {\n",
  "  boolean ACCEPTING_",name," [] =\n   ",finalsString finals, ";\n",
  "\n",
  "  int DELTA_",name,"[][] = \n",
  twoDarrayString table,
  "\n\n",
  "  boolean match_",name,"(String s) {\n",
  "    int state = 0;\n",
  "\n",
  "    for (int i = 0; i < s.length(); i++) { \n",
  "      state = DELTA_",name,"[state][s.charAt(i)];\n",
  "     }\n",
  "\n",
  "    return ACCEPTING_",name,"[state];\n",
  "  }\n",
  "}\n"
 ]
 end;

fun deconstruct {certificate, final, matchfn, start, table} =
 let fun toList V = List.map (curry Vector.sub V) (upto 0 (Vector.length V - 1))
 in (start, toList final, toList (Vector.map toList table))
 end;

(*---------------------------------------------------------------------------*)
(* Map to Java and write to stdOut                                           *)
(*---------------------------------------------------------------------------*)

fun string_to_Java justify name s =
 let val regexp = Regexp_Type.fromString s
     val _ = stdErr_print "Parsed regexp, now constructing DFA ... "
     val result = regexpLib.matcher justify regexp
     val _ = stdErr_print "done. Generating Java program.\n"
     val (start,finals,table) = deconstruct result
     val Javastring = Javafile name s (start,finals,table)
 in
   stdOut_print Javastring
 ; regexpMisc.succeed()
 end

(*---------------------------------------------------------------------------*)
(* Parse, transform, write out Java.                                         *)
(*---------------------------------------------------------------------------*)

fun parse_args () =
 let fun printHelp() = stdErr_print
          ("Usage: regexp2java [-dfagen (HOL | SML)] <name> <quotation>\n")
 in case CommandLine.arguments()
     of ["-dfagen","SML",name,string] => SOME (regexpLib.SML,name,string)
      | ["-dfagen","HOL",name,string] => SOME (regexpLib.HOL,name,string)
      | [name,string] => SOME(justifyDefault, name,string)
      | otherwise    => (printHelp(); NONE)
 end

fun main () =
 let val _ = stdErr_print "regexp2java: \n"
 in case parse_args()
    of NONE => regexpMisc.fail()
     | SOME (justify,name,string) => string_to_Java justify name string
 end;

