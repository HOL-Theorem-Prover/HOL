val _ = PolyML.SaveState.loadState "../../../bin/hol.state";

val _ = load "regexpLib";

open Lib regexpMisc;

val justifyDefault = regexpLib.SML;

fun finalsString list =
 let val spreadList = spreadln {sep=",", ln="\n     ", width=10} (map Bool.toString list)
 in
   String.concat ("Vector.fromList\n    [" :: spreadList @ ["]"])
 end;

fun array256String intList =
 let val spreadList = spreadln {sep=",", ln="\n     ", width=31} (map Int.toString intList)
 in
   String.concat ("[":: spreadList @ ["]"])
 end

fun twoDarrayString intLists =
  let val arrays = map array256String intLists
  in String.concat
      ((" Vector.fromList (List.map Vector.fromList\n    ["::spread ",\n    " arrays) @ ["])"])
  end;

fun MLfile name quote (_,finals,table) =
 let val nstates = List.length finals
 in String.concat
 ["(*---------------------------------------------------------------------------\n",
  " * DFA ", name, " is the compiled form of regexp\n",
  " *\n",
  " *   ", quote, "\n",
  " *\n",
  " * Number of states in DFA: ",Int.toString nstates, "\n",
  " *\n",
  " *---------------------------------------------------------------------------*)\n",
  "\n",
  "val ", name, " = let\n",
  " val FINALS =\n  ",finalsString finals, "\n ",
  " val DELTA =\n  ", twoDarrayString table, "\n ",
  "  fun step state char = Vector.sub(Vector.sub(DELTA,state),Char.ord char)\n",
  " in\n",
  "   fn s =>\n",
  "    let val len = String.size s\n",
  "        fun steps state i =\n",
  "          if i = len then state\n",
  "          else steps (step state (String.sub(s,i))) (i+1)\n",
  "    in\n",
  "      Vector.sub(FINALS,steps 0 0)\n",
  "    end\n",
  " end;\n"
  ]
 end;

fun deconstruct {certificate, final, matchfn, start, table} =
 let fun toList V = List.map (curry Vector.sub V) (upto 0 (Vector.length V - 1))
 in (start, toList final, toList (Vector.map toList table))
 end;

(*---------------------------------------------------------------------------*)
(* Map to ML and write to stdOut                                           *)
(*---------------------------------------------------------------------------*)

fun string_to_ML justify name s =
 let val regexp = Regexp_Type.fromString s
     val _ = stdErr_print "Parsed regexp, now constructing DFA ... "
     val result = regexpLib.matcher justify regexp
     val _ = stdErr_print "done. Generating ML program.\n"
     val (start,finals,table) = deconstruct result
     val MLstring = MLfile name s (start,finals,table)
 in
   stdOut_print MLstring
 ; regexpMisc.succeed()
 end

(*---------------------------------------------------------------------------*)
(* Parse, transform, write out ML.                                           *)
(*---------------------------------------------------------------------------*)

fun parse_args () =
 let fun printHelp() = stdErr_print
          ("Usage: regexp2ml [-dfagen (HOL | SML)] <name> <quotation>\n")
 in case CommandLine.arguments()
     of ["-dfagen","SML",name,string] => SOME (regexpLib.SML,name,string)
      | ["-dfagen","HOL",name,string] => SOME (regexpLib.HOL,name,string)
      | [name,string] => SOME(justifyDefault, name,string)
      | otherwise    => (printHelp(); NONE)
 end

fun main () =
 let val _ = stdErr_print "regexp2ml: \n"
 in case parse_args()
    of NONE => regexpMisc.fail()
     | SOME (justify,name,string) => string_to_ML justify name string
 end;

