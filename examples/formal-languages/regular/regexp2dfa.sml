open Lib regexpMisc regexpLib;

val justifyDefault = regexpLib.SML;

val ERR = Feedback.mk_HOL_ERR  "regexp2dfa";

fun failwithERR e =
  (stdErr_print (Feedback.exn_to_string e);
   regexpMisc.fail());

fun dest_string "" = raise ERR "dest_string" "empty string"
  | dest_string str = 
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

fun check_compset() =
 let fun join (s1,s2) = s2^"."^s1
 in case computeLib.unmapped (regexpLib.regexp_compset())
     of [] => ()
      | check_these =>
         (stdErr_print "Unmapped consts in regexp_compset: \n  ";
          stdErr_print (String.concat
	     (spreadlnWith {sep=", ", ln = "\n  ", width = 5}
                           join check_these));
          stdErr_print "\n\n")
 end


(*---------------------------------------------------------------------------*)
(* Ada code                                                                  *)
(*---------------------------------------------------------------------------*)

local
 fun finalsString nstates list =
 let val spreadList =
      spreadlnWith {sep=",", ln="\n     ", width=10} Bool.toString list
 in
  String.concat
   ["ACCEPTING : constant array (0 .. ", Int.toString (nstates-1), ") of Boolean :=",
    "\n    (", String.concat spreadList, ");"
   ]
 end;

fun array256String intList =
 let val spreadList =
      spreadlnWith {sep=",", ln="\n     ", width=31} Int.toString intList
 in
   String.concat ("(":: spreadList @ [")"])
 end

fun twoDarrayString nstates intLists =
  let val arrays = map array256String intLists
  in String.concat
      ["TABLE : constant array (0 .. ",
       Int.toString (nstates-1), ", 0 .. 255) of Integer :=",
       "\n    (",  String.concat (spread ",\n    " arrays), ");"
      ]
  end;
in
fun Adafile name quote (_,_,finals,table) =
 let val _ = stdErr_print "Generating code.\n"
     val nstates = List.length finals
     val Uname = Upper name handle e => failwithERR e
 in String.concat
 ["procedure ", Uname, "\nis\n\n",
  "-----------------------------------------------------------------------------\n",
  "-- The following DFA ", name, " is the compiled form of regexp\n",
  "--\n",
  "--   ", quote, "\n",
  "--\n",
  "-- Number of states in DFA: ",Int.toString nstates, "\n",
  "--\n",
  "-------------------------------------------------------------------------------\n",
  "\n",
  finalsString nstates finals, "\n\n",
  twoDarrayString nstates table, "\n\n",
  " function Matcher (S : in String) return Boolean\n",
  " is\n",
  "   State : Integer := 0;\n",
  " begin\n",
  "   for I in S'first .. S'last\n",
  "    loop\n",
  "      State := TABLE(State, Character'Pos(S(I)));\n",
  "    end loop;\n",
  "   return ACCEPTING(State);\n",
  " end Matcher;\n\n",
  "begin\n\n",
  "  null;  -- compiler wants a statement here, so here's a trivial one\n\n",
  "end ", Uname, ";\n"
  ]
 end
end;

(*---------------------------------------------------------------------------*)
(* C code                                                                    *)
(*---------------------------------------------------------------------------*)

local
fun bool_to_C true = 1
  | bool_to_C false = 0;

fun finalsString list =
 let val spreadList =
        spreadlnWith {sep=",", ln="\n  ", width=31} Int.toString list
 in
   String.concat ("{" :: spreadList @ ["}"])
 end;

fun array256String intList =
 let val spreadList =
      spreadlnWith {sep=",", ln="\n   ", width=31} Int.toString intList
 in
   String.concat ("{":: spreadList @ ["}"])
 end

fun twoDarrayString intLists =
  let val _ = stdErr_print "Generating code.\n"
      val arrays = map array256String intLists
  in String.concat
      (("{"::spread ",\n " arrays) @ ["};"])
  end;
in
fun Cfile name quote (_,_,finals,table) =
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
 end
end;

(*---------------------------------------------------------------------------*)
(* ML code                                                                   *)
(*---------------------------------------------------------------------------*)

local
 fun finalsString list =
 let val spreadList =
        spreadlnWith {sep=",", ln="\n     ", width=10} Bool.toString list
 in
   String.concat ("Vector.fromList\n    [" :: spreadList @ ["]"])
 end;

fun array256String intList =
 let val spreadList = 
       spreadlnWith {sep=",", ln="\n     ", width=31} Int.toString intList
 in
   String.concat ("[":: spreadList @ ["]"])
 end

fun twoDarrayString intLists =
  let val arrays = map array256String intLists
  in String.concat
      ((" Vector.fromList (List.map Vector.fromList\n    ["
         ::spread ",\n    " arrays) @ ["])"])
  end;
in
fun MLfile name quote (_,_,finals,table) =
 let val _ = stdErr_print "Generating code.\n"
     val nstates = List.length finals
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
 end
end;


(*---------------------------------------------------------------------------*)
(* Java code                                                                 *)
(*---------------------------------------------------------------------------*)

local
fun finalsString list =
 let val spreadList = 
       spreadlnWith {sep=",", ln="\n    ", width=10} Bool.toString list
 in
   String.concat ("{" :: spreadList @ ["}"])
 end;

fun array256String intList =
 let val spreadList = 
       spreadlnWith {sep=",", ln="\n     ", width=31} Int.toString intList
 in
   String.concat ("{":: spreadList @ ["}"])
 end

fun twoDarrayString intLists =
  let val arrays = map array256String intLists
  in String.concat
      (("   {"::spread ",\n    " arrays) @ ["};"])
  end;
in
fun Javafile name quote (_,_,finals,table) =
 let val _ = stdErr_print "Generating code.\n"
     val nstates = List.length finals
     val Uname = Upper name handle e => failwithERR e
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
  "public class ", Uname, " {\n",
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
 end
end;

fun HOLfile name quote (certificate,_,finals,table) =
 case certificate
  of NONE => ""
   | SOME thm => 
     let open HolKernel Drule boolLib bossLib
         val _ = stdErr_print "Generating theorem.\n"
         val eqn = snd(dest_forall(concl thm))
         val (exec_dfa,[finals,table,start,s]) = strip_comb(lhs eqn)
         val name_finals = name^"_finals"
	 val name_table = name^"_table"
	 val name_start = name^"_start"
         val finals_var = mk_var(name_finals,type_of finals)
         val table_var  = mk_var(name_table,type_of table)
         val start_var  = mk_var(name_start,type_of start)
         val finals_def = new_definition(name_finals,mk_eq(finals_var,finals))
         val table_def  = new_definition(name_table,mk_eq(table_var,table))
         val start_def  = new_definition(name_start,mk_eq(start_var,start))
         val thm' = CONV_RULE (BINDER_CONV
                      (LHS_CONV (REWRITE_CONV
                        [GSYM finals_def, GSYM table_def, GSYM start_def])))
                      thm
         val thm'' = LIST_CONJ [thm',table_def, finals_def, start_def]
     in
       Hol_pp.thm_to_string thm''
     end

fun deconstruct {certificate, final, matchfn, start, table} =
 let fun toList V = List.map (curry Vector.sub V) (upto 0 (Vector.length V - 1))
 in (certificate,start, toList final, toList (Vector.map toList table))
 end;

(*---------------------------------------------------------------------------*)
(* Parse, transform, write out code.                                         *)
(*---------------------------------------------------------------------------*)

datatype lang = Ada | C | Java | ML | Thm;

fun parse_args () =
 let fun to_lang s =
      if Lib.mem s ["Ada","ada"] then SOME Ada else
      if Lib.mem s ["C","c"] then SOME C else
      if Lib.mem s ["Java","java"] then SOME Java else
      if Lib.mem s ["ML","SML","ml","sml"] then SOME ML else
      if Lib.mem s ["THM","Thm","thm"] then SOME Thm
      else NONE
     fun check(J,lstring,name,string) =
       case to_lang lstring
        of SOME lang => SOME(J,lang,name,string)
	 | NONE => NONE
 in
    case CommandLine.arguments()
     of ["-dfagen","SML",lstring,name,string] => check(regexpLib.SML,lstring,name,string)
      | ["-dfagen","HOL",lstring,name,string] => check(regexpLib.HOL,lstring,name,string)
      | [lstring,name,string] => check(justifyDefault, lstring, name,string)
      | otherwise  => NONE
 end

fun main () =
 let fun printHelp() = stdErr_print (String.concat
      ["Usage: regexp2dfa [-dfagen (HOL | SML)] ",
       "(Ada | C | Java | ML | Thm) <name> '<regexp>'\n"])
     fun parse_regexp s =
       Regexp_Type.fromString s handle e => failwithERR e
     fun compile_regexp J r =
       regexpLib.matcher J r handle e => failwithERR e
 in
    stdErr_print "regexp2dfa: \n"
(*  ; check_compset() *)
  ; case parse_args()
    of NONE => (printHelp(); regexpMisc.fail())
     | SOME (justify,lang,name,rstring) => 
      let val regexp = parse_regexp rstring
          val _ = stdErr_print "Parsed regexp, now constructing DFA ... "
          val result = compile_regexp justify regexp
          val file_string =
	    (case lang
              of Ada  => Adafile
               | C    => Cfile
               | ML   => MLfile 
               | Java => Javafile 
               | Thm  => HOLfile)
	    name rstring (deconstruct result)
      in
         stdOut_print file_string
       ; regexpMisc.succeed()
      end
end;
