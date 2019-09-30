structure DFA_Codegen :> DFA_Codegen =
struct

open Lib Feedback regexpMisc;

val ERR = Feedback.mk_HOL_ERR  "DFA_Codegen";

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

 type dfa =
   {name       : string,
    src_regexp : string,
    finals     : bool list,
    table      : int list list}

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
fun Ada {name,src_regexp,finals,table} ostrm =
 let val _ = stdErr_print "Generating code.\n"
     val nstates = List.length finals
     val Uname = Upper name handle e => raise wrap_exn "Ada" "" e
 val string = String.concat
 ["procedure ", Uname, "\nis\n\n",
  "-----------------------------------------------------------------------------\n",
  "-- The following DFA ", name, " is the compiled form of regexp\n",
  "--\n",
  "--   ", src_regexp, "\n",
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
in
 TextIO.output(ostrm,string)
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
fun C {name,src_regexp,finals,table} ostrm =
 let val nstates = List.length finals
     val finals = map bool_to_C finals
 val string = String.concat
 ["/*---------------------------------------------------------------------------\n",
  " * DFA ", name, " is the compiled form of regexp\n",
  " *\n",
  " *    ", src_regexp, "\n",
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
 in
  TextIO.output(ostrm,string)
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
fun SML {name, src_regexp,finals,table} ostrm =
 let val _ = stdErr_print "Generating code.\n"
     val nstates = List.length finals
 val string = String.concat
 ["(*---------------------------------------------------------------------------\n",
  " * DFA ", name, " is the compiled form of regexp\n",
  " *\n",
  " *   ", src_regexp, "\n",
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
 in
   TextIO.output(ostrm,string)
 end
end;


(*---------------------------------------------------------------------------*)
(* Java code. Note: the generated code can run afoul of Java's restriction   *)
(* the size of a method (64K as of 2019) when the table size gets too big.   *)
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
fun Java {name, src_regexp,finals,table} ostrm =
 let val _ = stdErr_print "Generating code.\n"
     val nstates = List.length finals
     val Uname = Upper name handle e => raise wrap_exn "Java" "" e
 val string = String.concat
 ["/*---------------------------------------------------------------------------\n",
  " -- DFA ", name, " is the compiled form of regexp\n",
  " --\n",
  " --   ", src_regexp, "\n",
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
  "  boolean match_",name,"(byte[] input) {\n",
  "    int state = 0;\n",
  "\n",
  "    for (int i = 0; i < input.length; i++) { \n",
  "      state = DELTA_",name,"[state][Byte.toUnsignedInt(input[i])];\n",
  "     }\n",
  "\n",
  "    return ACCEPTING_",name,"[state];\n",
  "  }\n",
  "}\n"
 ]
 in
  TextIO.output(ostrm,string)
 end
end;


end
