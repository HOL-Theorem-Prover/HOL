open Lib regexpMisc regexpLib;

val justifyDefault = regexpLib.SML;

val ERR = Feedback.mk_HOL_ERR  "regexp2dfa";

fun failwithERR e =
  (stdErr_print (Feedback.exn_to_string e);
   regexpMisc.fail());

fun HOLfile name quote (certificate,_,finals,table) =
 case certificate
  of NONE => ""
   | SOME thm =>
     let open HolKernel Drule boolLib bossLib
         val _ = stdErr_print "Generating HOL theorem.\n"
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

(*---------------------------------------------------------------------------*)
(* Parse, transform, write out code.                                         *)
(*---------------------------------------------------------------------------*)

datatype lang = Ada | C | Java | Sml | Thm;

fun parse_args () =
 let fun to_lang s =
      if Lib.mem s ["ADA", "Ada","ada"] then SOME Ada else
      if Lib.mem s ["C","c"] then SOME C else
      if Lib.mem s ["JAVA", "Java","java"] then SOME Java else
      if Lib.mem s ["ML","SML","Ml", "Sml","ml","sml"] then SOME Sml else
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

fun deconstruct {certificate, final, matchfn, start, table, aux} =
 let fun toList V = List.map (curry Vector.sub V) (upto 0 (Vector.length V - 1))
 in (certificate,start, toList final, toList (Vector.map toList table))
 end;

fun main () =
 let fun printHelp() = stdErr_print (String.concat
      ["Usage: regexp2dfa [-dfagen (HOL | SML)] ",
       "(Ada | C | Java | Sml | Thm) <name> '<regexp>'\n"])
     fun parse_regexp s =
       Regexp_Type.fromString s handle e => failwithERR e
     fun compile_regexp J r =
       regexpLib.gen_dfa J r handle e => failwithERR e
 in
    stdErr_print "regexp2dfa: \n"
  ; case parse_args()
    of NONE => (printHelp(); regexpMisc.fail())
     | SOME (justify,lang,name,rstring) =>
      let val regexp = parse_regexp rstring
          val _ = stdErr_print "Parsed regexp, now constructing DFA ... "
          val (result as (_,_,finals,table)) =
                 deconstruct (compile_regexp justify regexp)
          val dfa = {name=name,src_regexp=rstring, finals=finals,table=table}
          val ostrm = TextIO.stdOut
      in
         (case lang
           of Ada  => DFA_Codegen.Ada dfa ostrm
            | C    => DFA_Codegen.C dfa ostrm
            | Sml  => DFA_Codegen.SML dfa ostrm
            | Java => DFA_Codegen.Java dfa ostrm
            | Thm  => TextIO.output(ostrm, HOLfile name rstring result))
       ;
         regexpMisc.succeed()
      end
end;
