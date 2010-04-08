(* this is an -*- sml -*- file, more or less *)
open mungeTools
type lexresult = unit
val linecount = ref 1;
val cpos = ref 1;
fun eof () = OS.Process.exit (if !numErrors > 0 then OS.Process.failure
                              else OS.Process.success)

fun mk_ECHO ostr s = (TextIO.output(ostr, s); TextIO.flushOut ostr);
val ECHO = mk_ECHO TextIO.stdOut
fun ERR s = let in
  mk_ECHO TextIO.stdErr (s^"\n");
  numErrors := !numErrors + 1;
  "MUNGER ERROR "^(Int.toString (!numErrors))
end
local open String in
  fun inside s = substring(s, 1, size s - 2)
end
local
  open Substring
  fun u p s = if isEmpty s then concat (rev p) else let
        val (pref,suff) = position "\\}" s
        in
          u (pref::p) (triml 1 suff)
        end
in
  fun unescape s = u [] (full s)
end
val width = ref 63

fun replace (pos, argpos, comm, optstring, args) = let
  val optset = parseOpts pos optstring
  val width = case optset_width optset of
                SOME w => w
              | NONE => !width
in
  TextIO.output(TextIO.stdOut,
                PP.pp_to_string width replacement
                                {commpos = pos, argpos = argpos,
                                 command = comm,
                                 options = optset,
                                 argument = unescape args})
end

fun getparts s = let
  open Substring
  val ss = full s
  val (preposn, posnsfx) = position "[" ss
  val (opstring, rest, argoffset) =
      if size posnsfx = 0 then let
          val (argpfx, argstart) = position "{" ss
        in
          ("", argstart, size argpfx)
        end
      else let
          val (opstuff, rest) = position "]" posnsfx
        in
          (string (slice(opstuff,1,NONE)),
           slice(rest,1,NONE),
           size opstuff + size preposn + 1)
        end
in
  (opstring, inside (string rest), argoffset)
end
%%
%structure mungeLex

args = "{"("\\}"|[^}])+"}";
options = "["[^\]]*"]";

%%
<INITIAL>"\\HOLtm" {options}? {args} =>
  (let val (optstring, args, argpos) = getparts yytext
   in
     replace ((!linecount, !cpos),(!linecount, !cpos + argpos),
              Term, optstring, args);
     cpos := !cpos + size yytext;
     lex()
   end);
<INITIAL>"\\HOLthm" {options}? {args} =>
  (let val (optstring, args, argpos) = getparts yytext
   in
     replace ((!linecount, !cpos), (!linecount, !cpos + argpos),
              Theorem, optstring, args);
     cpos := !cpos + size yytext;
     lex()
   end);
<INITIAL>"\\HOLty"  {options}? {args} =>
  (let val (optstring, args, argpos) = getparts yytext
   in
     replace ((!linecount, !cpos), (!linecount, !cpos + argpos),
              Type, optstring, args);
     cpos := !cpos + size yytext;
     lex()
   end);
<INITIAL>"\n" => (ECHO "\n";
                  linecount := !linecount + 1;
                  cpos := 1;
                  lex());
<INITIAL>. => (ECHO yytext; cpos := !cpos + 1; lex());
