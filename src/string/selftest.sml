(* tests for string and character parsing *)
open HolKernel Parse boolLib bossLib
fun q (QUOTE s) = "Q\"" ^ String.toString s ^ "\""
  | q (ANTIQUOTE a) = "AQ"

fun printq [] = ""
  | printq [x] = q x
  | printq (x::xs) = q x ^ " " ^ printq xs

open stringSyntax
val testdata = [(`#"("`, fromMLchar #"("),
                (`"\n^`)"`, fromMLstring "\n`)"),
                (`"foo\
    \bar"`, fromMLstring "foobar"),
                (`"foo\n\
\bar"`, fromMLstring "foo\nbar"),
                (`[#"c"]`, listSyntax.mk_list ([fromMLchar #"c"], ``:char``))]

fun do_test (q,res) = let
  val _ = print (StringCvt.padRight #" " 40 (printq q))
  val _ = print (StringCvt.padRight #" " 25 ("``" ^ term_to_string res ^ "``"))
in
  if aconv (Term q) res then print "OK\n"
  else (print "FAILED!\n"; OS.Process.exit OS.Process.failure)
end

val _ = app do_test testdata

val foo =
 Define
  `foo = [#"\n"; #" "; #"!"; #"\""; #"#";
          #"$"; #"%"; #"&"; #"'"; #"("; #")";
          #"*"; #"+"; #";"; #"-"; #"."; #"/";
          #"0"; #"1"; #"2"; #"3"; #"4"; #"5";
          #"6"; #"7"; #"8"; #"9"; #":"; #";";
          #"<"; #"="; #">"; #"?"; #"@"; #"A";
          #"B"; #"C"; #"D"; #"E"; #"F"; #"G";
          #"H"; #"I"; #"J"; #"K"; #"L"; #"M";
          #"N"; #"O"; #"P"; #"Q"; #"R"; #"S";
          #"T"; #"U"; #"V"; #"W"; #"X"; #"Y";
          #"Z"; #"["; #"\\"; #"]"; #"^^"; #"_";
          #"^`"; #"a"; #"b"; #"c"; #"d"; #"e";
          #"f"; #"g"; #"h"; #"i"; #"j"; #"k";
          #"l"; #"m"; #"n"; #"o"; #"p"; #"q";
          #"r"; #"s"; #"t"; #"u"; #"v"; #"w";
          #"x"; #"y"; #"z"; #"{"; #"|"; #"}";
          #"~"]`;

val bar = Define`
  bar = EXPLODE "\n !\"#$%&'()*+;-./0123456789:;<=>?@\
                \ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^^_^`\
                \abcdefghijklmnopqrstuvwxyz{|}~"
`

val testthm = prove(``foo = bar``, SRW_TAC [][foo,bar]);

(* ----------------------------------------------------------------------
    string_eq_conv
   ---------------------------------------------------------------------- *)

open boolSyntax
val sec_data = [(``"" = ""``, T),
                (``"" = "a"``, F),
                (``"a" = "b"``, F),
                (``"a" = "a"``, T),
                (``"abc" = "ab"``, F)]

fun sectest (t1, rest) = let
  val _ = print (StringCvt.padRight #" " 40 (term_to_string t1))
  val (actual, ok) = let
    val res = rhs (concl (stringLib.string_EQ_CONV t1))
  in
    (term_to_string res, aconv res rest)
  end handle _ => ("EXN", false)
in
  print (StringCvt.padRight #" " 25 actual);
  if ok then print "OK\n" else (print "FAILED!\n";
                                OS.Process.exit OS.Process.failure)
end

val _ = app sectest sec_data

fun tprint s = print (StringCvt.padRight #" " 65 (s ^ " ... "))

fun tpp s = let
  val t = Parse.Term [QUOTE s]
  val _ = tprint ("Printing of `"^s^"`")
  val res = term_to_string t
in
  if res = s then print "OK\n"
  else (print "FAILED!\n"; Process.exit Process.failure)
end

val _ = app tpp ["P \"a\" /\\ Q",
                 "P (STRCAT a \"b\") /\\ Q",
                 "#\"a\""]


val _ = OS.Process.exit OS.Process.success




