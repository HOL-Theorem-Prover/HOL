PolyML.print_depth 0;
use "Systeml.sig";
use "../../tools-poly/Holmake/Systeml.sml";
use "../../tools-poly/poly/Binaryset.sig";
use "../../tools-poly/poly/Binaryset.sml";
use "../../tools-poly/poly/Binarymap.sig";
use "../../tools-poly/poly/Binarymap.sml";
use "../../tools-poly/poly/Listsort.sig";
use "../../tools-poly/poly/Listsort.sml";
use "regexpMatch.sig";
use "regexpMatch.sml";
use "parse_glob.sig";
use "parse_glob.sml";
use "internal_functions.sig";
use "internal_functions.sml";
print "Testing\n";
fun column_print (s1, s2, s3, s4) =
    StringCvt.padRight #" " 30 s1 ^
    StringCvt.padRight #" " 20 s2 ^
    StringCvt.padRight #" " 10 s3 ^
    s4 ^ "\n";

print (column_print ("Regexp", "String", "Result", "Verdict"));
print (column_print ("------", "------", "------", "-------"));
open parse_glob regexpMatch;

val had_a_bad = ref false

fun test (restr, tests) = let
  val re = parse_glob restr
  val m = match re
  fun dotest (s, expected) = let
    val res = m s
  in
    print (column_print (restr, s, Bool.toString res,
                         if res = expected then "OK"
                         else (had_a_bad := true; "BAD!!")))
  end
in
  app dotest tests
end;

fun symbtest s =
    case parse_glob s of
        Symbs cset => implode (Binaryset.listItems cset)
      | _ => "not a symbs";

app test [
  ("fo", [("fo", true), ("f", false), ("o", false), ("", false),
          ("foo", false), ("of", false)]),
  ("for", [("fo", false), ("f", false), ("o", false), ("", false),
          ("foo", false), ("of", false), ("for", true),
          ("fort", false)]),
  ("f*", [("fo", true), ("f", true), ("o", false), ("", false),
          ("foo", true), ("of", false)]),
  ("*", [("fo", true), ("f", true), ("o", true), ("", true),
         ("foo", true), ("of", true)]),
  ("*o", [("fo", true), ("f", false), ("o", true), ("", false),
          ("foo", true), ("of", false)]),
  ("*o*", [("fo", true), ("f", false), ("o", true), ("", false),
           ("foo", true), ("of", true)]),
  ("?o", [("fo", true), ("f", false), ("o", false), ("", false),
          ("foo", false), ("of", false), ("?o", true)]),
  ("?o?", [("fo", false), ("f", false), ("o", false), ("", false),
           ("foo", true), ("of", false), ("?o", false)]),
  ("[ab]", [("a", true), ("b", true), ("c", false), ("ab", false),
            ("", false)]),
  ("[a]", [("a", true), ("b", false), ("c", false), ("ab", false),
           ("", false)]),
  ("[^a]", [("a", false), ("b", true), ("c", true), ("ab", false),
            ("", false)]),
  ("[^ab]", [("a", false), ("b", false), ("c", true), ("ab", false),
             ("", false)]),
  ("[]]", [("a", false), ("[", false), ("]", true), ("[a", false)]),
  ("[]^]", [("a", false), ("[", false), ("]", true), ("[a", false),
            ("^", true), ("]^", false)]),
  ("[^]]", [("a", true), ("[", true), ("]", false), ("[a", false),
            ("^", true), ("]^", false)]),
  ("[-a]", [("a", true), ("[", false), ("]", false), ("[a", false),
            ("^", false), ("]^", false), ("-", true)]),
  ("[a-z]", [("a", true), ("z", true), ("b", true), ("A", false),
             ("[", false), ("]", false), ("[a", false),
             ("^", false), ("]^", false), ("-", false)]),
  ("[Aa-z]", [("a", true), ("z", true), ("b", true), ("A", true),
              ("[", false), ("]", false), ("[a", false),
              ("^", false), ("]^", false), ("-", false)]),
  ("[a-zA]", [("a", true), ("z", true), ("b", true), ("A", true),
              ("[", false), ("]", false), ("[a", false),
              ("^", false), ("]^", false), ("-", false)]),
  ("[Ba-zA]", [("a", true), ("z", true), ("b", true), ("A", true),
               ("B", true), ("C", false),
               ("[", false), ("]", false), ("[a", false),
               ("^", false), ("]^", false), ("-", false)]),
  ("[A-Za-z]", [("a", true), ("z", true), ("b", true), ("A", true),
                ("B", true), ("C", true),
                ("[", false), ("]", false), ("[a", false),
                ("^", false), ("]^", false), ("-", false)]),
  ("[^A-Za-z]", [("a", false), ("z", false), ("b", false), ("A", false),
                 ("B", false), ("C", false),
                 ("[", true), ("]", true), ("[a", false),
                 ("^", true), ("]^", false), ("-", true)]),
  ("[!A-Za-z]", [("a", false), ("z", false), ("b", false), ("A", false),
                 ("B", false), ("C", false),
                 ("[", true), ("]", true), ("[a", false),
                 ("^", true), ("]^", false), ("-", true)]),
  ("[A-Z][a-z]", [("Bb", true), ("B", false), ("C]", false), ("", false)]),
  ("[A-]", [("A", true), ("-", true), ("", false), ("A-", false)]),
  ("[]-f]", [("a", true), ("^", true), ("]", true), ("", false),
             ("A-", false)]),
  ("[--4]", [(".", true), ("3", true), ("+", false)]),
  ("[^-4]", [(".", true), ("3", true), ("+", true), ("-", false)]),
  ("[_-b^]", [("_", true), ("3", false), ("+", false), ("^", true)]),
  ("[?]", [("?", true), ("", false), ("a", false), ("ab", false)]),
  ("[A-", [("A", false), ("[", false), ("[A-", true)]),
  ("[A?", [("A", false), ("[", false), ("[A-", true)]),
  ("[A?*", [("A", false), ("[", false), ("[A-", true), ("[A-B]", true)]),
  ("[[]", [("A", false), ("[", true), ("[A-", false), ("[A-B]", false)]),
  ("[[-c]", [("A", false), ("[", true), ("b", true), ("]", true)]),
  ("[[c]", [("A", false), ("[", true), ("b", false), ("]", false),
            ("c", true)]),
  ("[[:alpha:]][[:digit:]]",
   [("A9", true), ("A0", true), ("aa", false), ("a", false), ("", false),
    ("a8", true)]),
  ("[[:alpha:]_]", [("A9", false), ("A0", false), ("aa", false),
                    ("a", true), ("_", true), ("A", true)]),
  ("[[:alpha:]-#]", [("A9", false), ("A0", false), ("aa", false),
                     ("a", true), ("-", true), ("#", true)]),
  ("[[:alpha:]09]", [("A9", false), ("A0", false), ("aa", false),
                     ("a", true), ("-", false), ("#", false),
                     ("0", true), ("2", false), ("9", true)]),
  ("[[:alpha:][:digit:]]", [("0", true), ("a", true), ("_", false)]),
  ("[a-z-#]", [("a", true), ("b", true), ("z", true), ("#", true),
               ("&", false), ("-", true)]),

  (* note failure to include trailing :, turning this into a two
     character r.e., where the first character must be one of
     '[', ':', 'a', 'l', 'p', 'h', and the second character must be ']'
  *)
  ("[[:alpha]]", [(":]", true), ("a]", true), ("z", false),
                  ("p]", true)]),

  (* in this case, the parsing of the class block fails, so it has to
     be re-interpreted as a literal [ followed by a class containing
     ':', 'a', 'l', 'p' and 'h'. *)
  ("[[:alpha:]", [("[[:alpha:]", false), ("", false), ("a", false),
                  ("[a", true), ("[:", true)]),

  ("\\[a]", [("[a]", true), ("a", false)]),
  ("\\?", [("a", false), ("?", true)]),
  ("\\", [("a", false), ("?", false), ("", false), ("\\", true)]),
  ("\\*", [("a", false), ("?", false), ("", false), ("*", true)]),
  ("\\]", [("\\]", false), ("]", true)]),
  ("\\\\a", [("\\a", true), ("\\\\a", false), ("a", false)])
];

if !had_a_bad then print "\n*** BAD THINGS HAPPENED ***\n" else ();
PolyML.print_depth 100;
