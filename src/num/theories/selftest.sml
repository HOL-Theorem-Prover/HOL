open arithmeticTheory HolKernel boolLib Parse

fun tprint s = print (StringCvt.padRight #" " 60 s)

fun fail() = (print "FAILED\n"; OS.Process.exit OS.Process.failure)

val _ = tprint "Testing that I can parse num$0"
val _ = (Parse.Term`num$0`; print "OK\n")
        handle HOL_ERR _ => fail()

val _ = tprint "Testing that I can't parse num$1"
val _ = (Parse.Term`num$1`; fail()) handle HOL_ERR _ => print "OK\n";


val _ = tprint "Testing that bool$0 fails"
val _ = (Parse.Term`bool$0`; fail()) handle HOL_ERR _ => print "OK\n"

val _ = tprint "Testing that num$01 fails"
val _ = (Parse.Term`num$01`; fail()) handle HOL_ERR _ => print "OK\n"

val _ = let
  val _ = tprint "Anthony's pattern-overloading bug"
  val b2n_def = new_definition("b2n_def", ``b2n b = if b then 1 else 0``)
  val _ = overload_on ("foo", ``\(x:num#'a),(y:num#'b). b2n (FST x = FST y)``)
  val res = trace ("PP.catch_withpp_err", 0) term_to_string ``foo(x,y)``
            handle Fail _ => ""
in
  if res <> "" then print "OK\n" else fail()
end

val _ = let
  val tpp = let open testutils
            in
              unicode_off (raw_backend testutils.tpp)
            end
in
  List.app tpp [
    "case e1 of 0 => (case e2 of 0 => 1 | SUC n => n + 1) | SUC m => m * 2",
    "case e1 of 0 => 1 | SUC n => case e2 of 0 => 2 | SUC m => 3",
    "(case x of 0 => (\\x. x) | SUC n => (\\m. m + n)) y"
  ]
end



fun colourpp_test (testname, s, expected) =
    testutils.tpp_expected {testf = (fn _ => testname),
                            input = s,
                            output = expected}

val _ = Parse.current_backend := PPBackEnd.vt100_terminal

fun bound s = "\^[[0;32m" ^ s ^ "\^[[0m"
fun free s = "\^[[0;1;34m" ^ s ^ "\^[[0m"
val concat = String.concat

val colourtests =
    [("Pretty-printing of case expression bound variables",
      "case x of 0 => 1 | SUC n => n * 2",
      concat ["case ",free "x"," of 0 => 1 | ", "SUC ", bound "n", " => ",
              bound "n", " * 2"]),
     ("Pretty-printing of case in rand position",
      "f (case x of 0 => 1 | SUC n => n * 2)",
      concat [free "f", " (case ", free "x", " of 0 => 1 | SUC ", bound "n",
              " => ", bound "n", " * 2)"]),
     ("Colouring simple LET", "let x = 3 in x + 1",
      concat ["let ", bound "x", " = 3 in ", bound "x", " + 1"]),
     ("Colouring simple LET with free on right",
      "let x = y + 2 in x * 2",
      concat ["let ", bound "x", " = ", free "y", " + 2 in ", bound "x",
              " * 2"]),
     ("Colouring LET with ands",
      "let x = 10 and y = x + 6 in x + y",
      concat ["let ", bound "x", " = 10 and ", bound "y", " = ", free "x",
              " + 6 in ", bound "x", " + ", bound "y"]),
     ("Colouring LET binding local function",
      "let f x = x * 2 in x + f 10",
      concat ["let ", bound "f", " ", bound "x", " = ", bound "x", " * 2 in ",
              free "x", " + ", bound "f", " 10"])
    ]

val _ = app colourpp_test colourtests
