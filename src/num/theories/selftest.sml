open arithmeticTheory HolKernel boolLib Parse testutils

fun fail() = die "FAILED\n"

val _ = tprint "Testing that I can parse num$0"
val _ = (Parse.Term`num$0`; OK())
        handle HOL_ERR _ => fail()

val _ = tprint "Testing that I can't parse num$1"
val _ = (Parse.Term`num$1`; fail()) handle HOL_ERR _ => OK();


val _ = tprint "Testing that bool$0 fails"
val _ = (Parse.Term`bool$0`; fail()) handle HOL_ERR _ => OK()

val _ = tprint "Testing that num$01 fails"
val _ = (Parse.Term`num$01`; fail()) handle HOL_ERR _ => OK()

val _ = let
  val _ = tprint "Anthony's pattern-overloading bug"
  val b2n_def = new_definition("b2n_def", ``b2n b = if b then 1 else 0``)
  val _ = overload_on ("foo", ``\(x:num#'a),(y:num#'b). b2n (FST x = FST y)``)
  val res = trace ("PP.catch_withpp_err", 0) term_to_string ``foo(x,y)``
            handle Fail _ => ""
in
  if res <> "" then OK() else fail()
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
    "(case x of 0 => (\\x. x) | SUC n => (\\m. m + n)) y",
    "!a b c d e f g.\n\
    \  foo' a b /\\ bar a c /\\ baz a c d /\\ qux f g /\\ foo' f g ==>\n\
    \  a + b * c = 10 * d + e + f + g"
  ] ;
  trace ("PP.print_firstcasebar", 1) tpp "case e of | 0 => 1 | SUC n => n + 2";
  trace ("PP.print_firstcasebar", 1) tpp
    "case f e n longvarname of\n\
    \| 0 => superlongvarname * secondsuperlongname + 1\n\
    \| SUC n => n + 2"
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
    [("&3 should print as 3", "&3", "3"),
     ("Pretty-printing of case expression bound variables",
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

fun good_oneline th =
    null (hyp th) andalso
    (let val cs = strip_conj (concl th)
     in
       length cs = 1 andalso is_eq (hd cs)
     end)

fun test msg th =
    (tprint ("one_line_ify on " ^ msg);
     require_msg (check_result good_oneline)
                 (trace("assumptions", 1) thm_to_string)
                 (DefnBase.one_line_ify NONE) th)
val _ = test "cv_sub_def" cvTheory.cv_sub_def

open groundEval numeralTheory

val _ = overload_on ("B1", ``BIT1``);
val _ = overload_on ("B2", ``BIT2``);
val _ = overload_on ("iZ", ``numeral$iZ``);
val _ = overload_on ("NUM", ``NUMERAL``)

val ncset = HOLset.addList(empty_tmset,
                           [``NUMERAL``, ``BIT1``, ``BIT2``,
                            ``0:num``, ``ZERO``]);

val ge0 = GE {constrs = ncset, rwts = Net.empty, case_consts = empty_tmset }
val ge = List.foldl (fn (th,ge) => add_rwt th ge) ge0
                    (Rewrite.mk_rewrites numeralTheory.numeral_distrib @
                     Rewrite.mk_rewrites numeralTheory.numeral_add @
                     Rewrite.mk_rewrites numeralTheory.numeral_suc @
                     Rewrite.mk_rewrites numeralTheory.numeral_iisuc)

fun dot t = reduction ge (vTreeOf ge t) t (Conv (fn x => x));
fun testdot t expected = let
  val _ = tprint ("dot test: "^term_to_string t)
  fun check result =
      aconv (result_term result) expected andalso
      result_tree result = KnownValue
in
  require (check_result check) dot t
end;

val _ = testdot ``1 + 1`` ``2``;
val _ = testdot ``2 + 1`` ``3``;
val _ = testdot ``3 + 4`` ``7``;
val _ = testdot ``4 + 5 + 9`` ``18``;

val _ = testdot ``(\x. x + y) 5`` ``5 + y``;
val _ = testdot ``(\x. x + x + 1) ((\y. y + 10) 4)`` ``29``;

