open arithmeticTheory HolKernel boolLib Parse testutils

val _ = new_theory "scratch"

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
  val res = term_to_string ``foo(x,y)`` handle Fail _ => ""
in
  if res <> "" then OK() else fail()
end

val _ = let
  val tpp = let open testutils
            in
              unicode_off (raw_backend testutils.tpp)
            end
  val firstbar_tpp = HOLFlags.with_bflags [(term_pp.print_firstcasebar, true)] tpp
in
  List.app tpp [
    "case e1 of 0 => (case e2 of 0 => 1 | SUC n => n + 1) | SUC m => m * 2",
    "case e1 of 0 => 1 | SUC n => case e2 of 0 => 2 | SUC m => 3",
    "(case x of 0 => (\\x. x) | SUC n => (\\m. m + n)) y",
    "!a b c d e f g.\n\
    \  foo' a b /\\ bar a c /\\ baz a c d /\\ qux f g /\\ foo' f g ==>\n\
    \  a + b * c = 10 * d + e + f + g"
  ] ;
  firstbar_tpp "case e of | 0 => 1 | SUC n => n + 2";
  firstbar_tpp
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
                 (HOLFlags.with_bflags [(Parse.show_assums, true)]
                                       thm_to_string)
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

(* ----------------------------------------------------------------------
    A message sent down the MESG channel keeps its terms

    `src/parse' has the other `Msg' tests, but it is built before
    `boolTheory' and so has no constants to render; this is the first
    directory with real ones.
   ---------------------------------------------------------------------- *)

(* The point of `HOLmessage.message' is that the *reader* picks the
   back end, so one message serves a terminal and a structured front
   end alike.  `HOL_MESGm' flattens for `MESG_outstream', which is all
   a terminal wants, and that flattening runs through
   `HOLmessage.plain_renderer', which pins `raw_terminal' -- so no
   choice of `Parse.current_backend' at the call site can reach behind
   it, and the channel's text can never be the rich rendering.  A
   consumer that wants what the terms are needs the message itself,
   which is what `MESG_hook' offers it.

   The term here is built by the real parser and rendered by the real
   printer, unlike the hand-assembled `pretty' in `src/parse's back
   end tests.  That is the half that could rot unnoticed: `pp_term'
   has to be emitting `FV' and `Const' annotations for any of this to
   carry a type. *)
local
  val t = ``x + 1``
  val m = Msg.^^ (Msg.txt "about ", Msg.tm t)
  (* One call, both renderings: what the channel got, and what the
     hook was offered. *)
  val plain = ref ([] : string list)
  val seen = ref (NONE : Msg.message option)
  val () =
    Lib.with_flag (Feedback.MESG_hook, (fn msg => seen := SOME msg))
      (fn () =>
        Lib.with_flag (Feedback.MESG_outstream, (fn s => plain := s :: !plain))
          (fn () =>
            Lib.with_flag (Feedback.MESG_to_string, (fn s => s))
              (fn () => Feedback.HOL_MESGm m) ()) ()) ()
  val emitted = String.concat (List.rev (!plain))
  fun segs () = Msg.segments (valOf (!seen))
  fun find k = List.find (fn {kind, ...} => kind = k) (segs ())
in

val _ = tprint "HOL_MESGm offers the message, not just its text"
val _ = case !seen of SOME _ => OK() | NONE => die "the hook saw nothing"

val _ = tprint "the channel's own text stays plain"
val _ = if emitted = "about x + 1" then OK()
        else die ("got " ^ String.toString emitted)

val _ = tprint "a term in a MESG renders with its variable's type"
val _ =
    case find "fv" of
        NONE => die ("no free variable marked in " ^
                     String.concat (map #text (segs ())))
      | SOME {text, ty, ...} =>
        if text = "x" andalso String.isSubstring "num" ty then OK()
        else die ("got " ^ text ^ " : " ^ ty)

val _ = tprint "and with its constant's theory-qualified name and type"
val _ =
    case find "const" of
        NONE => die ("no constant marked in " ^
                     String.concat (map #text (segs ())))
      | SOME {name, ty, ...} =>
        if name = "arithmetic$+" andalso ty = "num -> num -> num" then OK()
        else die ("got " ^ name ^ " : " ^ ty)

(* Both renderings are of one message, so a consumer that lays the
   channel's text down and decorates it from the segments can do so by
   arithmetic rather than by searching the text for the terms. *)
val _ = tprint "the rich rendering and the channel's text agree"
val _ =
    let val rejoined = String.concat (List.map #text (segs ()))
    in
      if rejoined = emitted then OK()
      else die ("segments give " ^ String.toString rejoined ^
                " but the channel got " ^ String.toString emitted)
    end
end
