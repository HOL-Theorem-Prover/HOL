open HolKernel Parse boolTheory boolLib testutils
open monadsyntax parmonadsyntax state_transformerTheory errorStateMonadTheory

val _ = temp_remove_absyn_postprocessor "monadsyntax.transform_absyn"
val _ = temp_remove_user_printer "monadsyntax.print_monads"

val _ = set_trace "Unicode" 0
(* interactive only:
val _ = diemode := FailException
*)

fun udie () = die "FAILED!"

val _ = tprint "Testing parsing of parmonadsyntax"
val bind_t = prim_mk_const{Thy = "state_transformer", Name = "BIND"}
val _ = overload_on ("monad_bind", bind_t)
val _ = set_trace "notify type variable guesses" 0
val t = Term`do x <- f y ; g x od`
val _ = if same_const bind_t (#1 (strip_comb t)) then OK()
        else udie()

val _ = tprint "Testing Q.parsing of parmonadsyntax"
val t = Parse.parse_in_context [] `do x <- f y; g x od`
val _ = if same_const bind_t (#1 (strip_comb t)) then OK()
        else udie()

val _ = tprint "Testing Q-parsing of parmonadsyntax (TYPED-con)"
val t = Parse.parse_in_context [] `do x <- f y; g x od : 'a -> bool # 'a`
val _ = if same_const bind_t (#1 (strip_comb t)) then OK()
        else udie()

val _ = Parse.current_backend := PPBackEnd.vt100_terminal
fun tpp' (s,expected) =
  testutils.tpp_expected {
    input = s, output = expected,
    testf = fn s => "Testing (coloured-)printing of `"^s^"`"
  }

fun bound s = "\^[[0;32m" ^ s ^ "\^[[0m"
fun free s = "\^[[0;1;34m" ^ s ^ "\^[[0m"
val concat = String.concat

val bx = bound "x"
val fy = free "y"
val fp = free "p"
val fx = free "x"

val monadtpp_test1 =
    ("do x <- f y; g x od",
     concat ["do ", bx, " <- ", free "f", " ", fy, "; ", free "g", " ",
             bx, " od"])
val monadtpp_test2 =
    ("do m1; m2 od",
     concat ["do ", free "m1", "; ", free "m2", " od"])

val monadtpp_test3 =
  ("do x <- m1; y <- m2; \
   \if my_very_long_guard then m3 else do a <- very_long_monad1; \
   \b <- very_long_monad2; superLongFinalMonad long_arg od od",
   String.concat [
    "do\n  ",
      bx, " <- ", free "m1", ";\n  ",
      bound "y", " <- ", free "m2", ";\n  ",
      "if ", free "my_very_long_guard", " then ", free "m3", "\n  ",  (* 2 *)
      "else\n    ",
        "do\n      ",                                                 (* 6 *)
          bound "a", " <- ", free "very_long_monad1", ";\n      ",    (* 6 *)
          bound "b", " <- ", free "very_long_monad2", ";\n      ",    (* 6 *)
          free "superLongFinalMonad", " ", free "long_arg", "\n    ", (* 4 *)
        "od\n",                                                       (* 0 *)
    "od"])

val monadtpp_test4 =
    ("do (x:α) <- f (x:α); g x; od",
     String.concat [
       "do ", bx, " <- ", free "f", " ", free "x", "; ",
       free "g", " ", bx, " od"
     ])

val _ = app tpp' [monadtpp_test1, monadtpp_test2, monadtpp_test3,
                  monadtpp_test4]

val _ = clear_overloads_on "monad_bind"

val _ = temp_remove_absyn_postprocessor "parmonadsyntax.transform_absyn"
val _ = temp_remove_user_printer "parmonadsyntax.print_monads"

val _ = temp_add_user_printer ("monadsyntax.print_monads", genvar alpha,
                               monadsyntax.print_monads)
val _ = temp_add_absyn_postprocessor ("monadsyntax.transform_absyn",
                                      monadsyntax.transform_absyn)

val _ = monadsyntax.enable_monad "option"

val _ = unicode_off (raw_backend (trace ("types", 1) testutils.tpp))
                    "do (x :num) <- (s :num option); SOME (x + (1 :num)) od"

val _ = tprint "Testing monadsyntax parse of OPTION_BIND"
val t = ``do x <- opt ; SOME (x + 1) od``
val (f, args) = strip_comb t
val _ = if same_const f ``option$OPTION_BIND`` andalso
           hd args ~~ mk_var("opt", ``:num option``) andalso
           hd (tl args) ~~ ``\x:num. SOME (x + 1)``
        then OK() else udie ()

val _ = tprint "Testing monadsyntax parse of OPTION_IGNORE_BIND"
val t = ``do SOME 3 ; SOME 4 od``
val (f, args) = strip_comb t
val _ = if same_const f ``option$OPTION_IGNORE_BIND`` andalso
           hd args ~~ ``SOME 3`` andalso
           hd (tl args) ~~ ``SOME 4``
        then OK() else udie()

val _ = tprint "Testing parse of mlet in option monad"
val t = ``do mlet x <- y; SOME (x + 1) od``
val (f, args) = strip_comb t
val _ = if same_const f boolSyntax.let_tm andalso
           hd args ~~ ``\x. SOME (x + 1)`` andalso
           hd (tl args) ~~ ``y : num``
        then OK() else udie()

val _ = tprint "Testing parse of mlet in option monad (after bind)"
val t = ``do y <- z; mlet x <- y; SOME (x + 1) od``
val (f, args) = strip_comb t
val _ = if same_const f ``option$OPTION_BIND`` andalso
           hd args ~~ ``z : num option`` andalso
           hd (tl args) ~~ ``\y. let x = y in SOME (x + 1)``
        then OK() else udie()

val _ = tprint "Testing parse of mlet arrow in option monad"
val t = ``do x <<- y; SOME (x + 1) od``
val (f, args) = strip_comb t
val _ = if same_const f boolSyntax.let_tm andalso
           hd args ~~ ``\x. SOME (x + 1)`` andalso
           hd (tl args) ~~ ``y : num``
        then OK() else udie()

val _ = tprint "Testing parse of mlet arrow in option monad (after bind)"
val t = ``do y <- z; x <<- y; SOME (x + 1) od``
val (f, args) = strip_comb t
val _ = if same_const f ``option$OPTION_BIND`` andalso
           hd args ~~ ``z : num option`` andalso
           hd (tl args) ~~ ``\y. let x = y in SOME (x + 1)``
        then OK() else udie()

val mlettpp_test1 =
    ("do mlet (x:α) <- f (x:α); g x; od",
     String.concat [
       "let ", bx, " = ", free "f", " ", free "x", " in ",
       free "g", " ", bx
     ])

val mlettpp_test2 =
    ("do (x:α) <<- f (x:α); g x; od",
     String.concat [
       "let ", bx, " = ", free "f", " ", free "x", " in ",
       free "g", " ", bx
     ])

val mlettpp_test3 =
    ("do a <- b; (x:α) <<- f (x:α); g x; od",
     String.concat [
       "do ", bound "a", " <- ", free "b", "; ",
       bound "x", " <<- ", free "f", " ", free "x", "; ",
       free "g", " ", bx, " od"
     ])

val mlettpp_test4 =
    ("do a <- b; let x = f x in g x; od",
     String.concat [
       "do ", bound "a", " <- ", free "b", "; ",
       bound "x", " <<- ", free "f", " ", free "x", "; ",
       free "g", " ", bx, " od"
     ])

val _ = app tpp' [mlettpp_test1, mlettpp_test2, mlettpp_test3, mlettpp_test4]

val _ = monadsyntax.print_explicit_monadic_lets true;

val mlettpp_test5 =
    ("do a <- b; (x:α) <<- f (x:α); g x; od",
     String.concat [
       "do ", bound "a", " <- ", free "b", "; ",
       "mlet ", bound "x", " <- ", free "f", " ", free "x", "; ",
       free "g", " ", bx, " od"
     ])

val mlettpp_test6 =
    ("do a <- b; let x = f x in g x; od",
     String.concat [
       "do ", bound "a", " <- ", free "b", "; ",
       "mlet ", bound "x", " <- ", free "f", " ", free "x", "; ",
       free "g", " ", bx, " od"
     ])

val _ = app tpp' [mlettpp_test5, mlettpp_test6];

val _ = disable_monad "option"
val _ = declare_monad ("option",
                       {bind = ``OPTION_BIND``, ignorebind = NONE,
                        unit = ``SOME``, fail = SOME ``NONE``,
                        choice = SOME ``OPTION_CHOICE``,
                        guard = SOME ``OPTION_GUARD``})
val _ = enable_monad "option"

val _ = tprint "Testing monadsyntax parse of OPTION_BIND (ignoring)"
val t = ``do SOME 3 ; SOME 4 od``
val (f, args) = strip_comb t
val _ = if same_const f ``option$OPTION_BIND`` andalso
           hd args ~~ ``SOME 3`` andalso
           hd (tl args) ~~ ``K (SOME 4) : num -> num option`` then
          OK() else udie()

val _ = app tpp' [monadtpp_test1, monadtpp_test2, monadtpp_test3,
                  monadtpp_test4]

val _ = disable_monad "option"
val _ = enable_monad "errorState"

val _ = print "Testing with error state monad\n"

val _ = app tpp' [monadtpp_test1, monadtpp_test2, monadtpp_test3]

val _ = current_backend := PPBackEnd.raw_terminal
val _ = testutils.tpp "do x <- f y; g x od arg"

val _ = Process.exit Process.success
