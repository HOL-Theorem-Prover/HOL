open HolKernel Parse boolTheory boolLib testutils
open monadsyntax parmonadsyntax state_transformerTheory errorStateMonadTheory

val _ = temp_remove_absyn_postprocessor "monadsyntax.transform_absyn"
val _ = temp_remove_user_printer "monadsyntax.print_monads"

val _ = set_trace "Unicode" 0

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
fun tpp (s,expected) = let
  val t = Parse.Term [QUOTE s]
  val _ = tprint ("Testing (coloured-)printing of `"^s^"`")
  val res = ppstring pp_term t
in
  if res = expected then OK()
  else die ("FAILED\n  Printer produced \"" ^ res ^ "\"!")
end

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

val _ = app tpp [monadtpp_test1, monadtpp_test2]

val _ = clear_overloads_on "monad_bind"

val _ = temp_remove_absyn_postprocessor "parmonadsyntax.transform_absyn"
val _ = temp_remove_user_printer "parmonadsyntax.print_monads"

val _ = temp_add_user_printer ("monadsyntax.print_monads", genvar alpha,
                               monadsyntax.print_monads)
val _ = temp_add_absyn_postprocessor ("monadsyntax.transform_absyn",
                                      monadsyntax.transform_absyn)
val _ = temp_overload_on("monad_bind", ``option$OPTION_BIND``)
val _ = temp_overload_on("monad_unitbind", ``option$OPTION_IGNORE_BIND``)

val _ = unicode_off (raw_backend (trace ("types", 1) testutils.tpp))
                    "do (x :num) <- (s :num option); SOME (x + (1 :num)) od"

val _ = tprint "Testing monadsyntax parse of OPTION_BIND"
val t = ``do x <- opt ; SOME (x + 1) od``
val (f, args) = strip_comb t
val _ = same_const f ``option$OPTION_BIND`` andalso
        hd args = mk_var("opt", ``:num option``) andalso
        hd (tl args) = ``\x:num. SOME (x + 1)`` andalso
        (OK(); true) orelse udie ()

val _ = tprint "Testing monadsyntax parse of OPTION_IGNORE_BIND"
val t = ``do SOME 3 ; SOME 4 od``
val (f, args) = strip_comb t
val _ = same_const f ``option$OPTION_IGNORE_BIND`` andalso
        hd args = ``SOME 3`` andalso
        hd (tl args) = ``SOME 4`` andalso
        (OK(); true) orelse udie()

val _ = clear_overloads_on "monad_unitbind"
val _ = temp_overload_on ("monad_unitbind",
                          ``\m1 m2. option$OPTION_BIND m1 (K m2)``)

val _ = tprint "Testing monadsyntax parse of OPTION_BIND (ignoring)"
val t = ``do SOME 3 ; SOME 4 od``
val (f, args) = strip_comb t
val _ = same_const f ``option$OPTION_BIND`` andalso
        hd args = ``SOME 3`` andalso
        hd (tl args) = ``K (SOME 4) : num -> num option`` andalso
        (OK(); true) orelse udie()

val _ = app tpp [monadtpp_test1, monadtpp_test2]

val _ = app clear_overloads_on ["monad_bind", "monad_unitbind"]
val _ = temp_overload_on ("monad_bind", ``errorStateMonad$BIND``);
val _ = temp_overload_on ("monad_unitbind", ``errorStateMonad$IGNORE_BIND``);

val _ = print "Testing with error state monad\n"

val _ = app tpp [monadtpp_test1, monadtpp_test2]

val _ = current_backend := PPBackEnd.raw_terminal
val _ = testutils.tpp "do x <- f y; g x od arg"

val _ = Process.exit Process.success
