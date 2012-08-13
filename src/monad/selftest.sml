open HolKernel Parse boolTheory boolLib
open parmonadsyntax state_transformerTheory

val _ = set_trace "Unicode" 0

fun tprint s = print (StringCvt.padRight #" " 65 (s ^ " ... "))
fun die () = (print "FAILED!\n"; Process.exit Process.failure)

val _ = tprint "Testing parsing of parmonadsyntax"
val bind_t = prim_mk_const{Thy = "state_transformer", Name = "BIND"}
val _ = overload_on ("monad_bind", bind_t)
val _ = set_trace "notify type variable guesses" 0
val t = Term`do x <- f y ; g x od`
val _ = if same_const bind_t (#1 (strip_comb t)) then print "OK\n"
        else die()

val _ = tprint "Testing Q.parsing of parmonadsyntax"
val t = Parse.parse_in_context [] `do x <- f y; g x od`
val _ = if same_const bind_t (#1 (strip_comb t)) then print "OK\n"
        else die()

val _ = tprint "Testing Q-parsing of parmonadsyntax (TYPED-con)"
val t = Parse.parse_in_context [] `do x <- f y; g x od : 'a -> bool # 'a`
val _ = if same_const bind_t (#1 (strip_comb t)) then print "OK\n"
        else die()

val _ = Parse.current_backend := PPBackEnd.vt100_terminal
fun tpp (s,expected) = let
  val t = Parse.Term [QUOTE s]
  val _ = tprint ("Testing (coloured-)printing of `"^s^"`")
  val res = ppstring pp_term t
in
  if res = expected then print "OK\n"
  else die ()
end

fun bound s = "\^[[0;32m" ^ s ^ "\^[[0m"
fun free s = "\^[[0;1;34m" ^ s ^ "\^[[0m"
val concat = String.concat

val bx = bound "x"
val fy = free "y"
val fp = free "p"
val fx = free "x"

val _ = app tpp [
  ("do x <- f y; g x od",
   concat ["do ", bx, " <- ", free "f", " ", fy, "; ", free "g", " ",
           bx, " od"])
]

val _ = Process.exit Process.success
