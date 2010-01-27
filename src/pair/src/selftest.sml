open HolKernel Parse boolTheory boolLib pairTheory
open parmonadsyntax state_transformerTheory

val _ = set_trace "Unicode" 0

fun tprint s = print (StringCvt.padRight #" " 65 (s ^ " ... "))
fun die () = (print "FAILED!\n"; Process.exit Process.failure)

fun tpp s = let
  val t = Parse.Term [QUOTE s]
  val _ = tprint ("Testing printing of `"^s^"`")
  val res = term_to_string t
in
  if res = s then print "OK\n"
  else die ()
end


val _ = app tpp ["\\(x,y). x /\\ y",
                 "\\(x,y,z). x /\\ y /\\ z",
                 "\\((x,y),z). x /\\ y /\\ z",
                 "(\\(x,y,z). x /\\ y /\\ z) p"]

(* check LET_INTRO *)

val _ = let
  val _ = tprint "Testing pairTools.LET_INTRO"
  val _ = pairTools.LET_INTRO (ASSUME ``((x,y) = (zw)) ==> (ARB x y):bool``)
  val _ = pairTools.LET_INTRO (ASSUME ``((x,y) = (z,w)) ==> (ARB x y):bool``)
  val _ = print "OK\n"
in
  ()
end handle e => die()

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

val _ = Process.exit Process.success
