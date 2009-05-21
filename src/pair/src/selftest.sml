open HolKernel Parse boolTheory boolLib pairTheory

fun tprint s = print (StringCvt.padRight #" " 65 (s ^ " ... "))

fun tpp s = let
  val t = Parse.Term [QUOTE s]
  val _ = tprint ("Testing printing of `"^s^"`")
  val res = term_to_string t
in
  if res = s then print "OK\n"
  else (print "FAILED!\n"; Process.exit Process.failure)
end


val _ = app tpp ["\\(x,y). x /\\ y",
                 "\\(x,y,z). x /\\ y /\\ z",
                 "\\((x,y),z). x /\\ y /\\ z",
                 "(\\(x,y,z). x /\\ y /\\ z) p"]

(******************************************************************************)
(* check LET_INTRO *)

val _ =
    let val _ = print "*** Testing pairTools.LET_INTRO ..."
        val _ = pairTools.LET_INTRO (ASSUME ``((x,y) = (zw)) ==> (ARB x y):bool``)
        val _ = pairTools.LET_INTRO (ASSUME ``((x,y) = (z,w)) ==> (ARB x y):bool``)
        val _ = print "SUCCESS!\n"
    in
        ()
    end handle e => (print "FAILED!\n"; Process.exit Process.failure)


val _ = Process.exit Process.success
