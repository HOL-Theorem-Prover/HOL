open HolKernel Parse boolLib bossLib
open testutils

val _ = print "\n"

fun test_CONV (c,nm) (t, expected) = let
  val _ = tprint (nm^" on `"^term_to_string t^"`")
  val th = Conv.QCONV c t
in
  if aconv (rhs (concl th)) expected then print "OK\n"
  else die "FAILED!\n"
end handle HOL_ERR _ => die "FAILED (not even an eqn)!"

val _ = set_trace "Unicode" 0

val _ = app (test_CONV (EVAL,"EVAL")) [
      (``option_CASE (NONE : 'a option) (n:'b) f``, ``n:'b``),
      (``option_CASE (SOME (x:'a)) (n:'b) f``, ``f (x:'a):'b``),
      (``list_CASE ((h::t) : 'a list) (n:'b) f``,
       ``f (h:'a) (t:'a list):'b``),
      (``sum_CASE (INL 3) (\n. n) f``, ``3``),
      (``INL (x:'a) = INR (y:'b)``, ``F``),
      (``INL (x:'a) = INL x'``, ``x:'a = x'``)
];

val tydef_th = prove(
  ``?p. FST p /\ SND p``,
  EXISTS_TAC ``(T,T)`` THEN REWRITE_TAC []);

val _ = tprint "new_type_definition error message"
val failing_tydef =
    new_type_definition("mytydef", tydef_th)
    handle HOL_ERR {origin_function, message, origin_structure} =>
           if origin_function <> "new_type_definition" orelse
              origin_structure <> "Theory.Definition" orelse
              message <> "at Thm.prim_type_definition:\nexpected a theorem of the form \"?x. P x\""
           then
             die "FAILED"
           else (print "OK\n"; TRUTH)

val _ = tprint "Q.MATCH_ABBREV_TAC with underscores"
val goal = ([] : term list, ``(n + 10) * y <= 42315 /\ !x y:'a. x < f y``)
val (sgs, _) = Q.MATCH_ABBREV_TAC `a * _ <= b /\ _` goal
val expectedg = ``(a:num) * y <= b /\ !x y:'a. x < f y``
val exab1 = ``Abbrev((a:num) = n + 10)``
val exab2 = ``Abbrev((b:num) = 42315)``
val _ = case sgs of
            [(asms, g')] =>
            if aconv g' expectedg andalso op_mem aconv exab1 asms andalso
               op_mem aconv exab2 asms andalso length asms = 2
            then
              print "OK\n"
            else die "FAILED!"
          | _ => die "FAILED!"
