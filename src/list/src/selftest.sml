open HolKernel Parse boolLib
open ListConv1

fun test nm cmp pr f (x, expected) = let
  val _ = print (StringCvt.padRight #" " 20 nm)
  val _ = print (StringCvt.padRight #" " 40 (pr x))
  val result = f x
in
  if cmp(rhs (concl result),expected) <> EQUAL then
    (print "FAILED - BAD RHS\n"; false)
  else if not (null (hyp result)) then
    (print "FAILED - HYPS\n"; false)
  else if cmp(lhs (concl result),x) <> EQUAL then
    (print "FAILED - BAD LHS\n"; false)
  else
    (print "OK\n"; true)
end handle HOL_ERR _ => (print "FAILED - EXN\n"; false)

val _ =
    if List.all (test "FIRSTN_CONV" Term.compare term_to_string FIRSTN_CONV)
                [(``FIRSTN 3 [1;2;3;4;5]``, ``[1;2;3]``),
                 (``FIRSTN 4 [1;2;3;4]``, ``[1;2;3;4]``),
                 (``FIRSTN 0 [1;2]``, ``[] : num list``),
                 (``FIRSTN 0 [] : num list``, ``[] : num list``)]
       andalso
       List.all
           (test "BUTFIRSTN_CONV" Term.compare term_to_string BUTFIRSTN_CONV)
           [(``BUTFIRSTN 3 [1;2;3;4]``, ``[4]``),
            (``BUTFIRSTN 0 [1;2]``, ``[1;2]``),
            (``BUTFIRSTN 3 [1;2;3]``, ``[] : num list``),
            (``BUTFIRSTN 0 [] : num list``, ``[] : num list``)]
       andalso
       List.all
         (test "LIST_EQ_SIMP_CONV" Term.compare term_to_string
               listSimps.LIST_EQ_SIMP_CONV)
         [(``(l1:'a list ++ [])::t = p ++ q``, ``(l1:'a list)::t = p ++ q``)]
    then
      Process.exit Process.success
    else Process.exit Process.failure
