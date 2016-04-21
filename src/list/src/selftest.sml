open HolKernel Parse boolLib
open ListConv1

open testutils

fun test nm cmp pr f (x, expected) = let
  val _ = tprint (StringCvt.padRight #" " 20 nm ^ pr x)
  val result = f x
in
  if cmp(rhs (concl result),expected) <> EQUAL then die "FAILED - BAD RHS"
  else if not (null (hyp result)) then die "FAILED - HYPS"
  else if cmp(lhs (concl result),x) <> EQUAL then die "FAILED - BAD LHS"
  else (OK(); true)
end handle HOL_ERR _ => die "FAILED - EXN"

val _ = set_trace "Unicode" 0

val _ = app tpp ["MEM a l", "~MEM a l", "x NOTIN {1; 2; 3}"]

val _ = tpp_expected {input = "SINGL 3", output = "[3]",
                      testf = standard_tpp_message}

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
