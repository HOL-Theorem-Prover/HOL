open HolKernel Parse boolLib bossLib sptreeSyntax testutils

fun testeval (s, t, expected) =
  let
    val _ = tprint s
    val th = EVAL t
         handle _ => die "FAILED - exception raised"
    val r = rhs (concl th) handle HOL_ERR _ => die "FAILED - no RHS"
  in
    if aconv r expected then OK()
    else die ("FAILED\n  Got >|" ^ term_to_string r ^"|<")
  end

val _ = tprint "sptreeSyntax.fromList"
val tm1 =
    fromList (List.tabulate (100, fn i => numSyntax.term_of_int (2 * i)))
             handle HOL_ERR _ => die "FAILED"
val _ = OK()
val _ = tprint "sptreeSytax.fromAList"
val tm2 =
    fromAList
      (List.tabulate
         (100, fn i => (Arbnum.fromInt (2 * i), numSyntax.term_of_int i)))
      handle HOL_ERR _ => die "FAILED"
val _ = OK()


val _ = app testeval [
  ("EVAL fromAList",
    ``fromAList [(23746, a:num); (73246, b); (912, c); (0, d)] =
      fromAList [(0, d); (73246, b); (23746, a:num); (912, c)]``,
    boolSyntax.T),
  ("EVAL fromList",
   ``fromList [a;b;c;d:num]``,
   ``BS (LS c) (a:num) (BS LN b (LS d))``),
  ("EVAL wf o fromList", ``wf ^tm1``, boolSyntax.T),
  ("EVAL wf o fromAList", ``wf ^tm2``, boolSyntax.T)]

val _ = temp_add_sptree_printer ()
val _ = remove_sptree_printer ()
val _ = temp_add_sptree_printer ()

fun tpp' (i,out) =
  tpp_expected {testf = standard_tpp_message, input = i, output = out}
val _ = app tpp' [
  ("BS (LS c) (a:num) (BS LN b (LS d))", "sptree$fromList [a; b; c; d]"),
  ("BS LN (a:num) (BS LN b (LS d))", "sptree$fromAList [(0,a); (1,b); (3,d)]")
]
