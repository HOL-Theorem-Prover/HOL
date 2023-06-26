open testutils HolKernel Parse boolLib bossLib cv_computeLib cvSyntax cvTheory;

val (factc_def,_) = TotalDefn.tDefine
  "factc_def"
  `factc n =
    cv_if (cv_lt n (Num 1))
          (Num 1)
          (cv_mul n (factc (cv_sub n (Num 1))))`
  (WF_REL_TAC `measure cv_size_alt`
  \\ Cases \\ simp [cv_size_alt_def, CaseEq "bool"]);

fun fact n =
  if Arbnum.< (n, Arbnum.one) then Arbnum.one
  else Arbnum.* (n, fact (Arbnum.- (n, Arbnum.one)));

val factc_tm = ``factc``;
fun mk_factc tm = mk_comb (factc_tm, tm);
val dest_num = numSyntax.dest_numeral o rand;

fun test_factc n =
  cv_computeLib.cv_compute [factc_def]
    (mk_factc (cvSyntax.mk_cv_num (numSyntax.term_of_int n)));

fun test n =
  let
    val nstr = Int.toString n
    val _ = tprint ("factc " ^ nstr ^ " ?= ML fact " ^ nstr)
    val x = dest_num (rhs (concl (test_factc n)))
    val y = fact (Arbnum.fromInt n)
  in
    if x = y then OK () else
      die ("failed: " ^ Arbnum.toString x ^ " (factc), " ^
                        Arbnum.toString y ^ " (ML fact)")
  end;

(* dest_numeral runs out of stack for fact(256) *)

val _ = List.app test [0, 1, 5, 10, 13, 74, 157, 180];

