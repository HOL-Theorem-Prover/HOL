open testutils HolKernel Parse boolLib cv_computeLib cvSyntax cvTheory;
open arithmeticTheory tailrecLib

fun simp ths = simpLib.ASM_SIMP_TAC (BasicProvers.srw_ss()) ths

val M = “(λf n. cv_if (cv_lt n (cv$Num 1)) (cv$Num 1)
             (cv_mul n (f (cv_sub n (cv$Num 1)))))”
val factc_def0 = new_definition("factc_def0",
  “factc = WFREC (measure cv_size_alt) ^M”);

val restrict_lemma = Q.prove(
  ‘^M (RESTRICT factc (measure cv_size_alt) x) x = ^M factc x’,
  BETA_TAC >> irule cv_if_cong >> simp[] >>
  Q.SPEC_THEN ‘x’ STRUCT_CASES_TAC (TypeBase.nchotomy_of “:cv”) >>
  simp[] >> IF_CASES_TAC >> simp[c2b_def] >>
  simp[relationTheory.RESTRICT_DEF, cv_size_alt_def] >>
  Q.RENAME_TAC [‘n <> 0’] >>
  reverse $ Q.SUBGOAL_THEN ‘n - 1 < n’ ASSUME_TAC >- simp[] >>
  irule SUB_LESS >> pop_assum mp_tac >>
  Q.SPEC_THEN ‘n’ STRUCT_CASES_TAC num_CASES >>
  simp[ONE, LESS_EQ_MONO, ZERO_LESS_EQ]);

val factc_def = MATCH_MP relationTheory.WFREC_THM
                         (Q.ISPEC ‘cv_size_alt’ prim_recTheory.WF_measure)
                         |> ISPEC M
                         |> REWRITE_RULE[restrict_lemma, GSYM factc_def0]
                         |> BETA_RULE

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
    val MLresult = fact (Arbnum.fromInt n)
    fun check th =
        let val x = dest_num (rhs (concl th))
        in
          MLresult = x
        end
    val _ = tprint ("factc " ^ nstr ^ " ?= ML fact " ^ nstr)
    val x = dest_num (rhs (concl (test_factc n)))
  in
    require_msg (check_result check) thm_to_string test_factc n
  end;

(* dest_numeral runs out of stack for fact(256) *)

val _ = List.app test [0, 1, 5, 10, 13, 74, 157, 180];

(* tail-recursion *)
val base_t = “fib A N x = if x = 0 then A else fib (N + A) A (x -1) ”
val expected = “?fib. !A N x. ^base_t”
val _ = tprint "tailrecursive fibonacci"
val _ = require_msg (check_result (aconv expected o concl)) thm_to_string
                    prove_tailrec_exists
                    base_t

val odd = “(odd n = if n = 0 then F else even (n - 1))”
val even = “(even i = if i = 0 then T else odd (i - 1))”
val base_t = mk_conj(odd,even)
val expected = “?odd even. (!n. ^odd) /\ (!i. ^even) ”
val _ = tprint "tailrecursive even/odd"
val _ = require_msg (check_result (aconv expected o concl)) thm_to_string
                    prove_tailrec_exists
                    base_t

val odd = “(odd n = cv_if (cv_eq n (cv$Num 0))
                          (cv$Num 0) (even (cv_sub n (cv$Num 1))))”
val even = “(even i = cv_if (cv_eq i (cv$Num 0))
                          (cv$Num 1) (odd (cv_sub i (cv$Num 1))))”
val base_t = mk_conj(odd,even)
val expected = “?odd even. (!n. ^odd) /\ (!i. ^even) ”
val _ = tprint "tailrecursive even/odd"
val _ = require_msg (check_result (aconv expected o concl)) thm_to_string
                    prove_tailrec_exists
                    base_t

val _ = require_msg
