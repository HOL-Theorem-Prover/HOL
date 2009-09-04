(*-------------------------------------------------------------------
 * UNWIND_EXISTS_CONV : conv
 * UNWIND_FORALL_CONV : conv
 *
 * DESCRIPTION
 *
 * UNWIND_EXISTS_CONV eliminates existential
 * quantifiers where the quantified variable
 * is restricted to a single point via an equality in the
 * conjuncts of the body.  Given a term of the form
 *    ?x1 x2 ... xn. P1[x1..xn] /\ P2[x1..xn] /\ ... /\ Pm[x1..xn]
 * where one of Pk is
 *        "x1 = F[x2...xn]"
 *   or   "F[x2...xn] = x1"
 *   or   "x1"
 *   or   "~x1"
 * UNWIND_EXISTS_CONV eliminates the variable x1 from the existential
 * quantification and converts the term to
 *     ?x2...xn. P1'[x2...xn] /\ ...P(m-1)'[x2...xn]
 * where P1' through Pm-1' have any occurrences of x1 substituted as
 * F[x2...xn].
 *
 * UNWIND_FORALL_CONV eliminates universal
 * quantifiers where the quantified variable
 * is restricted to a single point via an equality in the
 * conjuncts of the body.  Given a term of the form
 *    !x1 x2 ... xn. P1[x1..xn] ==> P2[x1..xn] ==> ... ==> Pm[x1..xn]
 * where one of Pk (k < m) is
 *        "x1 = F[x2...xn]"
 *   or   "F[x2...xn] = x1"
 *   or   "x1"
 *   or   "~x1"
 * UNWIND_FORALL_CONV eliminates the variable x1 from the
 * quantification and converts the term to
 *     !x2...xn. P1'[x2...xn] ==> ...P(m-1)'[x2...xn] ==> Pm[x1..xn]
 * where P1' through Pm-1' have any occurrences of x1 substituted as
 * F[x2...xn], and Pk has been removed.
 *
 * The constraint can also occur within conjuncts of P1, P2 ... P(m-1).
 *
 * USES
 *
 * Eliminating trivial existential and universal quantifiers.
 *
 * EXAMPLES
 *
 * - UNWIND_EXISTS_CONV (--`?inp. inp /\ P inp`--);
 * |- (?inp. inp /\ P inp) = P T : thm
 *
 * - UNWIND_EXISTS_CONV (--`?inp (f:'a->num). (inp = f x)  /\ P f inp`--);
 * |- (?inp f. (inp = f x) /\ P f inp) = (?f. P f (f x)) : thm
 *
 * - UNWIND_EXISTS_CONV (--`?inp. ~inp /\ P inp`--);
 * |- (?inp. ~inp /\ P inp) = P F : thm
 *
 * UNWIND_FORALL_CONV (--`!x. (x = 3) ==> P x`--);
 * UNWIND_FORALL_CONV (--`!x. (x = 3) /\ Q x ==> P x`--);
 * UNWIND_FORALL_CONV (--`!x. (3 = x) /\ Q x ==> P x`--);
 * UNWIND_FORALL_CONV (--`!x. (x < y) ==> (x = 3) /\ Q x ==> P x`--);
 * UNWIND_FORALL_CONV (--`!Q R. (x = 3) /\ Q /\ P x ==> R Q`--);
 * UNWIND_FORALL_CONV (--`!Q R. (x = 3) /\ ~Q /\ P x ==> R Q`--);
 *
 * TESTING CODE
 *
 * use "3/simplifier/src/UNWIND.sml";
 * open UNWIND;
 *------------------------------------------------------------------------*)

signature Unwind =
sig
   include Abbrev

   val UNWIND_EXISTS_CONV : conv
   val UNWIND_EXISTS_TAC : tactic
   val UNWIND_EXISTS_RULE : thm -> thm
   val UNWIND_FORALL_CONV : conv
   val UNWIND_FORALL_TAC : tactic
   val UNWIND_FORALL_RULE : thm -> thm

end (* sig *)
