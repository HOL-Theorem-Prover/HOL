signature OmegaSimple =
sig

  include Abbrev

  val simple_CONV : conv

  val verify_result : term -> term list -> term OmegaMLShadow.result -> thm
  val verify_satisfaction : term -> term list -> Arbint.int PIntMap.t -> thm
  val verify_derivation :
      term -> term list -> term OmegaMLShadow.derivation -> thm
  val verify_contr : (thm * thm) -> thm
  val verify_gcd_check : thm -> thm
  val verify_combination : term -> thm -> thm -> thm

end;

(*
   This file turns the "external proofs" returned by the OmegaMLShadow
   implementation into HOL kernel proofs.  It also performs the initial
   translation from a HOL formula into a shadow proof state, so that the
   simple_CONV function can do an entire proof.

   [simple_CONV t] tries to prove t using the OmegaMLShadow approach.  The
   input term must be of the form
       ?x1..xn. body
   with body being a conjunction of terms, all of the form
       0 <= c1 * v1 + .. cn * vn + c
   with v1 < v2 < .. < vn according to the standard Term ordering.  (The
   ordering of x1..xn in the existential quantification isn't important.)
   The final term constant c must always be present, even if it is zero.

   [verify_result tm vars r] takes a term and a result from the
   MLShadow and attempts to turn it into a theorem, where vars is the
   list of variables occuring in tm, in order.

   [verify_satisfaction tm vars vm] proves formula tm true by providing
   witnesses for the variables.  vm maps indices from the list of vars
   to the values that those variables should take on.

   [verify_derivation tm vars d] takes a purported derivation of
   false from the assumption tm, and uses it to equate tm to false.
   vars is the list of variables in tm, in order.

   [verify_contr (th1, th2)] returns [..] |- F, given the theorems th1
   and th2, which between them say contradictory things.  They will
   be of the form 0 <= X + c and 0 <= ~X + d and ~c is not <= d.  X
   may be the sum of multiple ci * vi pairs.

   [verify_gcd_check th] eliminates a common divisor from the
   coefficients of the variables in theorem th, which is of the
   standard form.

   [verify_combination v th1 th2] does variable elimination on v,
   given a "lower-bound" theorem th1, and an "upper-bound" theorem
   th2.  Both th1 and th2 are of the form
     0 <= c1 * v1 + ... + vn * cn + n
   In th1, the coefficient of v will be positive, and in th2,
   negative.

*)
