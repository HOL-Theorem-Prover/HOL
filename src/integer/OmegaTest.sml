structure OmegaTest =
struct

(* implementation of Pugh's Omega Test.  See
     @Article{Pugh92:_omega_test,
        author =       {William Pugh},
        title =        {The Omega Test: a fast and practical integer
                        programming algorithm for dependence analysis},
        journal =      cacm,
        year =         1992,
        volume =       35,
        number =       8,
        pages =        {102--114},
        month =        {August}
     }
*)

(* ----------------------------------------------------------------------
    Basic strategy:

    0. Assume we have fully quantified formula, with quantifiers only
       over integer variables.  If not we'll need to guess
       quantifiers, and/or convert form a problem over :num.  Use
       Cooper's algorithm code to do this.  Can also get rid of
       division and modulo operators at this stage.

    1. Normalisation.
       In the ideal world we have a formula of the form
          ?x1 .. xn. c1 /\ c2 ... /\ cn
       This is what we aim for.  Here's how we get there:

       - first eliminate universals and ?! by rewriting with the
         theorems
             (!x. P x) = ~?x. ~P x
             (?!x. P x) = ?x. P x /\ !y. P y ==> (y = x)

       - eliminate boolean operators other than ~ /\ \/ (i.e.,
         rewriting away ==> and $= : bool -> bool -> bool)

       - push in negations over /\ and \/

       - pick an innermost existential, and then convert the term
         underneath it to DNF.

       - then push as many existentials as possible down over
         disjunctions.

       - rewrite so that only integer operations are + ~ * <= and =.
         Also remove boolean negations over integer operators.

    2. Eliminate equalities in chosen sub-term.
       Term is of form
          ?v1 .. vn. c1 /\ .. cn
       Some of the ci are equalities.  Our aim is to eliminate as many
       of these as possible.  Implementation of this phase is in the
       structure OmegaEq.

   ---------------------------------------------------------------------- *)





end