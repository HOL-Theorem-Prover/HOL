signature legacyInduction =
sig
  include Abbrev

  (* ----------------------------------------------------------------------
      The induction principle the older construction produced.

      A datatype that recurses under an operator gets a principle saying,
      of a constructor's argument, what the operator's own set function
      says of it:

        ∀P. .. ∧ (∀l. (∀z. z ∈ setL l ⇒ P z) ⇒ ∀e. P (Clos l e)) ⇒ ∀v. P v

      The older construction said the same with a predicate for the
      operator as well, and clauses for the operator's own constructors:

        ∀P0 P1. .. ∧ (∀l. P1 l ⇒ ∀e. P0 (Clos l e)) ∧
                P1 [] ∧ (∀y l. P0 y ∧ P1 l ⇒ P1 (y::l)) ⇒
                (∀v. P0 v) ∧ ∀l. P1 l

      A proof written against the second shape can have it back.  Two
      things are wanted per operator recursed under, and the caller
      supplies them, since only the caller knows which operator it
      means: the operator's own induction principle, and what its set
      function says at each of the operator's constructors —

        setL [] = ∅        setL (h::t) = {h} ∪ setL t

      in whatever form the operator's theory writes them.

      There is one predicate per operator recursed under, and they come
      in the order the principle's clauses first mention them — which
      fixes both their names and the order of the conclusion's
      conjuncts, since a caller matches against those.
     ---------------------------------------------------------------------- *)
  type operator = {induction : thm, sets : thm list}

  val mutual_induction : operator list -> thm -> thm

  (* what that will prove, for a caller who would rather see it first *)
  val mutual_induction_goal : operator list -> thm -> term

end
