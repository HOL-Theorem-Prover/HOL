signature legacyInduction =
sig
  include Abbrev

  (* ----------------------------------------------------------------------
      The induction principle the older construction produced.

      A datatype that recurses under an operator — `v = Litv lit | Clos
      (v list) exp` — gets a principle here saying, of a constructor's
      argument, what the operator's own set function says of it:

        ∀P. .. ∧ (∀l. (∀z. MEM z l ⇒ P z) ⇒ ∀e. P (Clos l e)) ⇒ ∀v. P v

      The older construction said the same thing with a predicate for the
      operator as well, and clauses for the operator's own constructors:

        ∀P0 P1. .. ∧ (∀l. P1 l ⇒ ∀e. P0 (Clos l e)) ∧
                P1 [] ∧ (∀y l. P0 y ∧ P1 l ⇒ P1 (y::l)) ⇒
                (∀v. P0 v) ∧ ∀l. P1 l

      A proof written against the second shape can have it back: this
      takes the first and returns the second.  The operators' own
      induction principles come from TypeBase; where one is not there to
      be found, the caller passes it.
     ---------------------------------------------------------------------- *)
  val mutual_induction : thm -> thm
  val mutual_induction_with : thm list -> thm -> thm

  (* what those two prove, for a caller who would rather see it than
     take it on trust *)
  val mutual_induction_goal : thm -> term

end
