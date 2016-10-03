open HolKernel Parse boolLib

val _ = new_theory "mergeGrammarsA1";

(* demonstrating what should happen when a theory ancestry graph looks like

        bool
        / \
       A1  A2
        \ /
         B

   and

   - A1 sets the fixity of equality (using set_fixity) to something
     other than its default;
   - A2 doesn't mention the parsing of equality at all

   Q: What should happen in B?

   A #1: the behaviour, as of 3 October 2016 is to "merge" the
   ancestral grammars by taking what is effectively a union operation
   over the rules. This results in a grammar with two rules for
   equality, and one that will report ambiguities at every computation
   of the precedence matrix.

   A #2: I believe the desired behaviour should be to merge the
   history of changes to the grammars. Assuming A2 doesn't do anything
   to equality, this should result in B's grammar being the same as
   A1's.

   - -

   Note that it's harder to see a problematic behaviour in the global
   grammar because this is updated by a sequence of calls that are
   made as the theories load. Instead, the problem is apparent in the
   value of

      #2 mergeGrammarsBTheory.mergeGrammarsB_grammars

*)

val _ = set_fixity "=" (Infix(NONASSOC, 450));

val a_theorem = store_thm(
  "a_theorem",
  ``x:bool = x /\ y = y``,
  REWRITE_TAC[]);

val _ = export_theory();
