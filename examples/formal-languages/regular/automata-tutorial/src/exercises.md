# Exercises

1. Formulate and prove the following statement of the Axiom of Choice:
   *For every set of non-empty sets there exists a function that picks an
   element from each set*.

1. Make the type of "sets of states" into something that can be
   computed over (lists, for example) and re-do the proofs.

1. Another way to approach this material---in fact the standard
   way---is to base it on *execution traces*. Say that a list of states
   \\( [q_0, \\ldots q_n ] \\) is an NFA execution trace for *N* on
   word *w* if it starts in a state of `N` and \\(q_{i+1} \in
   M.delta\\; q_i \\; w_i \\) holds for each \\(i \in \\{0, \ldots,
   |w| - 1 \\} \\).  This can be formulated as a recursive definition
   in the following way:

   ```
   Definition nfa_trace_def:
     nfa_trace N [q] [] = (q ∈ N.Q) ∧
     nfa_trace N (q1::q2::t) (a::w) =
        (a ∈ N.Sigma ∧
         q1 ∈ N.Q ∧
         q2 ∈ N.delta q1 a ∧
         nfa_trace N (q2::t) w) ∧
     nfa_trace N _ _ = F
   End
   ```

   Then we can define the accepting traces of NFA `M` and the set of words having an accepting `N`-trace as follows:

   ```
   Definition accepting_nfa_trace_def:
     accepting_nfa_trace N qs w <=>
        nfa_trace N qs w ∧
        HD qs ∈ N.initial ∧
        LAST qs ∈ N.final
   End

   Definition nfa_trace_lang_def:
     nfa_trace_lang N = {w | ∃qs. accepting_nfa_trace N qs w}
   End
   ```

   Show that `nfa_trace_lang M = nfa_lang M`.

1. Re-do the previous exercise, but use the `Inductive ... End` form to define the `nfa_trace` concept.
