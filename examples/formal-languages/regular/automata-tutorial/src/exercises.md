# Exercises

1. Formulate and prove the following statement of the Axiom of Choice:
   *For every set of non-empty sets there exists a function that picks an
   element from each set*.

1. Define a type `cfa` (for *computable NFA*) with a concrete
   representation for sets of states, such as lists or trees, so that
   `cfa` may be computed over with `EVAL` or `Thm.compute`. Define the
   languages accepted by wellformed CFAs and show they are equal to
   `NFA_LANGS`.

1. Although the result of the subset construction is a DFA, it is an
   inefficient one, since the (constructed) DFA transition works by
   decoding to a set of states, applying the underlying NFA transition
   function `Delta`, and encoding the result. Devise and prove correct
   a "compilation pass" that maps such a DFA to a DFA that operates by
   essentially looking up the successor state from a table.

1. Another way to approach NFA acceptance---in fact the standard
   way---is to base it on *execution traces*. For an NFA *N* we say
   that a list of states \\(\\mathit{qs} = [q_0, \\ldots q_n ] \\)
   drawn from `N.Q` is an execution trace for word *w* if
   \\(\\mathit{qs}_{i+1} \in N.delta\\; \\mathit{qs}_i \\; w_i \\)
   holds for each \\(i \in \\{0, \ldots, |w| - 1 \\} \\). This can be
   formulated as a recursive definition in the following way:

   ```
   Definition nfa_trace_def:
     nfa_trace N [q] [] = (q ∈ N.Q) ∧
     nfa_trace N (q1::q2::t) (a::w) =
        (nfa_trace N (q2::t) w ∧
         a ∈ N.Sigma ∧ q1 ∈ N.Q ∧ q2 ∈ N.delta q1 a) ∧
     nfa_trace N _ _ = F
   End
   ```

   Then we can define the accepting traces of NFA `N` and the set of
   words having an accepting `N`-trace as follows:

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

   Definition NFA_TRACE_LANGS_def:
     NFA_TRACE_LANGS = {nfa_trace_lang N | wf_nfa N}
   End
   ```

   An accepting NFA trace shows that there exists a path---a sequence
   of "choices of next state to be in"---that the NFA can
   take in order to accept its input. This is very much unlike a DFA
   evaluation in which there is never any choice about the next state
   the machine can be in.

   The main lemma in this exercise relates `nfa_eval` and `nfa_trace`:
   it says that the set of states in the fringe after computation with
   `nfa_eval` on `w` is equal to the set of final states of traces for
   `w`. More precisely:

   ```
   Theorem nfa_eval_trace:
     wf_nfa N ⇒
     ∀w qset.
       EVERY N.Sigma w ∧ qset ⊆ N.Q
       ⇒ nfa_eval N qset w = {LAST qs | nfa_trace N qs w ∧ HD qs ∈ qset}
   Proof
     ...
   QED
   ```

   The main difficulty in proving `nfa_eval_trace` is that traces get
   extended "on the right" by appending the next state to the end of
   the trace. A number of lemmas about `nfa_trace` need to be built up
   in order to address the difficulty.

   Finally, one can use `nfa_eval_trace` to prove `wf_nfa N ⇒ nfa_lang
   N = nfa_trace_lang N` and then showing `NFA_LANGS =
   NFA_TRACE_LANGS` is easy.

1. Re-do the previous exercise, but use the `Inductive ... End` form
   to define the `nfa_trace` concept.
