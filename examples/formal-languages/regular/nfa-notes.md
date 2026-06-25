<!--- Invocation for making HTML version:
   cat nfa-notes.md | pandoc --standalone -f gfm > nfa-notes.html && open nfa-notes.html
--->

# Notes on nfaScript.sml

The HOL4 theory found in `nfaScript.sml` formalizes non-deterministic
finite state automata (NFA). We follow the concise presentation by
Pippenger in his book [Theories of Computability](https://www.cambridge.org/us/universitypress/subjects/computer-science/programming-languages-and-applied-logic/theories-computability?format=HB&isbn=9780521553803).
Most of the material is well-known (the subset construction, closure
constructions for the regular languages, and further material ending
up with the Myhill-Nerode theorem). We have dealt with only a fragment
of the topic; Pippenger gives a much more comprehensive treatment. Buy
the book!

There are some elements that deserve further mention. First, the
development includes an old result from Nerode (1958) showing that the
so-called "intrinsic states" of a formal language are finite iff the
language is regular. (The intrinsic states of a language are what one
obtains by taking left-quotients on the language, using every word
over the alphabet. The technical definition is in
`../FormalLangScript.sml`.) This elegant---and fairly simple to
prove---characterization allows one to think about regular languages
in terms of set operations on languages rather than only in terms of
automata or regular expressions.

Secondly, $\epsilon$-transitions in automata are not supported. This
clarifies some proofs, at the cost of making some automata
constructions a bit harder to express. To be sure,
$\epsilon$-transitions can be added as a derived notion later, but we
haven't yet done so.

## Formalization Choices

In building finite-state automata theory in the HOL logic, there are
some formalization choices to wrestle with that aren't so obvious, and
then there are some that are obvious, but should still be written down.

### Alphabets are polymorphic

This aligns with the definitions in `FormalLangTheory` where
formal languages are represented by sets of words, which are
represented by `'a list`.

### States are not polymorphic (and not necessarily finite)

The central focus of automata theory is on the *Regular* languages,
namely those formal languages recognizable by an NFA. In our
formalization:

```
  (L,A) ∈ REGULAR ⇔ ∃N. N.Sigma = A ∧ is_nfa N ∧ L = nfa_lang N
```

Taking a computer science viewpoint, this clearly separates
specification (language, alphabet) from implementation
(automaton). The implementation has to satisfy the specification, but
is allowed full freedom in the construction of the specific machine,
including its state space. Indeed two machines with very different
state spaces can implement the same language.

The predicate `REGULAR` has type `'a list set # 'a set -> bool`. One
can see that the notion of *state* used by NFAs does not appear in the
definition of `REGULAR`: regularity is a property of languages
alone. In the HOL logic, this rules out using polymorphism to express
the state space of the NFA. Why? For the technical reason that all
polymorphism on the RHS of a definition in HOL must also be accounted
for on the LHS of the definition. Type theories with existential types
could surmount this difficulty.

So: NFAs are polymorphic in the symbols used in the alphabet, but not
in the state space. However, states can be arbitrarily complex and may
even involve polymorphic objects. For example, in the "intrinsic
state" DFA, each state of the machine is a formal language, ie, a
typically infinite set of words.  We resolve this conundrum, when
necessary, by using bijective "encode/decode" maps from state spaces
to initial segments of the natural numbers.

For example, a state transition in the "intrinsic state" machine takes
the current state (a number) and the current input symbol $a$ and (1)
finds the formal language $L$ indexed by the state, then (2) takes the
left-quotient of $L$ by $a$, then (3) returns the index of the resulting
language; this number is the new state.

### Why is the alphabet a parameter to `REGULAR`?

Early in all material on language theory, there is mention that a
formal language $L$ is a subset of $A^{*}$, where $A$ is the alphabet that
words in $L$ are built from. Each NFA representation includes its alphabet
$A$. Why then provide $A$ as a parameter to the definition of REGULAR,
*i.e.*, shouldn't it be enough that the alphabet of a regular language
be determined by the implementing automaton?

One important reason for this choice is that otherwise we wouldn't be
able to prove equivalence of `REGULAR` with `FINITE_STATE`, the latter of
which is defined wrt both $L$ and $A$. Moreover, in some examples,
operations on languages go together with operations on alphabets.  For
example, closure under morphisms should provide a good test of this
choice. A simpler example is regularity preservation under alphabet
extension:

```
  (L,A) ∈ REGULAR ∧ FINITE B ⇒ (L,A ∪ B) ∈ REGULAR
```

This wouldn't be expressible in an approach that suppresses mention of
the alphabet in the definition of regularity. (It can be expressed and
proved at a lower level of abstraction though.)
