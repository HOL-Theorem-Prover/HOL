# Automata

Finite state automata are a core component of computer science. One of
the nice things about them is their generality: automata appear in all
kinds of places, and the ideas developed in automata theory permeate
computer science.

An automaton processes a *word*, a list of symbols drawn from an
alphabet.  Processing goes symbol-by-symbol from left to right through
the word. At each step the automaton is in a *state* and it
transitions to a new state when it reads the next symbol. Once the
word has been fully traversed the automaton decides whether to accept
or reject the word; this is done by looking to see if the end state is
an accepting one or not. So: from one view this is a perfectly
mechanical process, but an automaton can also be viewed
mathematically as implementing a *set*, namely the set of words that
it accepts. The following formalization makes these ideas precise.

For this exercise we have a very simple notion of state: a state is
just a natural number.

```
Type state = “:num”
```
Well, one might think so ... there are shenanigans to be played!

## Deterministic Finite-State Automata (DFAs)

In textbooks, a DFA is defined to be a 5-tuple
\\(\langle Q,\Sigma,\delta,S,F \rangle \\), where *Q* is a finite set of states,
\\(\Sigma\\) is a finite set of symbols from which *words* may be formed,
\\(\delta\\) is a transition function, *S* is the start state, and *F* is
a set of final states.

```
Datatype:
  dfa = <|
    Q       : state set ;
    Sigma   : 'a set ;
    delta   : state -> 'a -> state;
    initial : state;
    final   : state set
  |>
End
```

DFA evaluation is defined by recursion:

```
Definition dfa_eval_def:
  dfa_eval N q [] = q ∧
  dfa_eval N q (a::w) = dfa_eval N (N.delta q a) w
End
```

The notion of *well-formedness* is important since the proofs we want
to make depend on DFAs having certain properties:

```
Definition wf_dfa_def:
  wf_dfa M ⇔
    FINITE M.Q ∧
    FINITE M.Sigma ∧
    M.initial ∈ M.Q ∧
    M.final ⊆ M.Q ∧
    (∀q a. a ∈ M.Sigma ∧ q ∈ M.Q ⇒ M.delta q a ∈ M.Q)
End
```

## Non-deterministic Finite-State Automata (NFAs)

NFAs have the same rough structure as DFAs, except that

- the start states are a set
- a transition results in a set of successor states

```
Datatype:
  nfa = <|
    Q : state set ;
    Sigma : 'a set ;
    delta : state -> 'a -> state set;
    initial : state set;
    final : state set
  |>
End
```

NFA evaluation is defined by recursion:

```
Definition nfa_eval_def:
  nfa_eval N qset [] = qset ∧
  nfa_eval N qset (a::w) = nfa_eval N (BIGUNION{N.delta q a | q | q ∈ qset}) w
End
```

```
Definition wf_nfa_def:
  wf_nfa N ⇔
    FINITE N.Q ∧
    FINITE N.Sigma ∧
    N.initial ⊆ N.Q ∧
    N.final ⊆ N.Q ∧
    (∀q a. a ∈ N.Sigma ∧ q ∈ N.Q ⇒ N.delta q a ⊆ N.Q)
End
```
