# Automata

An automaton processes a *word*, a list of symbols drawn from an
*alphabet*. (Basically a word is a string, although it may draw from a
non-traditional set of symbols.) Processing goes symbol-by-symbol from
left to right through the word. At each step the automaton is in a
*state* and it transitions to a new state when it reads the next
symbol. Once the word has been fully traversed the automaton decides
whether to accept or reject the word; this is done by looking to see
if the current state is an *accepting* one or not.

For this tutorial we have a very simple notion of state: a state is
just a natural number.

```
Type state = “:num”
```

## Deterministic Finite-State Automata (DFAs)

The above describes a *deterministic* automaton: given its current
state and input symbol, there is one and only one next state it can go
to. Formally, a DFA is defined to be a 5-tuple \\(\langle Q,\Sigma,\delta,S,F
\rangle \\), where *Q* is a finite set of states, \\(\Sigma\\) is a
finite set of symbols from which *words* may be formed, \\(\delta\\)
is a transition function, *S* is the start state, and *F* is a set of
final states. This 5-tuple is modelled by a record with 5 fields:

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

DFA evaluation is defined by recursion on the word:

```
Definition dfa_eval_def:
  dfa_eval M q [] = q ∧
  dfa_eval M q (a::w) = dfa_eval M (M.delta q a) w
End
```

Evaluation iterates through the list of symbols, updating the state
(variable *q*) for each symbol seen, and returning the state the
machine is in once the end of the word is encountered. Notice that the
definition of evaluation makes no mention of start states or final
states. Those components come in when automata are treated as ways to
compute sets.

A notion of well-formedness of DFAs is also needed since not all possible
values of the `dfa` type make sense.

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

A wellformed DFA must have a finite set of states and the words it
processes must be built from its (finite) alphabet. The other
constraints imply that a well-formed DFA never strays outside of its
state set.

> [!WARNING]
> `M.delta` is a HOL function, therefore it is a total function.  That
> means that `M.delta q a` has a value for every possible `q` and `a`,
> including, for example, when `q` is not in `M.Q` or `a` is
> not in `M.Sigma`. In such situations the value of `M.delta q a`
> exists, but all we really know about it is that it has type
> `:num`. We are only assured that `M.delta q a` is a state of `M`
> when `q` is a state of `M` and `a` is a symbol in the alphabet of
> `M`. In short, one only wants to reason about applications of
> `M.delta` in settings where it is known that `M` is a wellformed
> DFA running on a word formed from `M.Sigma`.


## Non-deterministic Finite-State Automata (NFAs)

There are also *non-deterministic* automata: ones where, at each step
of processing, there is a *set* of possible next states.  NFAs have much
the same structure as DFAs, except that

- the start states are a set
- a transition results in a set of successor states

```
Datatype:
  nfa = <|
    Q       : state set ;
    Sigma   : 'a set ;
    delta   : state -> 'a -> state set;
    initial : state set;
    final   : state set
  |>
End
```

NFA evaluation is defined by recursion on the word argument.  A step
of NFA evaluation `Delta N qset a` moves from the (possibly empty) set
of states \\(\mathit{qset} = \\{q_1, \ldots, q_n\\} \\) to a successor
set of states by

1. For each \\(q_i \in \\mathit{qset}\\), an `M.delta` step is made on
   symbol `a`, delivering a finite set of \\(q_i\\)-successors.

2. This gives a set of sets which all get unioned together:
\\[
 M.delta\\; q_1 \\; a \cup \ldots\cup  M.delta\\; q_n\\; a
\\]

```
Definition Delta_def:
  Delta N qset a = BIGUNION{N.delta q a | q | q ∈ qset}
End
```

We can think about NFA evaluation as evolving the fringe of a tree
where the fringe at each step of evaluation represents the states that
the machine might be in.

```
Definition nfa_eval_def:
  nfa_eval N qset [] = qset ∧
  nfa_eval N qset (a::w) = nfa_eval N (Delta N qset a) w
End
```

A wellformed NFA obeys ostensibly similar requirements as a wellformed
DFA, adjusting for its usage of sets of states.

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

> [!NOTE]
> The definition of wellformedness for NFAs allows the states of the
> machine and the alphabet to be empty. The initial and final states
> can also be empty, and the transition function could return an empty
> set for every input, including well-formed ones. Indeed the
> following theorem is straightforward:
>
> ```
> Theorem wf_nfa_vacuous:
>   wf_nfa <|
>     Q       := ∅ ;
>     Sigma   := ∅ ;
>     delta   := λq a. ∅ ;
>     initial := ∅ ;
>     final   := ∅
>   |>
> Proof
>   simp [wf_nfa_def]
> QED
> ```
>
> In contrast, a wellformed DFA has to have an initial state, so it
> has at least one state, and every state must provide a transition to
> a next state for every symbol in the alphabet.


## Automata and Languages

The execution of an automaton is a perfectly mechanical process, but
an automaton can also be viewed mathematically as implementing a
*set*, namely the set of words that it *accepts*. This is called the
*language* of the automaton. A DFA `M` accepts word `w` if

- `w` is built solely from `M.Sigma` symbols, and

- execution on `w` starts in state `M.initial` and ends in one of the
  states in `M.final`.

```
Definition dfa_lang_def:
  dfa_lang M = {w | EVERY M.Sigma w ∧ dfa_eval M M.initial w ∈ M.final}
End
```

An NFA `N` accepts word `w` if `w` is a word drawn from `N.Sigma` and
execution on `w` starts with the set of states `N.initial` and ends in
a set of states with a non-empty overlap with `M.final`.

```
Definition nfa_lang_def:
  nfa_lang N = {w | EVERY N.Sigma w ∧ nfa_eval N N.initial w ∩ N.final ≠ ∅}
End
```

We are now able to capture the languages implementable by DFAs and NFAs:

```
Definition DFA_LANGS_def:
   DFA_LANGS = {dfa_lang M | wf_dfa M}
End

Definition NFA_LANGS_def:
   NFA_LANGS = {nfa_lang N | wf_nfa N}
End
```

We will show how to prove these are the same in the following sections.
