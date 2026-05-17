# Introduction

The goal of this tutorial is to show some definitions and proofs being
performed in HOL4, eventually arriving at a well-known result in the
Theory of Computation, namely a proof of equivalence between the
languages definable by deterministic finite-state automata (DFAs) and
their non-deterministic analogues (NFAs).

We assume a working version of HOL4 plus some basic knowledge of the
system:

- how to start it up, whether standalone or in the editor of your choice;
- how to create and work with a theory script;
- how to start and work with a proof attempt in a goal manager; and
- what a tactic is and how to apply one to the current goal;

HOL4 provides a large and extensible collection of inference tools but
a relatively small set of tactics usually suffices. See
[Cheatsheet](https://hol-theorem-prover.org/cheatsheet.html) for a
good overview of the basics. We will discuss special aspects of our
reasoning tools as they get used in proofs.

## Noteworthy Features

The development has a few interesting aspects.

1. It is evaluation-oriented. The correctness of the subset
   construction is formalized as an equivalence between two different
   evaluations, one being that of the (constructed) DFA and the other
   being evaluation of the original NFA. The proof is quite simple. In
   the exercises, the connection with the standard notion of NFA
   language acceptance, *i.e.* the existence of a suitable *sequence*
   of states, then gets defined and related to NFA evaluation in a
   clean fashion.

2. The subset construction requires encoding and decoding sets of
   states. We use Hilbert's Choice operator as a device for achieving
   this, and explore how to deal with choice terms in proofs.

3. "Exotic" tactics used and explained: dependent rewriting in the
   form `DEP_{ASM_}REWRITE_TAC`, and `cong_tac` for removing common term
   structure from equalities.

## Theory Script

HOL4 formalizations are based on theory scripts. A *theory script* is
a stylized Standard ML (SML) file which

- is built up as a formalization progresses. It provides a
  user-maintained representation from which definitions and proofs may
  be run, either interactivelly or in batch mode.

- When a formalization is complete the script can be processed to
  create a succinct summary of the definitions and proofs.

The complete theory script for our example lives at XXXX. It starts

```
Theory tutorial
Ancestors
  pred_set list
Libs
  dep_rewrite
```

which specifies the following:

- The current theory is named `tutorial`.

- The ancestor theories (`Ancestors`) used by `tutorial` include at
  least `pred_set` and `list`, HOL4's standard theories for sets and
  lists. By virtue of being listed, these theories are `open`, meaning
  that elements of them can be accessed directly, *e.g.*, as `NULL`
  instead of `listTheory.NULL`.

- Further libraries (`Libs`) used include `dep_rewrite`. By being mentioned in
  the `Libs` list, the `dep_rewrite` module is also open, so that we may
  use `DEP_REWRITE_TAC` instead of `dep_rewrite.DEP_REWRITE_TAC`.
