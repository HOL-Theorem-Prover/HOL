# Introduction

The goal of this tutorial is to show, in some detail, how proofs are
actually done in HOL4. Towards that end, from a blank slate we
formalize a basic result of automata theory, namely a proof of
equivalence between the languages definable by deterministic
finite-state automata (DFAs) and their non-deterministic analogues
(NFAs).

We assume a working version of HOL4 plus some basic knowledge of the
system:

- how to start it up, whether standalone or in the editor of your choice;
- how to create and work with a theory script;
- how to start and work with a proof attempt in a goal manager; and
- what a tactic is and how to apply one to the current goal;

HOL4 provides a large and extensible collection of inference tools but
a relatively small set of tactics usually suffices. We will introduce
them as we go along. See
[Cheatsheet](https://hol-theorem-prover.org/cheatsheet.html) for a
comprehensive range of useful tactics.

## Theory Scripts (Reminder)

HOL4 formalizations are based on theory scripts. A *theory script* is
an enhanced Standard ML (SML) file which

- is built up as a formalization progresses. It provides a
  user-maintained representation from which definitions and proofs may
  be run, either interactivelly or in batch mode.

- When a formalization is complete the script can be processed to
  create a succinct summary of the definitions made and theorems
  proved.

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
  lists. Moreover, by virtue of being mentioned, these theories are
  `open`ed, meaning that elements of them can be accessed directly,
  e.g., as `NULL` instead of `listTheory.NULL`.

- Further libraries (`Libs`) used include `dep_rewrite`. By being mentioned in
  the `Libs` list, the `dep_rewrite` module is opened, so that we may
  use `DEP_REWRITE_TAC` instead of `dep_rewrite.DEP_REWRITE_TAC`.
