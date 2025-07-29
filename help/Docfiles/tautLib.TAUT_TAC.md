## `TAUT_TAC`

``` hol4
tautLib.TAUT_TAC : tactic
```

------------------------------------------------------------------------

Tautology checker. Proves propositional goals (and instances of them).

Given a goal that is an instance of a propositional formula, this tactic
will prove the goal provided it is valid. A propositional formula is a
term containing only Boolean constants, Boolean-valued variables,
Boolean equalities, implications, conjunctions, disjunctions, negations
and Boolean-valued conditionals. An instance of a formula is the formula
with one or more of the variables replaced by terms of the same type.
The tactic accepts goals with or without universal quantifiers for the
variables.

### Failure

Fails if the conclusion of the goal is not an instance of a
propositional formula or if the instance is not a valid formula.

### See also

[`tautLib.TAUT_CONV`](#tautLib.TAUT_CONV),
[`tautLib.TAUT_PROVE`](#tautLib.TAUT_PROVE),
[`tautLib.PTAUT_TAC`](#tautLib.PTAUT_TAC)
