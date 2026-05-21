## `PTAUT_TAC`

``` hol4
tautLib.PTAUT_TAC : tactic
```

------------------------------------------------------------------------

Tautology checker. Proves propositional goals.

Given a goal with a conclusion that contains only Boolean constants,
Boolean-valued variables, Boolean equalities, implications,
conjunctions, disjunctions, negations and Boolean-valued conditionals,
this tactic will prove the goal if it is valid. If all the variables in
the conclusion are universally quantified, this tactic will also reduce
an invalid goal to false.

### Failure

Fails if the conclusion of the goal is not of the form
`!x1 ... xn. f[x1,...,xn]` where `f[x1,...,xn]` is a propositional
formula (except that the variables do not have to be universally
quantified if the goal is valid).

### See also

[`tautLib.PTAUT_CONV`](#tautLib.PTAUT_CONV),
[`tautLib.PTAUT_PROVE`](#tautLib.PTAUT_PROVE),
[`tautLib.TAUT_TAC`](#tautLib.TAUT_TAC)
