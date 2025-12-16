## `TAUT_PROVE`

``` hol4
tautLib.TAUT_PROVE : term -> thm
```

------------------------------------------------------------------------

Tautology checker. Proves propositional formulae (and instances of
them).

Given an instance of a valid propositional formula, `TAUT_PROVE` returns
the instance of the formula as a theorem. A propositional formula is a
term containing only Boolean constants, Boolean-valued variables,
Boolean equalities, implications, conjunctions, disjunctions, negations
and Boolean-valued conditionals. An instance of a formula is the formula
with one or more of the variables replaced by terms of the same type.
The conversion accepts terms with or without universal quantifiers for
the variables.

### Failure

Fails if the term is not an instance of a propositional formula or if
the instance is not a valid formula.

### Example

``` hol4
#TAUT_PROVE
# ``!x n y. ((((n = 1) \/ ~x) ==> y) /\ (y ==> ~(n < 0)) /\ (n < 0)) ==> x``;
|- !x n y. ((n = 1) \/ ~x ==> y) /\ (y ==> ~n < 0) /\ n < 0 ==> x

#TAUT_PROVE ``((((n = 1) \/ ~x) ==> y) /\ (y ==> ~(n < 0)) /\ (n < 0)) ==> x``;
|- ((n = 1) \/ ~x ==> y) /\ (y ==> ~n < 0) /\ n < 0 ==> x

#TAUT_PROVE ``!n. (n < 0) \/ (n = 0)``;
Uncaught exception:
HOL_ERR
```

### See also

[`tautLib.TAUT_CONV`](#tautLib.TAUT_CONV),
[`tautLib.TAUT_TAC`](#tautLib.TAUT_TAC),
[`tautLib.PTAUT_PROVE`](#tautLib.PTAUT_PROVE)
