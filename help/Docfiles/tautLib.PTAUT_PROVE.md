## `PTAUT_PROVE`

``` hol4
tautLib.PTAUT_PROVE : term -> thm
```

------------------------------------------------------------------------

Tautology checker. Proves propositional formulae.

Given a term that contains only Boolean constants, Boolean-valued
variables, Boolean equalities, implications, conjunctions, disjunctions,
negations and Boolean-valued conditionals, `PTAUT_PROVE` returns the
term as a theorem if it is valid. The variables in the term may be
universally quantified.

### Failure

Fails if the term is not a valid propositional formula.

### Example

``` hol4
#PTAUT_PROVE ``!x y z w. (((x \/ ~y) ==> z) /\ (z ==> ~w) /\ w) ==> y``;
|- !x y z w. (x \/ ~y ==> z) /\ (z ==> ~w) /\ w ==> y

#PTAUT_PROVE ``(((x \/ ~y) ==> z) /\ (z ==> ~w) /\ w) ==> y``;
|- (x \/ ~y ==> z) /\ (z ==> ~w) /\ w ==> y

#PTAUT_PROVE ``!x. x = T``;
Uncaught exception:
HOL_ERR

#PTAUT_PROVE ``x = T``;
Uncaught exception:
HOL_ERR
```

### See also

[`tautLib.PTAUT_CONV`](#tautLib.PTAUT_CONV),
[`tautLib.PTAUT_TAC`](#tautLib.PTAUT_TAC),
[`tautLib.TAUT_PROVE`](#tautLib.TAUT_PROVE)
