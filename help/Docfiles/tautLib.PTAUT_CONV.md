## `PTAUT_CONV`

``` hol4
tautLib.PTAUT_CONV : conv
```

------------------------------------------------------------------------

Tautology checker. Proves closed propositional formulae true or false.

Given a term of the form `"!x1 ... xn. t"` where `t` contains only
Boolean constants, Boolean-valued variables, Boolean equalities,
implications, conjunctions, disjunctions, negations and Boolean-valued
conditionals, and all the variables in `t` appear in `x1 ... xn`, the
conversion `PTAUT_CONV` proves the term to be either true or false, that
is, one of the following theorems is returned:

``` hol4
   |- (!x1 ... xn. t) = T
   |- (!x1 ... xn. t) = F
```

This conversion also accepts propositional terms that are not fully
universally quantified. However, for such a term, the conversion will
only succeed if the term is valid.

### Failure

Fails if the term is not of the form `"!x1 ... xn. f[x1,...,xn]"` where
`f[x1,...,xn]` is a propositional formula (except that the variables do
not have to be universally quantified if the term is valid).

### Example

``` hol4
#PTAUT_CONV ``!x y z w. (((x \/ ~y) ==> z) /\ (z ==> ~w) /\ w) ==> y``;
|- (!x y z w. (x \/ ~y ==> z) /\ (z ==> ~w) /\ w ==> y) = T

#PTAUT_CONV ``(((x \/ ~y) ==> z) /\ (z ==> ~w) /\ w) ==> y``;
|- (x \/ ~y ==> z) /\ (z ==> ~w) /\ w ==> y = T

#PTAUT_CONV ``!x. x = T``;
|- (!x. x = T) = F

#PTAUT_CONV ``x = T``;
Uncaught exception:
HOL_ERR
```

### See also

[`tautLib.PTAUT_PROVE`](#tautLib.PTAUT_PROVE),
[`tautLib.PTAUT_TAC`](#tautLib.PTAUT_TAC),
[`tautLib.TAUT_CONV`](#tautLib.TAUT_CONV)
