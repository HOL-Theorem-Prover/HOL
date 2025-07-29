## `CNF_CONV`

``` hol4
normalForms.CNF_CONV : conv
```

------------------------------------------------------------------------

Converts a formula into Conjunctive Normal Form (CNF).

Given a formula consisting of truths, falsities, conjunctions,
disjunctions, negations, equivalences, conditionals, and universal and
existential quantifiers, `CNF_CONV` will convert it to the canonical
form:

``` hol4
?a_1 ... a_k.
  (!v_1 ... v_m1. P_1 \/ ... \/ P_n1) /\
  ...                                 /\
  (!v_1 ... v_mp. P_1 \/ ... \/ P_np)
```

The `P_ij` are literals: possibly-negated atoms. In first-order logic an
atom is a formula consisting of a top-level relation symbol applied to
first-order terms: function symbols and variables. In higher-order logic
there is no distinction between formulas and terms, so the concept of
atom is not well-formed. Note also that the `a_i` existentially bound
variables may be functions, as a result of Skolemization.

### Failure

`CNF_CONV` should never fail.

### Example

``` hol4
- CNF_CONV ``!x. P x ==> ?y z. Q y \/ ~?z. P z /\ Q z``;
> val it =
    |- (!x. P x ==> ?y z. Q y \/ ~?z. P z /\ Q z) =
       ?y. !x x'. Q (y x) \/ ~P x' \/ ~Q x' \/ ~P x : thm
```

### Example

``` hol4
- CNF_CONV ``~(~(x = y) = z) = ~(x = ~(y = z))``;
> val it = |- (~(~(x = y) = z) = ~(x = ~(y = z))) = T : thm
```
