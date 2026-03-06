## `IMP_TRANS`

``` hol4
Drule.IMP_TRANS : (thm -> thm -> thm)
```

------------------------------------------------------------------------

Implements the transitivity of implication.

When applied to theorems `A1 |- t1 ==> t2` and `A2 |- t2 ==> t3`, the
inference rule `IMP_TRANS` returns the theorem `A1 u A2 |- t1 ==> t3`.

``` hol4
    A1 |- t1 ==> t2   A2 |- t2 ==> t3
   -----------------------------------  IMP_TRANS
         A1 u A2 |- t1 ==> t3
```

### Failure

Fails unless the theorems are both implicative, with the consequent of
the first being the same as the antecedent of the second (up to
alpha-conversion).

### See also

[`Drule.IMP_ANTISYM_RULE`](#Drule.IMP_ANTISYM_RULE),
[`Thm.SYM`](#Thm.SYM), [`Thm.TRANS`](#Thm.TRANS)
