## `EQ_MP`

``` hol4
Thm.EQ_MP : thm -> thm -> thm
```

------------------------------------------------------------------------

Equality version of the Modus Ponens rule.

When applied to theorems `A1 |- t1 = t2` and `A2 |- t1`, the inference
rule `EQ_MP` returns the theorem `A1 u A2 |- t2`.

``` hol4
    A1 |- t1 = t2   A2 |- t1
   --------------------------  EQ_MP
         A1 u A2 |- t2
```

### Failure

Fails unless the first theorem is equational and its left side is the
same as the conclusion of the second theorem (and is therefore of type
`bool`), up to alpha-conversion.

### See also

[`Thm.EQ_IMP_RULE`](#Thm.EQ_IMP_RULE),
[`Drule.IMP_ANTISYM_RULE`](#Drule.IMP_ANTISYM_RULE), [`Thm.MP`](#Thm.MP)
