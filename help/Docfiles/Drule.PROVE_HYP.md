## `PROVE_HYP`

``` hol4
Drule.PROVE_HYP : thm -> thm -> thm
```

------------------------------------------------------------------------

Eliminates a provable assumption from a theorem.

When applied to two theorems, `PROVE_HYP` returns a theorem having the
conclusion of the second. The new hypotheses are the union of the two
hypothesis sets (first deleting, however, the conclusion of the first
theorem from the hypotheses of the second).

``` hol4
     A1 |- t1     A2 |- t2
   ------------------------  PROVE_HYP
    A1 u (A2 - {t1}) |- t2
```

### Failure

Never fails.

### Comments

This is the Cut rule. It is not necessary for the conclusion of the
first theorem to be the same as an assumption of the second, but
`PROVE_HYP` is otherwise of doubtful value.

### See also

[`Thm.DISCH`](#Thm.DISCH), [`Thm.MP`](#Thm.MP),
[`Drule.UNDISCH`](#Drule.UNDISCH)
