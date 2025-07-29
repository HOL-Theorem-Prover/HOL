## `HALF_MK_PABS`

``` hol4
PairRules.HALF_MK_PABS : (thm -> thm)
```

------------------------------------------------------------------------

Converts a function definition to lambda-form.

When applied to a theorem `A |- !p. t1 p = t2`, whose conclusion is a
universally quantified equation, `HALF_MK_PABS` returns the theorem
`A |- t1 = (\p. t2)`.

``` hol4
    A |- !p. t1 p = t2
   --------------------  HALF_MK_PABS            [where p is not free in t1]
    A |- t1 = (\p. t2)
```

### Failure

Fails unless the theorem is a singly paired universally quantified
equation whose left-hand side is a function applied to the quantified
pair, or if any of the variables in the quantified pair is free in that
function.

### See also

[`jrhUtils.HALF_MK_ABS`](#jrhUtils.HALF_MK_ABS),
[`PairRules.PETA_CONV`](#PairRules.PETA_CONV),
[`PairRules.MK_PABS`](#PairRules.MK_PABS),
[`PairRules.MK_PEXISTS`](#PairRules.MK_PEXISTS)
