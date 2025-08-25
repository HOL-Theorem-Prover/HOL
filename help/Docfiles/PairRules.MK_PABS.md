## `MK_PABS`

``` hol4
PairRules.MK_PABS : (thm -> thm)
```

------------------------------------------------------------------------

Abstracts both sides of an equation.

When applied to a theorem `A |- !p. t1 = t2`, whose conclusion is a
paired universally quantified equation, `MK_PABS` returns the theorem
`A |- (\p. t1) = (\p. t2)`.

``` hol4
        A |- !p. t1 = t2
   --------------------------  MK_PABS
    A |- (\p. t1) = (\p. t2)
```

### Failure

Fails unless the theorem is a (singly) paired universally quantified
equation.

### See also

[`Drule.MK_ABS`](#Drule.MK_ABS), [`PairRules.PABS`](#PairRules.PABS),
[`PairRules.HALF_MK_PABS`](#PairRules.HALF_MK_PABS),
[`PairRules.MK_PEXISTS`](#PairRules.MK_PEXISTS)
