## `MK_PSELECT`

``` hol4
PairRules.MK_PSELECT : (thm -> thm)
```

------------------------------------------------------------------------

Quantifies both sides of a universally quantified equational theorem
with the choice quantifier.

When applied to a theorem `A |- !p. t1 = t2`, the inference rule
`MK_PSELECT` returns the theorem `A |- (@x. t1) = (@x. t2)`.

``` hol4
       A |- !p. t1 = t2
   --------------------------  MK_PSELECT
    A |- (@p. t1) = (@p. t2)
```

### Failure

Fails unless the theorem is a singly paired universally quantified
equation.

### See also

[`PairRules.PSELECT_EQ`](#PairRules.PSELECT_EQ),
[`PairRules.MK_PABS`](#PairRules.MK_PABS)
