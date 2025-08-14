## `MK_PEXISTS`

``` hol4
PairRules.MK_PEXISTS : (thm -> thm)
```

------------------------------------------------------------------------

Existentially quantifies both sides of a universally quantified
equational theorem.

When applied to a theorem `A |- !p. t1 = t2`, the inference rule
`MK_PEXISTS` returns the theorem `A |- (?x. t1) = (?x. t2)`.

``` hol4
       A |- !p. t1 = t2
   --------------------------  MK_PEXISTS
    A |- (?p. t1) = (?p. t2)
```

### Failure

Fails unless the theorem is a singly paired universally quantified
equation.

### See also

[`PairRules.PEXISTS_EQ`](#PairRules.PEXISTS_EQ),
[`PairRules.PGEN`](#PairRules.PGEN),
[`PairRules.LIST_MK_PEXISTS`](#PairRules.LIST_MK_PEXISTS),
[`PairRules.MK_PABS`](#PairRules.MK_PABS)
