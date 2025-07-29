## `MK_PFORALL`

``` hol4
PairRules.MK_PFORALL : (thm -> thm)
```

------------------------------------------------------------------------

Universally quantifies both sides of a universally quantified equational
theorem.

When applied to a theorem `A |- !p. t1 = t2`, the inference rule
`MK_PFORALL` returns the theorem `A |- (!x. t1) = (!x. t2)`.

``` hol4
       A |- !p. t1 = t2
   --------------------------  MK_PFORALL
    A |- (!p. t1) = (!p. t2)
```

### Failure

Fails unless the theorem is a singly paired universally quantified
equation.

### See also

[`PairRules.PFORALL_EQ`](#PairRules.PFORALL_EQ),
[`PairRules.LIST_MK_PFORALL`](#PairRules.LIST_MK_PFORALL),
[`PairRules.MK_PABS`](#PairRules.MK_PABS)
