## `PEXISTS_EQ`

``` hol4
PairRules.PEXISTS_EQ : (term -> thm -> thm)
```

------------------------------------------------------------------------

Existentially quantifies both sides of an equational theorem.

When applied to a paired structure of variables `p` and a theorem whose
conclusion is equational:

``` hol4
    A |- t1 = t2
```

the inference rule `PEXISTS_EQ` returns the theorem:

``` hol4
    A |- (?p. t1) = (?p. t2)
```

provided the none of the variables in `p` is not free in any of the
assumptions.

``` hol4
          A |- t1 = t2
   --------------------------  PEXISTS_EQ "p"      [where p is not free in A]
    A |- (?p. t1) = (?p. t2)
```

### Failure

Fails unless the theorem is equational with both sides having type
`bool`, or if the term is not a paired structure of variables, or if any
variable in the pair to be quantified over is free in any of the
assumptions.

### See also

[`Drule.EXISTS_EQ`](#Drule.EXISTS_EQ),
[`PairRules.PEXISTS_IMP`](#PairRules.PEXISTS_IMP),
[`PairRules.PFORALL_EQ`](#PairRules.PFORALL_EQ),
[`PairRules.MK_PEXISTS`](#PairRules.MK_PEXISTS),
[`PairRules.PSELECT_EQ`](#PairRules.PSELECT_EQ)
