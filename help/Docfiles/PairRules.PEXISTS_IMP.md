## `PEXISTS_IMP`

``` hol4
PairRules.PEXISTS_IMP : (term -> thm -> thm)
```

------------------------------------------------------------------------

Existentially quantifies both the antecedent and consequent of an
implication.

When applied to a paired structure of variables `p` and a theorem
`A |- t1 ==> t2`, the inference rule `PEXISTS_IMP` returns the theorem
`A |- (?p. t1) ==> (?p. t2)`, provided no variable in `p` is free in the
assumptions.

``` hol4
         A |- t1 ==> t2
   --------------------------  EXISTS_IMP "x"   [where x is not free in A]
    A |- (?x.t1) ==> (?x.t2)
```

### Failure

Fails if the theorem is not implicative, or if the term is not a paired
structure of variables, of if any variable in the pair is free in the
assumption list.

### See also

[`Drule.EXISTS_IMP`](#Drule.EXISTS_IMP),
[`PairRules.PEXISTS_EQ`](#PairRules.PEXISTS_EQ)
