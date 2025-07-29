## `PGEN`

``` hol4
PairRules.PGEN : (term -> thm -> thm)
```

------------------------------------------------------------------------

Generalizes the conclusion of a theorem.

When applied to a paired structure of variables `p` and a theorem
`A |- t`, the inference rule `PGEN` returns the theorem `A |- !p. t`,
provided that no variable in `p` occurs free in the assumptions `A`.
There is no compulsion that the variables of `p` should be free in `t`.

``` hol4
      A |- t
   ------------  PGEN "p"               [where p does not occur free in A]
    A |- !p. t
```

### Failure

Fails if `p` is not a paired structure of variables, of if any variable
in `p` is free in the assumptions.

### See also

[`Thm.GEN`](#Thm.GEN), [`PairRules.PGENL`](#PairRules.PGENL),
[`PairRules.PGEN_TAC`](#PairRules.PGEN_TAC),
[`PairRules.PSPEC`](#PairRules.PSPEC),
[`PairRules.PSPECL`](#PairRules.PSPECL),
[`PairRules.PSPEC_ALL`](#PairRules.PSPEC_ALL),
[`PairRules.PSPEC_TAC`](#PairRules.PSPEC_TAC)
