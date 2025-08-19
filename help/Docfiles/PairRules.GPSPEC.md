## `GPSPEC`

``` hol4
PairRules.GPSPEC : (thm -> thm)
```

------------------------------------------------------------------------

Specializes the conclusion of a theorem with unique pairs.

When applied to a theorem `A |- !p1...pn. t`, where the number of
universally quantified variables may be zero, `GPSPEC` returns
`A |- t[g1/p1]...[gn/pn]`, where the `gi` is paired structures of the
same structure as `pi` and made up of distinct variables , chosen by
`genvar`.

``` hol4
        A |- !p1...pn. t
   -------------------------  GPSPEC
    A |- t[g1/p1]...[gn/pn]
```

### Failure

Never fails.

`GPSPEC` is useful in writing derived inference rules which need to
specialize theorems while avoiding using any variables that may be
present elsewhere.

### See also

[`Drule.GSPEC`](#Drule.GSPEC), [`PairRules.PGEN`](#PairRules.PGEN),
[`PairRules.PGENL`](#PairRules.PGENL), [`Term.genvar`](#Term.genvar),
[`PairRules.PGEN_TAC`](#PairRules.PGEN_TAC),
[`PairRules.PSPEC`](#PairRules.PSPEC),
[`PairRules.PSPECL`](#PairRules.PSPECL),
[`PairRules.PSPEC_ALL`](#PairRules.PSPEC_ALL),
[`PairRules.PSPEC_TAC`](#PairRules.PSPEC_TAC),
[`PairRules.PSPEC_PAIR`](#PairRules.PSPEC_PAIR)
