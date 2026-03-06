## `PEXISTS_OR_CONV`

``` hol4
PairRules.PEXISTS_OR_CONV : conv
```

------------------------------------------------------------------------

Moves a paired existential quantification inwards through a disjunction.

When applied to a term of the form `?p. t \/ u`, the conversion
`PEXISTS_OR_CONV` returns the theorem:

``` hol4
   |- (?p. t \/ u) = (?p. t) \/ (?p. u)
```

### Failure

Fails if applied to a term not of the form `?p. t \/ u`.

### See also

[`Conv.EXISTS_OR_CONV`](#Conv.EXISTS_OR_CONV),
[`PairRules.OR_PEXISTS_CONV`](#PairRules.OR_PEXISTS_CONV),
[`PairRules.LEFT_OR_PEXISTS_CONV`](#PairRules.LEFT_OR_PEXISTS_CONV),
[`PairRules.RIGHT_OR_PEXISTS_CONV`](#PairRules.RIGHT_OR_PEXISTS_CONV)
