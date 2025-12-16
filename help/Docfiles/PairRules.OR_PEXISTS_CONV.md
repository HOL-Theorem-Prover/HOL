## `OR_PEXISTS_CONV`

``` hol4
PairRules.OR_PEXISTS_CONV : conv
```

------------------------------------------------------------------------

Moves a paired existential quantification outwards through a
disjunction.

When applied to a term of the form `(?p. t) \/ (?p. u)`, the conversion
`OR_PEXISTS_CONV` returns the theorem:

``` hol4
   |- (?p. t) \/ (?p. u) = (?p. t \/ u)
```

### Failure

Fails if applied to a term not of the form `(?p. t) \/ (?p. u)`.

### See also

[`Conv.OR_EXISTS_CONV`](#Conv.OR_EXISTS_CONV),
[`PairRules.PEXISTS_OR_CONV`](#PairRules.PEXISTS_OR_CONV),
[`PairRules.LEFT_OR_PEXISTS_CONV`](#PairRules.LEFT_OR_PEXISTS_CONV),
[`PairRules.RIGHT_OR_PEXISTS_CONV`](#PairRules.RIGHT_OR_PEXISTS_CONV)
