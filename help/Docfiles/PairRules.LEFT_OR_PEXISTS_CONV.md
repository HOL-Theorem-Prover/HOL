## `LEFT_OR_PEXISTS_CONV`

``` hol4
PairRules.LEFT_OR_PEXISTS_CONV : conv
```

------------------------------------------------------------------------

Moves a paired existential quantification of the left disjunct outwards
through a disjunction.

When applied to a term of the form `(?p. t) \/ u`, the conversion
`LEFT_OR_PEXISTS_CONV` returns the theorem:

``` hol4
   |- (?p. t) \/ u = (?p'. t[p'/p] \/ u)
```

where `p'` is a primed variant of the pair `p` that does not contain any
variables free in the input term.

### Failure

Fails if applied to a term not of the form `(?p. t) \/ u`.

### See also

[`Conv.LEFT_OR_EXISTS_CONV`](#Conv.LEFT_OR_EXISTS_CONV),
[`PairRules.PEXISTS_OR_CONV`](#PairRules.PEXISTS_OR_CONV),
[`PairRules.OR_PEXISTS_CONV`](#PairRules.OR_PEXISTS_CONV),
[`PairRules.RIGHT_OR_PEXISTS_CONV`](#PairRules.RIGHT_OR_PEXISTS_CONV)
