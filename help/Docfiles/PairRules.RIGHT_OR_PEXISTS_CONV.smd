## `RIGHT_OR_PEXISTS_CONV`

``` hol4
PairRules.RIGHT_OR_PEXISTS_CONV : conv
```

------------------------------------------------------------------------

Moves a paired existential quantification of the right disjunct outwards
through a disjunction.

When applied to a term of the form `t \/ (?p. u)`, the conversion
`RIGHT_OR_PEXISTS_CONV` returns the theorem:

``` hol4
   |- t \/ (?p. u) = (?p'. t \/ (u[p'/p]))
```

where `p'` is a primed variant of the pair `p` that does not contain any
variables free in the input term.

### Failure

Fails if applied to a term not of the form `t \/ (?p. u)`.

### See also

[`Conv.RIGHT_OR_EXISTS_CONV`](#Conv.RIGHT_OR_EXISTS_CONV),
[`PairRules.OR_PEXISTS_CONV`](#PairRules.OR_PEXISTS_CONV),
[`PairRules.PEXISTS_OR_CONV`](#PairRules.PEXISTS_OR_CONV),
[`PairRules.LEFT_OR_PEXISTS_CONV`](#PairRules.LEFT_OR_PEXISTS_CONV)
