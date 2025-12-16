## `LEFT_AND_PEXISTS_CONV`

``` hol4
PairRules.LEFT_AND_PEXISTS_CONV : conv
```

------------------------------------------------------------------------

Moves a paired existential quantification of the left conjunct outwards
through a conjunction.

When applied to a term of the form `(?p. t) /\ u`, the conversion
`LEFT_AND_PEXISTS_CONV` returns the theorem:

``` hol4
   |- (?p. t) /\ u = (?p'. t[p'/p] /\ u)
```

where `p'` is a primed variant of the pair `p` that does not contains
variables free in the input term.

### Failure

Fails if applied to a term not of the form `(?p. t) /\ u`.

### See also

[`Conv.LEFT_AND_EXISTS_CONV`](#Conv.LEFT_AND_EXISTS_CONV),
[`PairRules.AND_PEXISTS_CONV`](#PairRules.AND_PEXISTS_CONV),
[`PairRules.PEXISTS_AND_CONV`](#PairRules.PEXISTS_AND_CONV),
[`PairRules.RIGHT_AND_PEXISTS_CONV`](#PairRules.RIGHT_AND_PEXISTS_CONV)
