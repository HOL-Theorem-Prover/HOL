## `LEFT_OR_PFORALL_CONV`

``` hol4
PairRules.LEFT_OR_PFORALL_CONV : conv
```

------------------------------------------------------------------------

Moves a paired universal quantification of the left disjunct outwards
through a disjunction.

When applied to a term of the form `(!p. t) \/ u`, the conversion
`LEFT_OR_FORALL_CONV` returns the theorem:

``` hol4
   |- (!p. t) \/ u = (!p'. t[p'/p] \/ u)
```

where `p'` is a primed variant of the pair `p` that does not contain any
variables that appear free in the input term.

### Failure

Fails if applied to a term not of the form `(!p. t) \/ u`.

### See also

[`Conv.LEFT_OR_FORALL_CONV`](#Conv.LEFT_OR_FORALL_CONV),
[`PairRules.OR_PFORALL_CONV`](#PairRules.OR_PFORALL_CONV),
[`PairRules.PFORALL_OR_CONV`](#PairRules.PFORALL_OR_CONV),
[`PairRules.RIGHT_OR_PFORALL_CONV`](#PairRules.RIGHT_OR_PFORALL_CONV)
