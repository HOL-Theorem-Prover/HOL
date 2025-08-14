## `LEFT_AND_PFORALL_CONV`

``` hol4
PairRules.LEFT_AND_PFORALL_CONV : conv
```

------------------------------------------------------------------------

Moves a paired universal quantification of the left conjunct outwards
through a conjunction.

When applied to a term of the form `(!p. t) /\ u`, the conversion
`LEFT_AND_PFORALL_CONV` returns the theorem:

``` hol4
   |- (!p. t) /\ u = (!p'. t[p'/p] /\ u)
```

where `p'` is a primed variant of `p` that does not appear free in the
input term.

### Failure

Fails if applied to a term not of the form `(!p. t) /\ u`.

### See also

[`Conv.LEFT_AND_FORALL_CONV`](#Conv.LEFT_AND_FORALL_CONV),
[`PairRules.AND_PFORALL_CONV`](#PairRules.AND_PFORALL_CONV),
[`PairRules.PFORALL_AND_CONV`](#PairRules.PFORALL_AND_CONV),
[`PairRules.RIGHT_AND_PFORALL_CONV`](#PairRules.RIGHT_AND_PFORALL_CONV)
