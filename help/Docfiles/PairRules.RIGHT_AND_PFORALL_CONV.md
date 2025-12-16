## `RIGHT_AND_PFORALL_CONV`

``` hol4
PairRules.RIGHT_AND_PFORALL_CONV : conv
```

------------------------------------------------------------------------

Moves a paired universal quantification of the right conjunct outwards
through a conjunction.

When applied to a term of the form `t /\ (!p. u)`, the conversion
`RIGHT_AND_PFORALL_CONV` returns the theorem:

``` hol4
   |- t /\ (!p. u) = (!p'. t /\ (u[p'/p]))
```

where `p'` is a primed variant of the pair `p` that does not contain any
variables free in the input term.

### Failure

Fails if applied to a term not of the form `t /\ (!p. u)`.

### See also

[`Conv.RIGHT_AND_FORALL_CONV`](#Conv.RIGHT_AND_FORALL_CONV),
[`PairRules.AND_PFORALL_CONV`](#PairRules.AND_PFORALL_CONV),
[`PairRules.PFORALL_AND_CONV`](#PairRules.PFORALL_AND_CONV),
[`PairRules.LEFT_AND_PFORALL_CONV`](#PairRules.LEFT_AND_PFORALL_CONV)
