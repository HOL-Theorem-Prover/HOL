## `PFORALL_AND_CONV`

``` hol4
PairRules.PFORALL_AND_CONV : conv
```

------------------------------------------------------------------------

Moves a paired universal quantification inwards through a conjunction.

When applied to a term of the form `!p. t /\ u`, the conversion
`PFORALL_AND_CONV` returns the theorem:

``` hol4
   |- (!p. t /\ u) = (!p. t) /\ (!p. u)
```

### Failure

Fails if applied to a term not of the form `!p. t /\ u`.

### See also

[`Conv.FORALL_AND_CONV`](#Conv.FORALL_AND_CONV),
[`PairRules.AND_PFORALL_CONV`](#PairRules.AND_PFORALL_CONV),
[`PairRules.LEFT_AND_PFORALL_CONV`](#PairRules.LEFT_AND_PFORALL_CONV),
[`PairRules.RIGHT_AND_PFORALL_CONV`](#PairRules.RIGHT_AND_PFORALL_CONV)
