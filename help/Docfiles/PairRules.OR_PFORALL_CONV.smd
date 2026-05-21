## `OR_PFORALL_CONV`

``` hol4
PairRules.OR_PFORALL_CONV : conv
```

------------------------------------------------------------------------

Moves a paired universal quantification outwards through a disjunction.

When applied to a term of the form `(!p. t) \/ (!p. u)`, where no
variables from `p` are free in either `t` nor `u`, `OR_PFORALL_CONV`
returns the theorem:

``` hol4
   |- (!p. t) \/ (!p. u) = (!p. t \/ u)
```

### Failure

`OR_PFORALL_CONV` fails if it is applied to a term not of the form
`(!p. t) \/ (!p. u)`, or if it is applied to a term `(!p. t) \/ (!p. u)`
in which the variables from `p` are free in either `t` or `u`.

### See also

[`Conv.OR_FORALL_CONV`](#Conv.OR_FORALL_CONV),
[`PairRules.PFORALL_OR_CONV`](#PairRules.PFORALL_OR_CONV),
[`PairRules.LEFT_OR_PFORALL_CONV`](#PairRules.LEFT_OR_PFORALL_CONV),
[`PairRules.RIGHT_OR_PFORALL_CONV`](#PairRules.RIGHT_OR_PFORALL_CONV)
