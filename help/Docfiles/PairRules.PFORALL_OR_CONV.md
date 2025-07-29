## `PFORALL_OR_CONV`

``` hol4
PairRules.PFORALL_OR_CONV : conv
```

------------------------------------------------------------------------

Moves a paired universal quantification inwards through a disjunction.

When applied to a term of the form `!p. t \/ u`, where no variable in
`p` is free in both `t` and `u`, `PFORALL_OR_CONV` returns a theorem of
one of three forms, depending on occurrences of the variables from `p`
in `t` and `u`. If variables from `p` are free in `t` but not in `u`,
then the theorem:

``` hol4
   |- (!p. t \/ u) = (!p. t) \/ u
```

is returned. If variables from `p` are free in `u` but none are free in
`t`, then the result is:

``` hol4
   |- (!p. t \/ u) = t \/ (!t. u)
```

And if no variable from `p` is free in either `t` nor `u`, then the
result is:

``` hol4
   |- (!p. t \/ u) = (!p. t) \/ (!p. u)
```

### Failure

`PFORALL_OR_CONV` fails if it is applied to a term not of the form
`!p. t \/ u`, or if it is applied to a term `!p. t \/ u` in which
variables from `p` are free in both `t` and `u`.

### See also

[`Conv.FORALL_OR_CONV`](#Conv.FORALL_OR_CONV),
[`PairRules.OR_PFORALL_CONV`](#PairRules.OR_PFORALL_CONV),
[`PairRules.LEFT_OR_PFORALL_CONV`](#PairRules.LEFT_OR_PFORALL_CONV),
[`PairRules.RIGHT_OR_PFORALL_CONV`](#PairRules.RIGHT_OR_PFORALL_CONV)
