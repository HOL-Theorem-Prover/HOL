## `PFORALL_IMP_CONV`

``` hol4
PairRules.PFORALL_IMP_CONV : conv
```

------------------------------------------------------------------------

Moves a paired universal quantification inwards through an implication.

When applied to a term of the form `!p. t ==> u`, where variables from
`p` are not free in both `t` and `u`, `PFORALL_IMP_CONV` returns a
theorem of one of three forms, depending on occurrences of the variables
from `p` in `t` and `u`. If variables from `p` are free in `t` but none
are in `u`, then the theorem:

``` hol4
   |- (!p. t ==> u) = (?p. t) ==> u
```

is returned. If variables from `p` are free in `u` but none are in `t`,
then the result is:

``` hol4
   |- (!p. t ==> u) = t ==> (!p. u)
```

And if no variable from `p` is free in either `t` nor `u`, then the
result is:

``` hol4
   |- (!p. t ==> u) = (?p. t) ==> (!p. u)
```

### Failure

`PFORALL_IMP_CONV` fails if it is applied to a term not of the form
`!p. t ==> u`, or if it is applied to a term `!p. t ==> u` in which
variables from `p` are free in both `t` and `u`.

### See also

[`Conv.FORALL_IMP_CONV`](#Conv.FORALL_IMP_CONV),
[`PairRules.LEFT_IMP_PEXISTS_CONV`](#PairRules.LEFT_IMP_PEXISTS_CONV),
[`PairRules.RIGHT_IMP_PFORALL_CONV`](#PairRules.RIGHT_IMP_PFORALL_CONV)
