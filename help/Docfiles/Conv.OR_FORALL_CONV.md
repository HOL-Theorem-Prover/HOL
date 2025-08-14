## `OR_FORALL_CONV`

``` hol4
Conv.OR_FORALL_CONV : conv
```

------------------------------------------------------------------------

Moves a universal quantification outwards through a disjunction.

When applied to a term of the form `(!x.P) \/ (!x.Q)`, where `x` is free
in neither `P` nor `Q`, `OR_FORALL_CONV` returns the theorem:

``` hol4
   |- (!x. P) \/ (!x. Q) = (!x. P \/ Q)
```

### Failure

`OR_FORALL_CONV` fails if it is applied to a term not of the form
`(!x.P) \/ (!x.Q)`, or if it is applied to a term `(!x.P) \/ (!x.Q)` in
which the variable `x` is free in either `P` or `Q`.

### See also

[`Conv.FORALL_OR_CONV`](#Conv.FORALL_OR_CONV),
[`Conv.LEFT_OR_FORALL_CONV`](#Conv.LEFT_OR_FORALL_CONV),
[`Conv.RIGHT_OR_FORALL_CONV`](#Conv.RIGHT_OR_FORALL_CONV)
