## `FORALL_OR_CONV`

``` hol4
Conv.FORALL_OR_CONV : conv
```

------------------------------------------------------------------------

Moves a universal quantification inwards through a disjunction.

When applied to a term of the form `!x. P \/ Q`, where `x` is not free
in both `P` and `Q`, `FORALL_OR_CONV` returns a theorem of one of three
forms, depending on occurrences of the variable `x` in `P` and `Q`. If
`x` is free in `P` but not in `Q`, then the theorem:

``` hol4
   |- (!x. P \/ Q) = (!x.P) \/ Q
```

is returned. If `x` is free in `Q` but not in `P`, then the result is:

``` hol4
   |- (!x. P \/ Q) = P \/ (!x.Q)
```

And if `x` is free in neither `P` nor `Q`, then the result is:

``` hol4
   |- (!x. P \/ Q) = (!x.P) \/ (!x.Q)
```

### Failure

`FORALL_OR_CONV` fails if it is applied to a term not of the form
`!x. P \/ Q`, or if it is applied to a term `!x. P \/ Q` in which the
variable `x` is free in both `P` and `Q`.

### See also

[`Conv.OR_FORALL_CONV`](#Conv.OR_FORALL_CONV),
[`Conv.LEFT_OR_FORALL_CONV`](#Conv.LEFT_OR_FORALL_CONV),
[`Conv.RIGHT_OR_FORALL_CONV`](#Conv.RIGHT_OR_FORALL_CONV)
