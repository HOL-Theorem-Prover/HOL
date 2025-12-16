## `AND_EXISTS_CONV`

``` hol4
Conv.AND_EXISTS_CONV : conv
```

------------------------------------------------------------------------

Moves an existential quantification outwards through a conjunction.

When applied to a term of the form `(?x.P) /\ (?x.Q)`, where `x` is free
in neither `P` nor `Q`, `AND_EXISTS_CONV` returns the theorem:

``` hol4
   |- (?x. P) /\ (?x. Q) = (?x. P /\ Q)
```

### Failure

`AND_EXISTS_CONV` fails if it is applied to a term not of the form
`(?x.P) /\ (?x.Q)`, or if it is applied to a term `(?x.P) /\ (?x.Q)` in
which the variable `x` is free in either `P` or `Q`.

### Comments

It may be easier to use higher order rewriting with some of
`BOTH_EXISTS_AND_THM`, `LEFT_EXISTS_AND_THM`, and
`RIGHT_EXISTS_AND_THM`.

### See also

[`Conv.EXISTS_AND_CONV`](#Conv.EXISTS_AND_CONV),
[`Conv.LEFT_AND_EXISTS_CONV`](#Conv.LEFT_AND_EXISTS_CONV),
[`Conv.RIGHT_AND_EXISTS_CONV`](#Conv.RIGHT_AND_EXISTS_CONV)
