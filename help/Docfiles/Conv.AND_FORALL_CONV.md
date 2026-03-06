## `AND_FORALL_CONV`

``` hol4
Conv.AND_FORALL_CONV : conv
```

------------------------------------------------------------------------

Moves a universal quantification outwards through a conjunction.

When applied to a term of the form `(!x.P) /\ (!x.Q)`, the conversion
`AND_FORALL_CONV` returns the theorem:

``` hol4
   |- (!x.P) /\ (!x.Q) = (!x. P /\ Q)
```

### Failure

Fails if applied to a term not of the form `(!x.P) /\ (!x.Q)`.

### Comments

It may be easier to use higher order rewriting with `FORALL_AND_THM`.

### See also

[`Conv.FORALL_AND_CONV`](#Conv.FORALL_AND_CONV),
[`Conv.LEFT_AND_FORALL_CONV`](#Conv.LEFT_AND_FORALL_CONV),
[`Conv.RIGHT_AND_FORALL_CONV`](#Conv.RIGHT_AND_FORALL_CONV)
