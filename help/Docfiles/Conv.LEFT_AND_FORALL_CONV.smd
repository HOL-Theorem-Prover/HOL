## `LEFT_AND_FORALL_CONV`

``` hol4
Conv.LEFT_AND_FORALL_CONV : conv
```

------------------------------------------------------------------------

Moves a universal quantification of the left conjunct outwards through a
conjunction.

When applied to a term of the form `(!x.P) /\ Q`, the conversion
`LEFT_AND_FORALL_CONV` returns the theorem:

``` hol4
   |- (!x.P) /\ Q = (!x'. P[x'/x] /\ Q)
```

where `x'` is a primed variant of `x` that does not appear free in the
input term.

### Failure

Fails if applied to a term not of the form `(!x.P) /\ Q`.

### See also

[`Conv.AND_FORALL_CONV`](#Conv.AND_FORALL_CONV),
[`Conv.FORALL_AND_CONV`](#Conv.FORALL_AND_CONV),
[`Conv.RIGHT_AND_FORALL_CONV`](#Conv.RIGHT_AND_FORALL_CONV)
