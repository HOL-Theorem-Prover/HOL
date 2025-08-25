## `RIGHT_AND_FORALL_CONV`

``` hol4
Conv.RIGHT_AND_FORALL_CONV : conv
```

------------------------------------------------------------------------

Moves a universal quantification of the right conjunct outwards through
a conjunction.

When applied to a term of the form `P /\ (!x.Q)`, the conversion
`RIGHT_AND_FORALL_CONV` returns the theorem:

``` hol4
   |- P /\ (!x.Q) = (!x'. P /\ (Q[x'/x]))
```

where `x'` is a primed variant of `x` that does not appear free in the
input term.

### Failure

Fails if applied to a term not of the form `P /\ (!x.Q)`.

### See also

[`Conv.AND_FORALL_CONV`](#Conv.AND_FORALL_CONV),
[`Conv.FORALL_AND_CONV`](#Conv.FORALL_AND_CONV),
[`Conv.LEFT_AND_FORALL_CONV`](#Conv.LEFT_AND_FORALL_CONV)
