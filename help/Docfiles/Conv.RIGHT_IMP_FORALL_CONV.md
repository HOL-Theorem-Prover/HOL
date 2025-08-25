## `RIGHT_IMP_FORALL_CONV`

``` hol4
Conv.RIGHT_IMP_FORALL_CONV : conv
```

------------------------------------------------------------------------

Moves a universal quantification of the consequent outwards through an
implication.

When applied to a term of the form `P ==> (!x.Q)`, the conversion
`RIGHT_IMP_FORALL_CONV` returns the theorem:

``` hol4
   |- P ==> (!x.Q) = (!x'. P ==> (Q[x'/x]))
```

where `x'` is a primed variant of `x` that does not appear free in the
input term.

### Failure

Fails if applied to a term not of the form `P ==> (!x.Q)`.

### See also

[`Conv.FORALL_IMP_CONV`](#Conv.FORALL_IMP_CONV),
[`Conv.LEFT_IMP_EXISTS_CONV`](#Conv.LEFT_IMP_EXISTS_CONV)
