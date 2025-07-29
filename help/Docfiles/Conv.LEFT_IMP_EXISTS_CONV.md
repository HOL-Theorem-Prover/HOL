## `LEFT_IMP_EXISTS_CONV`

``` hol4
Conv.LEFT_IMP_EXISTS_CONV : conv
```

------------------------------------------------------------------------

Moves an existential quantification of the antecedent outwards through
an implication.

When applied to a term of the form `(?x.P) ==> Q`, the conversion
`LEFT_IMP_EXISTS_CONV` returns the theorem:

``` hol4
   |- (?x.P) ==> Q = (!x'. P[x'/x] ==> Q)
```

where `x'` is a primed variant of `x` that does not appear free in the
input term.

### Failure

Fails if applied to a term not of the form `(?x.P) ==> Q`.

### See also

[`Conv.FORALL_IMP_CONV`](#Conv.FORALL_IMP_CONV),
[`Conv.RIGHT_IMP_FORALL_CONV`](#Conv.RIGHT_IMP_FORALL_CONV)
