## `RIGHT_IMP_EXISTS_CONV`

``` hol4
Conv.RIGHT_IMP_EXISTS_CONV : conv
```

------------------------------------------------------------------------

Moves an existential quantification of the consequent outwards through
an implication.

When applied to a term of the form `P ==> (?x.Q)`, the conversion
`RIGHT_IMP_EXISTS_CONV` returns the theorem:

``` hol4
   |- P ==> (?x.Q) = (?x'. P ==> (Q[x'/x]))
```

where `x'` is a primed variant of `x` that does not appear free in the
input term.

### Failure

Fails if applied to a term not of the form `P ==> (?x.Q)`.

### See also

[`Conv.EXISTS_IMP_CONV`](#Conv.EXISTS_IMP_CONV),
[`Conv.LEFT_IMP_FORALL_CONV`](#Conv.LEFT_IMP_FORALL_CONV)
