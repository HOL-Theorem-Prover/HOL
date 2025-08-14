## `NOT_EXISTS_CONV`

``` hol4
Conv.NOT_EXISTS_CONV : conv
```

------------------------------------------------------------------------

Moves negation inwards through an existential quantification.

When applied to a term of the form `~(?x.P)`, the conversion
`NOT_EXISTS_CONV` returns the theorem:

``` hol4
   |- ~(?x.P) = !x.~P
```

### Failure

Fails if applied to a term not of the form `~(?x.P)`.

### See also

[`Conv.EXISTS_NOT_CONV`](#Conv.EXISTS_NOT_CONV),
[`Conv.FORALL_NOT_CONV`](#Conv.FORALL_NOT_CONV),
[`Conv.NOT_FORALL_CONV`](#Conv.NOT_FORALL_CONV)
