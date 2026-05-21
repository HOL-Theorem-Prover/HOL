## `FORALL_NOT_CONV`

``` hol4
Conv.FORALL_NOT_CONV : conv
```

------------------------------------------------------------------------

Moves a universal quantification inwards through a negation.

When applied to a term of the form `!x.~P`, the conversion
`FORALL_NOT_CONV` returns the theorem:

``` hol4
   |- (!x.~P) = ~(?x. P)
```

### Failure

Fails if applied to a term not of the form `!x.~P`.

### See also

[`Conv.EXISTS_NOT_CONV`](#Conv.EXISTS_NOT_CONV),
[`Conv.NOT_EXISTS_CONV`](#Conv.NOT_EXISTS_CONV),
[`Conv.NOT_FORALL_CONV`](#Conv.NOT_FORALL_CONV)
