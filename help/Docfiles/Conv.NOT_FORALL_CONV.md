## `NOT_FORALL_CONV`

``` hol4
Conv.NOT_FORALL_CONV : conv
```

------------------------------------------------------------------------

Moves negation inwards through a universal quantification.

When applied to a term of the form `~(!x.P)`, the conversion
`NOT_FORALL_CONV` returns the theorem:

``` hol4
   |- ~(!x.P) = ?x.~P
```

It is irrelevant whether `x` occurs free in `P`.

### Failure

Fails if applied to a term not of the form `~(!x.P)`.

### See also

[`Conv.EXISTS_NOT_CONV`](#Conv.EXISTS_NOT_CONV),
[`Conv.FORALL_NOT_CONV`](#Conv.FORALL_NOT_CONV),
[`Conv.NOT_EXISTS_CONV`](#Conv.NOT_EXISTS_CONV)
