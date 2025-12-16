## `SKOLEM_CONV`

``` hol4
Conv.SKOLEM_CONV : conv
```

------------------------------------------------------------------------

Proves the existence of a Skolem function.

When applied to an argument of the form `!x1...xn. ?y. P`, the
conversion `SKOLEM_CONV` returns the theorem:

``` hol4
   |- (!x1...xn. ?y. P) = (?y'. !x1...xn. P[y' x1 ... xn/y])
```

where `y'` is a primed variant of `y` not free in the input term.

### Failure

`SKOLEM_CONV tm` fails if `tm` is not a term of the form
`!x1...xn. ?y. P`.

### See also

[`Conv.X_SKOLEM_CONV`](#Conv.X_SKOLEM_CONV)
