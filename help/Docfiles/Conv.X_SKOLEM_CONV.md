## `X_SKOLEM_CONV`

``` hol4
Conv.X_SKOLEM_CONV : (term -> conv)
```

------------------------------------------------------------------------

Introduces a user-supplied Skolem function.

`X_SKOLEM_CONV` takes two arguments. The first is a variable `f`, which
must range over functions of the appropriate type, and the second is a
term of the form `!x1...xn. ?y. P`. Given these arguments,
`X_SKOLEM_CONV` returns the theorem:

``` hol4
   |- (!x1...xn. ?y. P) = (?f. !x1...xn. tm[f x1 ... xn/y])
```

which expresses the fact that a skolem function `f` of the universally
quantified variables `x1...xn` may be introduced in place of the the
existentially quantified value `y`.

### Failure

`X_SKOLEM_CONV f tm` fails if `f` is not a variable, or if the input
term `tm` is not a term of the form `!x1...xn. ?y. P`, or if the
variable `f` is free in `tm`, or if the type of `f` does not match its
intended use as an `n`-place curried function from the variables
`x1...xn` to a value having the same type as `y`.

### See also

[`Conv.SKOLEM_CONV`](#Conv.SKOLEM_CONV)
