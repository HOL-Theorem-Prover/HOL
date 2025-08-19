## `X_FUN_EQ_CONV`

``` hol4
Conv.X_FUN_EQ_CONV : (term -> conv)
```

------------------------------------------------------------------------

Performs extensionality conversion for functions (function equality).

The conversion `X_FUN_EQ_CONV` embodies the fact that two functions are
equal precisely when they give the same results for all values to which
they can be applied. For any variable `"x"` and equation `"f = g"`,
where `x` is of type `ty1` and `f` and `g` are functions of type
`ty1->ty2`, a call to `X_FUN_EQ_CONV "x" "f = g"` returns the theorem:

``` hol4
   |- (f = g) = (!x. f x = g x)
```

### Failure

`X_FUN_EQ_CONV x tm` fails if `x` is not a variable or if `tm` is not an
equation `f = g` where `f` and `g` are functions. Furthermore, if `f`
and `g` are functions of type `ty1->ty2`, then the variable `x` must
have type `ty1`; otherwise the conversion fails. Finally, failure also
occurs if `x` is free in either `f` or `g`.

### See also

[`Drule.EXT`](#Drule.EXT), [`Conv.FUN_EQ_CONV`](#Conv.FUN_EQ_CONV)
