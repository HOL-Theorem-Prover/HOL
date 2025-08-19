## `FUN_EQ_CONV`

``` hol4
Conv.FUN_EQ_CONV : conv
```

------------------------------------------------------------------------

Equates normal and extensional equality for two functions.

The conversion `FUN_EQ_CONV` embodies the fact that two functions are
equal precisely when they give the same results for all values to which
they can be applied. When supplied with a term argument of the form
`f = g`, where `f` and `g` are functions of type `ty1->ty2`,
`FUN_EQ_CONV` returns the theorem:

``` hol4
   |- (f = g) = (!x. f x = g x)
```

where `x` is a variable of type `ty1` chosen by the conversion.

### Failure

`FUN_EQ_CONV tm` fails if `tm` is not an equation `f = g`, where `f` and
`g` are functions.

Used for proving equality of functions.

### See also

[`Drule.EXT`](#Drule.EXT), [`Conv.X_FUN_EQ_CONV`](#Conv.X_FUN_EQ_CONV)
