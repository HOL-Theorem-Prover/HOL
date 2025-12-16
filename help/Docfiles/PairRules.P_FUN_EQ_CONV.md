## `P_FUN_EQ_CONV`

``` hol4
PairRules.P_FUN_EQ_CONV : (term -> conv)
```

------------------------------------------------------------------------

Performs extensionality conversion for functions (function equality).

The conversion `P_FUN_EQ_CONV` embodies the fact that two functions are
equal precisely when they give the same results for all values to which
they can be applied. For any paired variable structure `"p"` and
equation `"f = g"`, where `p` is of type `ty1` and `f` and `g` are
functions of type `ty1->ty2`, a call to `P_FUN_EQ_CONV "p" "f = g"`
returns the theorem:

``` hol4
   |- (f = g) = (!p. f p = g p)
```

### Failure

`P_FUN_EQ_CONV p tm` fails if `p` is not a paired structure of variables
or if `tm` is not an equation `f = g` where `f` and `g` are functions.
Furthermore, if `f` and `g` are functions of type `ty1->ty2`, then the
pair `x` must have type `ty1`; otherwise the conversion fails. Finally,
failure also occurs if any of the variables in `p` is free in either `f`
or `g`.

### See also

[`Conv.FUN_EQ_CONV`](#Conv.FUN_EQ_CONV),
[`PairRules.PEXT`](#PairRules.PEXT)
