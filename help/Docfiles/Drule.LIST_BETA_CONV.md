## `LIST_BETA_CONV`

``` hol4
Drule.LIST_BETA_CONV : conv
```

------------------------------------------------------------------------

Performs an iterated beta conversion.

The conversion `LIST_BETA_CONV` maps terms of the form

``` hol4
   "(\x1 x2 ... xn. u) v1 v2 ... vn"
```

to the theorems of the form

``` hol4
   |- (\x1 x2 ... xn. u) v1 v2 ... vn = u[v1/x1][v2/x2] ... [vn/xn]
```

where `u[vi/xi]` denotes the result of substituting `vi` for all free
occurrences of `xi` in `u`, after renaming sufficient bound variables to
avoid variable capture.

### Failure

`LIST_BETA_CONV tm` fails if `tm` does not have the form
`"(\x1 ... xn. u) v1 ... vn"` for `n` greater than 0.

### Example

``` hol4
- LIST_BETA_CONV (Term `(\x y. x+y) 1 2`);
> val it = |- (\x y. x + y)1 2 = 1 + 2 : thm
```

### See also

[`Thm.BETA_CONV`](#Thm.BETA_CONV), [`Conv.BETA_RULE`](#Conv.BETA_RULE),
[`Tactic.BETA_TAC`](#Tactic.BETA_TAC),
[`Drule.RIGHT_BETA`](#Drule.RIGHT_BETA),
[`Drule.RIGHT_LIST_BETA`](#Drule.RIGHT_LIST_BETA)
