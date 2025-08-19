## `BETA_CONV`

``` hol4
Thm.BETA_CONV : conv
```

------------------------------------------------------------------------

Performs a single step of beta-conversion.

The conversion `BETA_CONV` maps a beta-redex `"(\x.u)v"` to the theorem

``` hol4
   |- (\x.u)v = u[v/x]
```

where `u[v/x]` denotes the result of substituting `v` for all free
occurrences of `x` in `u`, after renaming sufficient bound variables to
avoid variable capture. This conversion is one of the primitive
inference rules of the HOL system.

### Failure

`BETA_CONV tm` fails if `tm` is not a beta-redex.

### Example

``` hol4
- BETA_CONV (Term `(\x.x+1)y`);
> val it = |- (\x. x + 1)y = y + 1 :thm

- BETA_CONV (Term `(\x y. x+y)y`);
> val it = |- (\x y. x + y)y = (\y'. y + y') : thm
```

### See also

[`Conv.BETA_RULE`](#Conv.BETA_RULE),
[`Tactic.BETA_TAC`](#Tactic.BETA_TAC),
[`Drule.LIST_BETA_CONV`](#Drule.LIST_BETA_CONV),
[`PairedLambda.PAIRED_BETA_CONV`](#PairedLambda.PAIRED_BETA_CONV),
[`Drule.RIGHT_BETA`](#Drule.RIGHT_BETA),
[`Drule.RIGHT_LIST_BETA`](#Drule.RIGHT_LIST_BETA)
