## `FORK_CONV`

``` hol4
Conv.FORK_CONV : (conv * conv) -> conv
```

------------------------------------------------------------------------

Applies a pair of conversions to the arguments of a binary operator.

If the conversion `c1` maps a term `t1` to the theorem `|- t1 = t1'`,
and the conversion `c2` maps `t2` to `|- t2 = t2'`, then the conversion
`FORK_CONV (c1,c2)` maps terms of the form `f t1 t2` to theorems of the
form `|- f t1 t2 = f t1' t2'`.

### Failure

`FORK_CONV (c1,c2) t` will fail if `t` is not of the general form
`f t1 t2`, or if `c1` fails when applied to `t1`, or if `c2` fails when
applied to `t2`, or if `c1` or `c2` aren't really conversions, and
thereby fail to return appropriate equational theorems.

### Example

``` hol4
- FORK_CONV (BETA_CONV,REDUCE_CONV) (Term`(\x. x + 1)y * (10 DIV 3)`);
> val it = |- (\x. x + 1) y * (10 DIV 3) = (y + 1) * 3 : thm
```

### See also

[`Conv.BINOP_CONV`](#Conv.BINOP_CONV),
[`Conv.LAND_CONV`](#Conv.LAND_CONV),
[`Conv.RAND_CONV`](#Conv.RAND_CONV),
[`Conv.RATOR_CONV`](#Conv.RATOR_CONV),
[`numLib.REDUCE_CONV`](#numLib.REDUCE_CONV)
