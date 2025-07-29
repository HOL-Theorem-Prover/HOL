## `BINOP_CONV`

``` hol4
Conv.BINOP_CONV : conv -> conv
```

------------------------------------------------------------------------

Applies a conversion to both arguments of a binary operator.

If `c` is a conversion that when applied to `t1` returns the theorem
`|- t1 = t1'` and when applied to `t2` returns the theorem
`|- t2 = t2'`, then `` BINOP_CONV c (Term`f t1 t2`) `` will return the
theorem

``` hol4
   |- f t1 t2 = f t1' t2'
```

### Failure

`BINOP_CONV c t` will fail if `t` is not of the general form `f t1 t2`,
or if `c` fails when applied to either `t1` or `t2`, or if `c` fails to
return theorems of the form `|- t1 = t1'` and `|- t2 = t2'` when applied
to those arguments. (The latter case would imply that `c` wasn't a
conversion at all.)

### Example

``` hol4
- BINOP_CONV REDUCE_CONV (Term`3 * 4 + 6 * 7`);
> val it = |- 3 * 4 + 6 * 7 = 12 + 42 : thm
```

### See also

[`Conv.FORK_CONV`](#Conv.FORK_CONV),
[`Conv.LAND_CONV`](#Conv.LAND_CONV),
[`Conv.RAND_CONV`](#Conv.RAND_CONV),
[`Conv.RATOR_CONV`](#Conv.RATOR_CONV),
[`numLib.REDUCE_CONV`](#numLib.REDUCE_CONV)
