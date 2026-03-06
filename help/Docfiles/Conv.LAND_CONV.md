## `LAND_CONV`

``` hol4
Conv.LAND_CONV : conv -> conv
```

------------------------------------------------------------------------

Applies a conversion to the left-hand argument of a binary operator.

If `c` is a conversion that maps a term `t1` to the theorem
`|- t1 = t1'`, then the conversion `LAND_CONV c` maps applications of
the form `f t1 t2` to theorems of the form:

``` hol4
   |- f t1 t2 = f t1' t2
```

### Failure

`LAND_CONV c tm` fails if `tm` is not an application where the rator of
the application is in turn another application, as `f t1 t2`, or if `tm`
has this form but the conversion `c` fails when applied to the term
`t1`. The function returned by `LAND_CONV c` may also fail if the ML
function `c:term->thm` is not, in fact, a conversion (i.e. a function
that maps a term `t` to a theorem `|- t = t'`).

### Example

``` hol4
- LAND_CONV REDUCE_CONV (Term`(3 + 5) * 7`);
> val it = |- (3 + 5) * 7 = 8 * 7 : thm
```

### See also

[`Conv.ABS_CONV`](#Conv.ABS_CONV),
[`Conv.BINOP_CONV`](#Conv.BINOP_CONV),
[`Conv.RAND_CONV`](#Conv.RAND_CONV),
[`Conv.RATOR_CONV`](#Conv.RATOR_CONV),
[`numLib.REDUCE_CONV`](#numLib.REDUCE_CONV),
[`Conv.LHS_CONV`](#Conv.LHS_CONV)
