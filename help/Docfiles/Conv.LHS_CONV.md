## `LHS_CONV`

``` hol4
Conv.LHS_CONV : conv -> conv
```

------------------------------------------------------------------------

Applies a conversion to the left-hand argument of an equality.

If `c` is a conversion that maps a term `t1` to the theorem
`|- t1 = t1'`, then the conversion `LHS_CONV c` maps applications of the
form `t1 = t2` to theorems of the form:

``` hol4
   |- (t1 = t2) = (t1' = t2)
```

### Failure

`LHS_CONV c tm` fails if `tm` is not an an equality `t1 = t2`, or if
`tm` has this form but the conversion `c` fails when applied to the term
`t1`. The function returned by `LHS_CONV c` may also fail if the ML
function `c:term->thm` is not, in fact, a conversion (i.e. a function
that maps a term `t` to a theorem `|- t = t'`).

### Example

``` hol4
- LHS_CONV REDUCE_CONV (Term`(3 + 5) = 7`);
> val it = |- ((3 + 5) = 7) = (8 = 7) : thm
```

### Comments

`LAND_CONV` is similar, but works for any binary operator

### See also

[`Conv.BINOP_CONV`](#Conv.BINOP_CONV),
[`Conv.RHS_CONV`](#Conv.RHS_CONV),
[`numLib.REDUCE_CONV`](#numLib.REDUCE_CONV),
[`Conv.LAND_CONV`](#Conv.LAND_CONV)
