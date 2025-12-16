## `RHS_CONV`

``` hol4
Conv.RHS_CONV : conv -> conv
```

------------------------------------------------------------------------

Applies a conversion to the right-hand argument of an equality.

If `c` is a conversion that maps a term `t2` to the theorem
`|- t2 = t2'`, then the conversion `RHS_CONV c` maps applications of the
form `t1 = t2` to theorems of the form:

``` hol4
   |- (t1 = t2) = (t1 = t2')
```

### Failure

`RHS_CONV c tm` fails if `tm` is not an an equality `t1 = t2`, or if
`tm` has this form but the conversion `c` fails when applied to the term
`t2`. The function returned by `RHS_CONV c` may also fail if the ML
function `c:term->thm` is not, in fact, a conversion (i.e. a function
that maps a term `t` to a theorem `|- t = t'`).

### Example

``` hol4
- RHS_CONV REDUCE_CONV (Term`7 = (3 + 5)`);
> val it = |- (7 = (3 + 5)) = (7 = 8) : thm
```

### Comments

`RAND_CONV` is similar, but works for any binary operator

### See also

[`Conv.BINOP_CONV`](#Conv.BINOP_CONV),
[`Conv.LHS_CONV`](#Conv.LHS_CONV),
[`numLib.REDUCE_CONV`](#numLib.REDUCE_CONV),
[`Conv.RAND_CONV`](#Conv.RAND_CONV)
