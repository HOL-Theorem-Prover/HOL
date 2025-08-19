## `RAND_CONV`

``` hol4
Conv.RAND_CONV : (conv -> conv)
```

------------------------------------------------------------------------

Applies a conversion to the operand of an application.

If `c` is a conversion that maps a term `"t2"` to the theorem
`|- t2 = t2'`, then the conversion `RAND_CONV c` maps applications of
the form `"t1 t2"` to theorems of the form:

``` hol4
   |- (t1 t2) = (t1 t2')
```

That is, `RAND_CONV c "t1 t2"` applies `c` to the operand of the
application `"t1 t2"`.

### Failure

`RAND_CONV c tm` fails if `tm` is not an application or if `tm` has the
form `"t1 t2"` but the conversion `c` fails when applied to the term
`t2`. The function returned by `RAND_CONV c` may also fail if the ML
function `c:term->thm` is not, in fact, a conversion (i.e. a function
that maps a term `t` to a theorem `|- t = t'`).

### Example

``` hol4
- RAND_CONV numLib.num_CONV (Term `SUC 2`);
> val it = |- SUC 2 = SUC(SUC 1) : thm
```

### See also

[`Conv.ABS_CONV`](#Conv.ABS_CONV),
[`Conv.BINOP_CONV`](#Conv.BINOP_CONV),
[`Conv.LAND_CONV`](#Conv.LAND_CONV),
[`Conv.RATOR_CONV`](#Conv.RATOR_CONV),
[`Conv.SUB_CONV`](#Conv.SUB_CONV), [`Conv.RHS_CONV`](#Conv.RHS_CONV)
