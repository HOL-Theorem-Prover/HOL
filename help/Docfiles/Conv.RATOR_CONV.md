## `RATOR_CONV`

``` hol4
Conv.RATOR_CONV : (conv -> conv)
```

------------------------------------------------------------------------

Applies a conversion to the operator of an application.

If `c` is a conversion that maps a term `"t1"` to the theorem
`|- t1 = t1'`, then the conversion `RATOR_CONV c` maps applications of
the form `"t1 t2"` to theorems of the form:

``` hol4
   |- (t1 t2) = (t1' t2)
```

That is, `RATOR_CONV c "t1 t2"` applies `c` to the operand of the
application `"t1 t2"`.

### Failure

`RATOR_CONV c tm` fails if `tm` is not an application or if `tm` has the
form `"t1 t2"` but the conversion `c` fails when applied to the term
`t1`. The function returned by `RATOR_CONV c` may also fail if the ML
function `c:term->thm` is not, in fact, a conversion (i.e. a function
that maps a term `t` to a theorem `|- t = t'`).

### Example

``` hol4
- RATOR_CONV BETA_CONV (Term `(\x y. x + y) 1 2`);
> val it = |- (\x y. x + y)1 2 = (\y. 1 + y) 2 : thm
```

### See also

[`Conv.ABS_CONV`](#Conv.ABS_CONV), [`Conv.RAND_CONV`](#Conv.RAND_CONV),
[`Conv.SUB_CONV`](#Conv.SUB_CONV)
