## `ABS_CONV`

``` hol4
Conv.ABS_CONV : conv -> conv
```

------------------------------------------------------------------------

Applies a conversion to the body of an abstraction.

If `c` is a conversion that maps a term `tm` to the theorem
`|- tm = tm'`, then the conversion `ABS_CONV c` maps abstractions of the
form `\x.tm` to theorems of the form:

``` hol4
   |- (\x.tm) = (\x.tm')
```

That is, `ABS_CONV c (\x.t)` applies `c` to the body of the abstraction
`\x.t`.

### Failure

`ABS_CONV c tm` fails if `tm` is not an abstraction or if `tm` has the
form `\x.t` but the conversion `c` fails when applied to the term `t`.
The function returned by `ABS_CONV c` may also fail if the ML function
`c:term->thm` is not, in fact, a conversion (i.e. a function that maps a
term `M` to a theorem `|- M = N`).

### Example

``` hol4
- ABS_CONV SYM_CONV (Term `\x. 1 = x`)
> val it = |- (\x. 1 = x) = (\x. x = 1) : thm
```

### See also

[`Conv.RAND_CONV`](#Conv.RAND_CONV),
[`Conv.RATOR_CONV`](#Conv.RATOR_CONV),
[`Conv.SUB_CONV`](#Conv.SUB_CONV),
[`Conv.BINDER_CONV`](#Conv.BINDER_CONV),
[`Conv.QUANT_CONV`](#Conv.QUANT_CONV),
[`Conv.STRIP_BINDER_CONV`](#Conv.STRIP_BINDER_CONV),
[`Conv.STRIP_QUANT_CONV`](#Conv.STRIP_QUANT_CONV)
