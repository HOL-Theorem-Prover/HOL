## `SUB_CONV`

``` hol4
Conv.SUB_CONV : conv -> conv
```

------------------------------------------------------------------------

Applies a conversion to the top-level subterms of a term.

For any conversion `c`, the function returned by `SUB_CONV c` is a
conversion that applies `c` to all the top-level subterms of a term. Its
implementation is

``` hol4
  fun SUB_CONV c = TRY_CONV (COMB_CONV c ORELSEC ABS_CONV c)
```

### Example

If the conversion `c` maps `t` to `|- t = t'`, then `SUB_CONV c` maps an
abstraction ``` ``\x.t`` ``` to the theorem:

``` hol4
   |- (\x.t) = (\x.t')
```

That is, ``` SUB_CONV c ``\x.t`` ``` applies `c` to the body of the
abstraction ``` ``\x.t`` ```. If `c` is a conversion that maps
``` ``t1`` ``` to the theorem `|- t1 = t1'` and ``` ``t2`` ``` to the
theorem `|- t2 = t2'`, then the conversion `SUB_CONV c` maps an
application ``` ``t1 t2`` ``` to the theorem:

``` hol4
   |- (t1 t2) = (t1' t2')
```

That is, ``` SUB_CONV c ``t1 t2`` ``` applies `c` to the both the
operator `t1` and the operand `t2` of the application ``` ``t1 t2`` ```.
Finally, for any conversion `c`, the function returned by `SUB_CONV c`
acts as the identity conversion on variables and constants. That is, if
``` ``t`` ``` is a variable or constant, then ``` SUB_CONV c ``t`` ```
raises the `UNCHANGED` exception.

### Failure

`SUB_CONV c tm` fails if `tm` is an abstraction ``` ``\x.t`` ``` and the
conversion `c` fails when applied to `t`, or if `tm` is an application
``` ``t1 t2`` ``` and the conversion `c` fails when applied to either
`t1` or `t2`. The function returned by `SUB_CONV c` may also fail if the
ML function `c:term->thm` is not, in fact, a conversion (i.e. a function
that maps a term `t` to a theorem `|- t = t'`).

### See also

[`Conv.ABS_CONV`](#Conv.ABS_CONV), [`Conv.COMB_CONV`](#Conv.COMB_CONV),
[`Conv.RAND_CONV`](#Conv.RAND_CONV),
[`Conv.RATOR_CONV`](#Conv.RATOR_CONV)
