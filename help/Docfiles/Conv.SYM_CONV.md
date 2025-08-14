## `SYM_CONV`

``` hol4
Conv.SYM_CONV : conv
```

------------------------------------------------------------------------

Interchanges the left and right-hand sides of an equation.

When applied to an equational term `t1 = t2`, the conversion `SYM_CONV`
returns the theorem:

``` hol4
   |- (t1 = t2) = (t2 = t1)
```

### Failure

Fails if applied to a term that is not an equation.

### See also

[`Thm.SYM`](#Thm.SYM)
