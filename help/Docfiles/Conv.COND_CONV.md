## `COND_CONV`

``` hol4
Conv.COND_CONV : conv
```

------------------------------------------------------------------------

Simplifies conditional terms.

The conversion `COND_CONV` simplifies a conditional term `"c => u | v"`
if the condition `c` is either the constant `T` or the constant `F` or
if the two terms `u` and `v` are equivalent up to alpha-conversion. The
theorems returned in these three cases have the forms:

``` hol4
   |- (T => u | v) = u

   |- (F => u | v) = u

   |- (c => u | u) = u
```

### Failure

`COND_CONV tm` fails if `tm` is not a conditional `"c => u | v"`, where
`c` is `T` or `F`, or `u` and `v` are alpha-equivalent.
