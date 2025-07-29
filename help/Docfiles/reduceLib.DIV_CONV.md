## `DIV_CONV`

``` hol4
reduceLib.DIV_CONV : conv
```

------------------------------------------------------------------------

Calculates by inference the result of dividing, with truncation, one
numeral by another.

If `m` and `n` are numerals (e.g. `0`, `1`, `2`, `3`,...), then
``` DIV_CONV ``m DIV n`` ``` returns the theorem:

``` hol4
   |- m DIV n = s
```

where `s` is the numeral that denotes the result of dividing the natural
number denoted by `m` by the natural number denoted by `n`, with
truncation.

### Failure

`DIV_CONV tm` fails unless `tm` is of the form ``` ``m DIV n`` ```,
where `m` and `n` are numerals, or if `n` denotes zero.

### Example

``` hol4
> DIV_CONV ``0 DIV 0``;
Exception-
   HOL_ERR
  {message = "attempt to divide by zero", origin_function = "DIV_CONV",
  origin_structure = "Arithconv"} raised

> DIV_CONV ``x DIV 12``;
Exception- ...

> DIV_CONV ``0 DIV 12``;
val it = |- 0 DIV 12 = 0 : thm

> DIV_CONV ``7 DIV 2``;
val it = |- 7 DIV 2 = 3 : thm
```
