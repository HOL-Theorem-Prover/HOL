## `PRE_CONV`

``` hol4
reduceLib.PRE_CONV : conv
```

------------------------------------------------------------------------

Calculates by inference the predecessor of a numeral.

If `n` is a numeral (e.g. `0`, `1`, `2`, `3`,...), then
`PRE_CONV "PRE n"` returns the theorem:

``` hol4
   |- PRE n = s
```

where `s` is the numeral that denotes the predecessor of the natural
number denoted by `n`.

### Failure

`PRE_CONV tm` fails unless `tm` is of the form ``` ``PRE n`` ```, where
`n` is a numeral.

### Example

``` hol4
> PRE_CONV ``PRE 0``;
val it = |- PRE 0 = 0 : thm

> PRE_CONV ``PRE 1``;
val it = |- PRE 1 = 0 : thm

> PRE_CONV ``PRE 22``;
val it = |- PRE 22 = 21 : thm
```
