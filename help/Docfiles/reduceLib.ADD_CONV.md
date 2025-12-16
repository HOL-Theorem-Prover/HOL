## `ADD_CONV`

``` hol4
reduceLib.ADD_CONV : conv
```

------------------------------------------------------------------------

Calculates by inference the sum of two numerals.

If `m` and `n` are numerals (e.g. `0`, `1`, `2`, `3`,...) of type
`:num`, then ``` ADD_CONV ``m + n`` ``` returns the theorem:

``` hol4
   |- m + n = s
```

where `s` is the numeral that denotes the sum of the natural numbers
denoted by `m` and `n`.

### Failure

`ADD_CONV tm` fails unless `tm` is of the form ``` ``m + n`` ```, where
`m` and `n` are numerals of type `:num`.

### Example

``` hol4
> ADD_CONV ``75 + 25``;
val it = |- 75 + 25 = 100 : thm
```

### See also

[`reduceLib.MUL_CONV`](#reduceLib.MUL_CONV)
