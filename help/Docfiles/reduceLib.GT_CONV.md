## `GT_CONV`

``` hol4
reduceLib.GT_CONV : conv
```

------------------------------------------------------------------------

Proves result of greater-than ordering on two numerals.

If `m` and `n` are both numerals (e.g. `0`, `1`, `2`, `3`,...) of type
`:num`, then `GT_CONV "m > n"` returns the theorem:

``` hol4
   |- (m > n) = T
```

if the natural number denoted by `m` is greater than that denoted by
`n`, or

``` hol4
   |- (m > n) = F
```

otherwise.

### Failure

`GT_CONV tm` fails unless `tm` is of the form ``` ``m > n`` ```, where
`m` and `n` are numerals of type `:num`.

### Example

``` hol4
> GT_CONV ``100 > 10``;
val it = |- 100 > 10 <=> T : thm

> GT_CONV ``15 > 15``;
val it = |- 15 > 15 <=> F : thm

> GT_CONV ``11 > 27``;
val it = |- 11 > 27 = F : thm
```

### See also

[`reduceLib.LT_CONV`](#reduceLib.LT_CONV)
