## `SUM_CONV`

``` hol4
listLib.SUM_CONV : conv
```

------------------------------------------------------------------------

Computes by inference the result of summing the elements of a list.

For any object language list of the form `“[x1;x2;...;xn]”`, where `x1`,
`x2`, ..., `xn` are numeral constants, the result of evaluating

``` hol4
   SUM_CONV “SUM [x1;x2;...;xn]”
```

is the theorem

``` hol4
   |- SUM [x1;x2;...;xn] = n
```

where `n` is the numeral constant that denotes the sum of the elements
of the list.

### Example

Evaluating `SUM_CONV “SUM [0;1;2;3]”` will return the following theorem:

``` hol4
   |- SUM [0;1;2;3] = 6
```

### Failure

`SUM_CONV tm` fails if `tm` is not of the form described above.

### See also

[`listLib.FOLDL_CONV`](#listLib.FOLDL_CONV),
[`listLib.FOLDR_CONV`](#listLib.FOLDR_CONV),
[`listLib.list_FOLD_CONV`](#listLib.list_FOLD_CONV)
