## `SNOC_CONV`

``` hol4
listLib.SNOC_CONV : conv
```

------------------------------------------------------------------------

Computes by inference the result of adding an element to the tail end of
a list.

`SNOC_CONV` takes a term `tm` in the following form:

``` hol4
   SNOC x [x0;...xn]
```

It returns the theorem

``` hol4
   |- SNOC x [x0;...xn] = [x0;...xn;x]
```

where the right-hand side is the list in the canonical form, i.e.,
constructed with only the constructor `CONS`.

### Failure

`SNOC_CONV tm` fails if `tm` is not of the form described above.

### Example

Evaluating

``` hol4
   SNOC_CONV “SNOC 5[0;1;2;3;4]”;
```

returns the following theorem:

``` hol4
   |- SNOC 5[0;1;2;3;4] = [0;1;2;3;4;5]
```

### See also

[`listLib.FOLDL_CONV`](#listLib.FOLDL_CONV),
[`listLib.FOLDR_CONV`](#listLib.FOLDR_CONV),
[`listLib.list_FOLD_CONV`](#listLib.list_FOLD_CONV)
