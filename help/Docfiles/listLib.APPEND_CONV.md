## `APPEND_CONV`

``` hol4
listLib.APPEND_CONV : conv
```

------------------------------------------------------------------------

Computes by inference the result of appending two object-language lists.

For any pair of object language lists of the form `“[x1;...;xn]”` and
`“[y1;...;ym]”`, the result of evaluating

``` hol4
   APPEND_CONV “APPEND [x1;...;xn] [y1;...;ym]”
```

is the theorem

``` hol4
   |- APPEND [x1;...;xn] [y1;...;ym] = [x1;...;xn;y1;...;ym]
```

The length of either list (or both) may be 0.

### Failure

`APPEND_CONV tm` fails if `tm` is not of the form `“APPEND l1 l2”`,
where `l1` and `l2` are (possibly empty) object-language lists of the
forms `“[x1;...;xn]”` and `“[y1;...;ym]”`.
