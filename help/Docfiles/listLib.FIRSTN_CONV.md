## `FIRSTN_CONV`

``` hol4
listLib.FIRSTN_CONV : conv
```

------------------------------------------------------------------------

Computes by inference the result of taking the initial n elements of a
list.

For any object language list of the form `“[x0;...x(n-k);...;x(n-1)]”` ,
the result of evaluating

``` hol4
   FIRSTN_CONV “FIRSTN k [x0;...x(n-k);...;x(n-1)]”
```

is the theorem

``` hol4
   |- FIRSTN k [x0;...;x(n-k);...;x(n-1)] = [x0;...;x(n-k)]
```

### Failure

`FIRSTN_CONV tm` fails if `tm` is not of the form described above, or
`k` is greater than the length of the list.
