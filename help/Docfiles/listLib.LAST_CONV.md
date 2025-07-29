## `LAST_CONV`

``` hol4
listLib.LAST_CONV : conv
```

------------------------------------------------------------------------

Computes by inference the result of taking the last element of a list.

For any object language list of the form `“[x0;...x(n-1)]”` , the result
of evaluating

``` hol4
   LAST_CONV “LAST [x0;...;x(n-1)]”
```

is the theorem

``` hol4
   |- LAST [x0;...;x(n-1)] = x(n-1)
```

### Failure

`LAST_CONV tm` fails if `tm` is an empty list.
