## `BUTLAST_CONV`

``` hol4
listLib.BUTLAST_CONV : conv
```

------------------------------------------------------------------------

Computes by inference the result of stripping the last element of a
list.

For any object language list of the form `“[x0;...x(n-1)]”` , the result
of evaluating

``` hol4
   BUTLAST_CONV “BUTLAST [x0;...;x(n-1)]”
```

is the theorem

``` hol4
   |- BUTLAST [x0;...;x(n-1)] = [x0;...; x(n-2)]
```

### Failure

`BUTLAST_CONV tm` fails if `tm` is an empty list.
