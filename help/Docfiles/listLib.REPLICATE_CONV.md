## `REPLICATE_CONV`

``` hol4
listLib.REPLICATE_CONV : conv
```

------------------------------------------------------------------------

Computes by inference the result of replicating an element a given
number of times to form a list.

For an arbitrary expression `x` and numeral constant `n`, the result of
evaluating

``` hol4
   REPLICATE_CONV “REPLICATE n x”
```

is the theorem

``` hol4
   |- REPLICATE n x = [x;x;...;x]
```

where the list`[x;x;...;x]` is of length `n`.

### Example

Evaluating `REPLICATE_CONV “REPLICATE 3 [0;1;2;3]”` will return the
following theorem:

``` hol4
   |- REPLICATE 3 [0;1;2;3] = [[0;1;2;3]; [0;1;2;3]; [0;1;2;3]]
```

### Failure

`REPLICATE_CONV tm` fails if `tm` is not of the form described above.
