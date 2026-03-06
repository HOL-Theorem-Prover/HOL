## `GENLIST_CONV`

``` hol4
listLib.GENLIST_CONV : conv -> conv
```

------------------------------------------------------------------------

Computes by inference the result of generating a list from a function.

For an arbitrary function `f`, numeral constant `n` and conversion to
evaluate `f` `conv`, the result of evaluating

``` hol4
   GENLIST_CONV conv “GENLIST f n”
```

is the theorem

``` hol4
   |- GENLIST f x = [x0;x1...xi...x(n-1)]
```

where each `xi` is the result of evaluating `conv “f i”`

### Example

Evaluating `GENLIST_CONV BETA_CONV “GENLIST (\n . n) 4”` will return the
following theorem:

``` hol4
   |- GENLIST (\n. n) 4 = [0; 1; 2; 3]
```

### Failure

`GENLIST_CONV tm` fails if `tm` is not of the form described above, or
if any call `conv “f i”` fails.
