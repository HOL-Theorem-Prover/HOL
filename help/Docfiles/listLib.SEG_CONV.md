## `SEG_CONV`

``` hol4
listLib.SEG_CONV : conv
```

------------------------------------------------------------------------

Computes by inference the result of taking a segment of a list.

For any object language list of the form `“[x0;...x(n-1)]”` , the result
of evaluating

``` hol4
   SEG_CONV “SEG m k [x0;...;x(n-1)]”
```

is the theorem

``` hol4
   |- SEG m k [x0;...;x(n-1)] = [xk;...;x(m+k-1)]
```

### Failure

`SEG_CONV tm` fails if `tm` is not in the form described above or the
indexes `m` and `k` are not in the correct range, i.e., `m + k <= n`.

### Example

Evaluating the expression

``` hol4
   SEG_CONV “SEG 2 3[0;1;2;3;4;5]”;
```

returns the following theorem

``` hol4
   |- SEG 2 3[0;1;2;3;4;5] = [3;4]
```

### See also

[`listLib.FIRSTN_CONV`](#listLib.FIRSTN_CONV),
[`listLib.LASTN_CONV`](#listLib.LASTN_CONV),
[`listLib.BUTFIRSTN_CONV`](#listLib.BUTFIRSTN_CONV),
[`listLib.BUTLASTN_CONV`](#listLib.BUTLASTN_CONV),
[`listLib.LAST_CONV`](#listLib.LAST_CONV),
[`listLib.BUTLAST_CONV`](#listLib.BUTLAST_CONV)
