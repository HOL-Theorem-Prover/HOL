## `LENGTH_CONV`

``` hol4
listLib.LENGTH_CONV : conv
```

------------------------------------------------------------------------

Computes by inference the length of an object-language list.

For any object language list of the form `“[x1;x2;...;xn]”`, where `x1`,
`x2`, ..., `xn` are arbitrary terms of the same type, the result of
evaluating

``` hol4
   LENGTH_CONV “LENGTH [x1;x2;...;xn]”
```

is the theorem

``` hol4
   |- LENGTH [x1;x2;...;xn] = n
```

where `n` is the numeral constant that denotes the length of the list.

### Failure

`LENGTH_CONV tm` fails if `tm` is not of the form
`“LENGTH [x1;x2;...;xn]”` or `“LENGTH []”`.
