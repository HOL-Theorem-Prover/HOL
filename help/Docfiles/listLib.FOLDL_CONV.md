## `FOLDL_CONV`

``` hol4
listLib.FOLDL_CONV : conv -> conv
```

------------------------------------------------------------------------

Computes by inference the result of applying a function to the elements
of a list.

`FOLDL_CONV` takes a conversion `conv` and a term `tm` in the following
form:

``` hol4
   FOLDL f e [x0;...xn]
```

It returns the theorem

``` hol4
   |- FOLDL f e [x0;...xn] = tm'
```

where `tm'` is the result of applying the function `f` iteratively to
the successive elements of the list and the result of the previous
application starting from the tail end of the list. During each
iteration, an expression `f ei xi` is evaluated. The user supplied
conversion `conv` is used to derive a theorem

``` hol4
   |- f ei xi = e(i+1)
```

which is used in the next iteration.

### Failure

`FOLDL_CONV conv tm` fails if `tm` is not of the form described above.

### Example

To sum the elements of a list, one can use `FOLDL_CONV` with
`REDUCE_CONV` from the library `numLib`.

``` hol4
   - FOLDL_CONV numLib.REDUCE_CONV ``FOLDL $+ 0 [0;1;2;3]``;
   val it = |- FOLDL $+ 0 [0;1;2;3] = 6 : thm
```

In general, if the function `f` is an explicit lambda abstraction
`(\x x'. t[x,x'])`, the conversion should be in the form

``` hol4
   ((RATOR_CONV BETA_CONV) THENC BETA_CONV THENC conv'))
```

where `conv'` applied to `t[x,x']` returns the theorem

``` hol4
   |-t[x,x'] = e''.
```

### See also

[`listLib.FOLDR_CONV`](#listLib.FOLDR_CONV),
[`listLib.list_FOLD_CONV`](#listLib.list_FOLD_CONV)
