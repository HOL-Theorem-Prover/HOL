## `SCANR_CONV`

``` hol4
listLib.SCANR_CONV : conv -> conv
```

------------------------------------------------------------------------

Computes by inference the result of applying a function to the elements
of a list.

`SCANR_CONV` takes a conversion `conv` and a term `tm` in the following
form:

``` hol4
   SCANR f e0 [xn;...;x1]
```

It returns the theorem

``` hol4
   |- SCANR f e0 [xn;...;x1] = [en; ...;e1;e0]
```

where `ei` is the result of applying the function `f` to the result of
the previous iteration and the current element, i.e.,
`ei = f e(i-1) xi`. The iteration starts from the right-hand side (the
tail) of the list. The user supplied conversion `conv` is used to derive
a theorem

``` hol4
   |- f e(i-1) xi = ei
```

which is used in the next iteration.

### Failure

`SCANR_CONV conv tm` fails if `tm` is not of the form described above,
or failure occurs when evaluating `conv “f e(i-1) xi”`.

### Example

To sum the elements of a list and save the result at each step, one can
use `SCANR_CONV` with `ADD_CONV` from the library `num_lib`.

``` hol4
   - load_library_in_place num_lib;
   - SCANR_CONV Num_lib.ADD_CONV “SCANR $+ 0 [1;2;3]”;
   |- SCANR $+ 0[1;2;3] = [6;5;3;0]
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

[`listLib.SCANL_CONV`](#listLib.SCANL_CONV),
[`listLib.FOLDL_CONV`](#listLib.FOLDL_CONV),
[`listLib.FOLDR_CONV`](#listLib.FOLDR_CONV),
[`listLib.list_FOLD_CONV`](#listLib.list_FOLD_CONV)
