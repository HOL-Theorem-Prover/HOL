## `IS_EL_CONV`

``` hol4
listLib.IS_EL_CONV : conv -> conv
```

------------------------------------------------------------------------

Computes by inference the result of testing whether a list contains a
certain element.

`IS_EL_CONV` takes a conversion `conv` and a term `tm` in the following
form:

``` hol4
   IS_EL x [x0;...xn]
```

It returns the theorem

``` hol4
   |- IS_EL x [x0;...xn] = F
```

if for every `xi` occurred in the list, `conv “x = xi”` returns a
theorem `|- P xi = F`, otherwise, if for at least one `xi`, evaluating
`conv “P xi”` returns the theorem `|- P xi = T`, then it returns the
theorem

``` hol4
   |- IS_EL P [x0;...xn] = T
```

### Failure

`IS_EL_CONV conv tm` fails if `tm` is not of the form described above,
or failure occurs when evaluating `conv “x = xi”` for some `xi`.

### Example

Evaluating

``` hol4
   IS_EL_CONV bool_EQ_CONV “IS_EL T [T;F;T]”;
```

returns the following theorem:

``` hol4
   |- IS_EL($= T)[F;F] = F
```

### See also

[`listLib.SOME_EL_CONV`](#listLib.SOME_EL_CONV),
[`listLib.ALL_EL_CONV`](#listLib.ALL_EL_CONV),
[`listLib.FOLDL_CONV`](#listLib.FOLDL_CONV),
[`listLib.FOLDR_CONV`](#listLib.FOLDR_CONV),
[`listLib.list_FOLD_CONV`](#listLib.list_FOLD_CONV)
