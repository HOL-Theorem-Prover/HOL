## `ALL_EL_CONV`

``` hol4
listLib.ALL_EL_CONV : conv -> conv
```

------------------------------------------------------------------------

Computes by inference the result of applying a predicate to elements of
a list.

`ALL_EL_CONV` takes a conversion `conv` and a term `tm` in the following
form:

``` hol4
   ALL_EL P [x0;...xn]
```

It returns the theorem

``` hol4
   |- ALL_EL P [x0;...xn] = T
```

if for every `xi` occurring in the list, `conv “P xi”` returns a theorem
`|- P xi = T`, otherwise, if for at least one `xi`, evaluating
`conv “P xi”` returns the theorem `|- P xi = F`, then it returns the
theorem

``` hol4
   |- ALL_EL P [x0;...xn] = F
```

### Failure

`ALL_EL_CONV conv tm` fails if `tm` is not of the form described above,
or failure occurs when evaluating `conv “P xi”` for some `xi`.

### Example

Evaluating

``` hol4
   ALL_EL_CONV bool_EQ_CONV “ALL_EL ($= T) [T;F;T]”;
```

returns the following theorem:

``` hol4
   |- ALL_EL($= T)[T;F;T] = F
```

In general, if the predicate `P` is an explicit lambda abstraction
`(\x. P x)`, the conversion should be in the form

``` hol4
   (BETA_CONV THENC conv')
```

### See also

[`listLib.SOME_EL_CONV`](#listLib.SOME_EL_CONV),
[`listLib.IS_EL_CONV`](#listLib.IS_EL_CONV),
[`listLib.FOLDL_CONV`](#listLib.FOLDL_CONV),
[`listLib.FOLDR_CONV`](#listLib.FOLDR_CONV),
[`listLib.list_FOLD_CONV`](#listLib.list_FOLD_CONV)
