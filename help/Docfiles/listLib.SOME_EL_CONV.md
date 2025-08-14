## `SOME_EL_CONV`

``` hol4
listLib.SOME_EL_CONV : conv -> conv
```

------------------------------------------------------------------------

Computes by inference the result of applying a predicate to the elements
of a list.

`SOME_EL_CONV` takes a conversion `conv` and a term `tm` of the
following form:

``` hol4
   SOME_EL P [x0;...xn]
```

It returns the theorem

``` hol4
   |- SOME_EL P [x0;...xn] = F
```

if for every `xi` occurred in the list, `conv “P xi”` returns a theorem
`|- P xi = F`, otherwise, if for at least one `xi`, evaluating
`conv “P xi”` returns the theorem `|- P xi = T`, then it returns the
theorem

``` hol4
   |- SOME_EL P [x0;...xn] = T
```

### Failure

`SOME_EL_CONV conv tm` fails if `tm` is not of the form described above,
or failure occurs when evaluating `conv “P xi”` for some `xi`.

### Example

Evaluating

``` hol4
   SOME_EL_CONV bool_EQ_CONV “SOME_EL ($= T) [T;F;T]”;
```

returns the following theorem:

``` hol4
   |- SOME_EL($= T)[T;F;T] = T
```

In general, if the predicate `P` is an explicit lambda abstraction
`(\x. P x)`, the conversion should be in the form

``` hol4
   (BETA_CONV THENC conv')
```

### See also

[`listLib.ALL_EL_CONV`](#listLib.ALL_EL_CONV),
[`listLib.IS_EL_CONV`](#listLib.IS_EL_CONV),
[`listLib.FOLDL_CONV`](#listLib.FOLDL_CONV),
[`listLib.FOLDR_CONV`](#listLib.FOLDR_CONV),
[`listLib.list_FOLD_CONV`](#listLib.list_FOLD_CONV)
