## `quadruple`

``` hol4
Lib.quadruple : 'a -> 'b -> 'c -> 'd -> 'a * 'b * 'c * 'd
```

------------------------------------------------------------------------

Makes four values into a quadruple.

`quadruple x1 x2 x3 x4` returns `(x1, x2, x3, x4)`.

### Failure

Never fails.

### See also

[`Lib.quadruple_of_list`](#Lib.quadruple_of_list),
[`Lib.pair`](#Lib.pair), [`Lib.triple`](#Lib.triple)
