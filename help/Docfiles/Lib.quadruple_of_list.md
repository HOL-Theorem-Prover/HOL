## `quadruple_of_list`

``` hol4
Lib.quadruple_of_list : 'a list -> 'a * 'a * 'a * 'a
```

------------------------------------------------------------------------

Turns a four-element list into a quadruple.

`quadruple_of_list [x1, x2, x3, x4]` returns `(x1, x2, x3, x4)`.

### Failure

Fails if applied to a list that is not of length 4.

### See also

[`Lib.singleton_of_list`](#Lib.singleton_of_list),
[`Lib.pair_of_list`](#Lib.pair_of_list),
[`Lib.triple_of_list`](#Lib.triple_of_list)
