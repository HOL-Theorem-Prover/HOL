## `pair_of_list`

``` hol4
Lib.pair_of_list : 'a list -> 'a * 'a
```

------------------------------------------------------------------------

Turns a two-element list into a pair.

`pair_of_list [x, y]` returns `(x, y)`.

### Failure

Fails if applied to a list that is not of length 2.

### See also

[`Lib.singleton_of_list`](#Lib.singleton_of_list),
[`Lib.triple_of_list`](#Lib.triple_of_list),
[`Lib.quadruple_of_list`](#Lib.quadruple_of_list)
