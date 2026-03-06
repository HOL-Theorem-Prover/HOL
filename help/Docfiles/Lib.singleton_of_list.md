## `singleton_of_list`

``` hol4
Lib.singleton_of_list : 'a list -> 'a
```

------------------------------------------------------------------------

Turns a single-element list into a singleton.

`singleton_of_list [x]` returns `x`.

### Failure

Fails if applied to a list that is not of length 1.

### See also

[`Lib.pair_of_list`](#Lib.pair_of_list),
[`Lib.triple_of_list`](#Lib.triple_of_list),
[`Lib.quadruple_of_list`](#Lib.quadruple_of_list)
