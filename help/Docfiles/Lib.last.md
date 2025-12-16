## `last`

``` hol4
Lib.last : 'a list -> 'a
```

------------------------------------------------------------------------

Computes the last element of a list.

`last [x1,...,xn]` returns `xn`.

### Failure

Fails if the list is empty.

### See also

[`Lib.butlast`](#Lib.butlast), [`Lib.el`](#Lib.el),
[`Lib.front_last`](#Lib.front_last)
