## `butlast`

``` hol4
Lib.butlast : 'a list -> 'a list
```

------------------------------------------------------------------------

Computes the sub-list of a list consisting of all but the last element.

`butlast [x1,...,xn]` returns `[x1,...,x(n-1)]`.

### Failure

Fails if the list is empty.

### See also

[`Lib.last`](#Lib.last), [`Lib.el`](#Lib.el),
[`Lib.front_last`](#Lib.front_last)
