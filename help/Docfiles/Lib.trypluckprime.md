## `trypluck'`

``` hol4
Lib.trypluck' : ('a -> 'b option) -> 'a list -> ('b option * 'a list)
```

------------------------------------------------------------------------

Pull an element out of a list.

An invocation `trypluck' f [x1,...,xk,...,xn]` returns either the pair

``` hol4
   (f(xk),[x1,...,xk-1,xk+1,...xn])
```

where `xk` has been lifted out of the list without disturbing the
relative positions of the other elements, where `f(xk)` is `SOME(v)`,
and where `f(xi)` returns `NONE` for `x1,...,xk-1`; or it returns
`(NONE,[x1,...xn]` when `f` applied to every element of the list returns
`NONE`.

This is an 'option' version of the other library function `trypluck`.

### Failure

Never fails.

### See also

[`Lib.first`](#Lib.first), [`Lib.filter`](#Lib.filter),
[`Lib.mapfilter`](#Lib.mapfilter), [`Lib.tryfind`](#Lib.tryfind),
[`Lib.trypluck`](#Lib.trypluck)
