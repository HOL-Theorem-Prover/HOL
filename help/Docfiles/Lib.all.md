## `all`

``` hol4
Lib.all : ('a -> bool) -> 'a list -> bool
```

------------------------------------------------------------------------

Tests whether a predicate holds throughout a list.

`all P [x1,...,xn]` equals `P x1 andalso .... andalso P xn`. `all P []`
yields `true`.

### Failure

If `P x0,...,P x(j-1)` all evaluate to `true` and `P xj` raises an
exception `e`, then `all P [x0,...,x(j-1),xj,...,xn]` raises `e`.

### Example

``` hol4
- all (equal 3) [3,3,3];
> val it = true : bool

- all (equal 3) [];
> val it = true : bool

- all (fn _ => raise Fail "") [];
> val it = true : bool

- all (fn _ => raise Fail "") [1];
! Uncaught exception:
! Fail  ""
```

### See also

[`Lib.all2`](#Lib.all2), [`Lib.exists`](#Lib.exists),
[`Lib.first`](#Lib.first)
