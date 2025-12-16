## `all2`

``` hol4
Lib.all2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
```

------------------------------------------------------------------------

Tests whether a predicate holds pairwise throughout two lists.

An invocation

``` hol4
   all2 P [x1,...,xn] [y1,...,yn]
```

equals

``` hol4
   P x1 y1 andalso .... andalso P xn yn
```

Also, `all2 P [] []` yields `true`.

### Failure

If `P x0,...,P x(j-1)` all evaluate to `true` and `P xj` raises an
exception `e`, then

``` hol4
   all2 P [x0,...,x(j-1),xj,...,xn]
```

raises `e`. An invocation `all2 P l1 l2` will also raise an exception if
the length of `l1` is not equal to the length of `l2`.

### Example

``` hol4
- all2 equal [1,2,3] [1,2,3];
> val it = true : bool

- all2 equal [1,2,3] [1,2,3,4] handle e => Raise e;

Exception raised at Lib.all2:
different length lists
! Uncaught exception:
! HOL_ERR

- all2 (fn _ => fn _ => raise Fail "") [] [];
> val it = true : bool

- all2 (fn _ => fn _ => raise Fail "") [1] [1];
! Uncaught exception:
! Fail  ""
```

### See also

[`Lib.all`](#Lib.all)
