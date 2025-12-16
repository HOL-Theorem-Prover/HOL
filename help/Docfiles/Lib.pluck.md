## `pluck`

``` hol4
Lib.pluck : ('a -> bool) -> 'a list -> 'a * 'a list
```

------------------------------------------------------------------------

Pull an element out of a list.

An invocation `pluck P [x1,...,xk,...,xn]` returns a pair
`(xk,[x1,...,xk-1,xk+1,...xn])`, where `xk` has been lifted out of the
list without disturbing the relative positions of the other elements.
For this to happen, `P xk` must hold, and `P xi` must not have held for
`x1,...,xk-1`.

### Failure

If the input list is empty. Also fails if `P` holds of no member of the
list. Also fails if an application of `P` fails.

### Example

``` hol4
- val (x,rst) = pluck (fn x => x mod 2 = 0) [1,2,3];
> val x = 2 : int
  val rst = [1, 3] : int list
```

### See also

[`Lib.first`](#Lib.first), [`Lib.filter`](#Lib.filter),
[`Lib.mapfilter`](#Lib.mapfilter), [`Lib.assoc1`](#Lib.assoc1),
[`Lib.assoc2`](#Lib.assoc2), [`Lib.assoc`](#Lib.assoc),
[`Lib.rev_assoc`](#Lib.rev_assoc)
