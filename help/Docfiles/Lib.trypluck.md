## `trypluck`

``` hol4
Lib.trypluck : ('a -> 'b) -> 'a list -> 'b * 'a list
```

------------------------------------------------------------------------

Pull an element out of a list.

An invocation `trypluck f [x1,...,xk,...,xn]` returns a pair

``` hol4
   (f(xk),[x1,...,xk-1,xk+1,...xn])
```

where `xk` has been lifted out of the list without disturbing the
relative positions of the other elements. For this to happen, `f(xk)`
must hold, and `f(xi)` must fail for `x1,...,xk-1`.

### Failure

If the input list is empty. Also fails if `f` fails on every member of
the list.

### Example

``` hol4
- val (x,rst) = trypluck BETA_CONV [``1``,``(\x. x+2) 3``, ``p + q``];
> val x = |- (\x. x + 2) 3 = 3 + 2 : thm
  val rst = [``1``, ``p + q``] : term list
```

### See also

[`Lib.first`](#Lib.first), [`Lib.filter`](#Lib.filter),
[`Lib.mapfilter`](#Lib.mapfilter), [`Lib.tryfind`](#Lib.tryfind)
