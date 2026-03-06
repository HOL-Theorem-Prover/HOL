## `end_itlist`

``` hol4
Lib.end_itlist : ('a -> 'a -> 'a) -> 'a list -> 'a
```

------------------------------------------------------------------------

List iteration function. Applies a binary function between adjacent
elements of a list.

`end_itlist f [x1,...,xn]` returns `f x1 ( ... (f x(n-1) xn)...)`.
Returns `x` for a one-element list `[x]`.

### Failure

Fails if list is empty, or if an application of `f` raises an exception.

### Example

``` hol4
- end_itlist (curry op+) [1,2,3,4];
> val it = 10 : int
```

### See also

[`Lib.itlist`](#Lib.itlist), [`Lib.rev_itlist`](#Lib.rev_itlist),
[`Lib.itlist2`](#Lib.itlist2), [`Lib.rev_itlist2`](#Lib.rev_itlist2)
