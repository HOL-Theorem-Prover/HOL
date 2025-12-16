## `first`

``` hol4
Lib.first : ('a -> bool) -> 'a list -> 'a
```

------------------------------------------------------------------------

Return first element in list that predicate holds of.

An invocation `first P [x1,...,xk,...xn]` returns `xk` if `P xk` returns
`true` and `P xi (1 <= i < k)` equals `false`.

### Failure

If `P xi` is `false` for every element in `list`, then `first P list`
raises an exception. When searching for an element of `list` that `P`
holds of, it may happen that an application of `P` to an element of
`list` raises an exception `e`. In that case, `first P list` also raises
`e`.

### Example

``` hol4
- first (fn i => i mod 2 = 0) [1,3,4,5];
> val it = 4 : int

- first (fn i => i mod 2 = 0) [1,3,5,7];
! Uncaught exception:
! HOL_ERR

- first (fn _ => raise Fail "") [1];
! Uncaught exception:
! Fail  ""
```

### See also

[`Lib.exists`](#Lib.exists), [`Lib.tryfind`](#Lib.tryfind),
[`Lib.all`](#Lib.all)
