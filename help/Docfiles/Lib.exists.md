## `exists`

``` hol4
Lib.exists : ('a -> bool) -> 'a list -> bool
```

------------------------------------------------------------------------

Check if a predicate holds somewhere in a list.

An invocation `exists P l` returns true if `P` holds of some element of
`l`. Since there are no elements of `[]`, `exists P []` always returns
`false`.

### Failure

When searching for an element of `l` that `P` holds of, it may happen
that an application of `P` to an element of `l` raises an exception. In
that case, `exists P l` raises an exception.

### Example

``` hol4
- exists (fn i => i mod 2 = 0) [1,3,4];
> val it = true : bool

- exists (fn _ => raise Fail "") [];
> val it = false : bool

- exists (fn _ => raise Fail "") [1];
! Uncaught exception:
! Fail  ""
```

### See also

[`Lib.all`](#Lib.all), [`Lib.first`](#Lib.first),
[`Lib.tryfind`](#Lib.tryfind)
