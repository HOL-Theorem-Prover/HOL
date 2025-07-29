## `assert`

``` hol4
Lib.assert : ('a -> bool) -> 'a -> 'a
```

------------------------------------------------------------------------

Checks that a value satisfies a predicate.

`assert p x` returns `x` if the application `p x` yields `true`.
Otherwise, `assert p x` fails.

### Failure

`assert p x` fails with exception `HOL_ERR` if the predicate `p` yields
`false` when applied to the value `x`. If the application `p x` raises
an exception `e`, then `assert p x` raises `e`.

### Example

``` hol4
- null [];
> val it = true : bool

- assert null ([]:int list);
> val it = [] : int list

- null [1];
> false : bool

- assert null [1];
! Uncaught exception:
! HOL_ERR <poly>
```

### See also

[`Lib.can`](#Lib.can), [`Lib.assert_exn`](#Lib.assert_exn)
