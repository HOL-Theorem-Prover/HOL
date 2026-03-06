## `assert_exn`

``` hol4
Lib.assert_exn : ('a -> bool) -> 'a -> exn -> 'a
```

------------------------------------------------------------------------

Checks that a value satisfies a predicate.

`assert_exn p x e` returns `x` if the application `p x` evaluates to
`true`. Otherwise, `assert_exn p x e` raises `e`

### Failure

`assert_exn p x e` fails with exception `e` if the predicate `p` yields
`false` when applied to the value `x`. If the application `p x` raises
an exception `ex`, then `assert_exn p x e` raises `ex`.

### Example

``` hol4
- null [];
> val it = true : bool

- assert_exn null ([]:int list) (Fail "non-empty list");
> val it = [] : int list

- null [1];
> false : bool

- assert_exn null [1] (Fail "non-empty list");;
! Uncaught exception:
! Fail  "non-empty list"
```

### See also

[`Lib.can`](#Lib.can), [`Lib.assert`](#Lib.assert)
