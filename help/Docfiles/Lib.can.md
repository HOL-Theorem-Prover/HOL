## `can`

``` hol4
Lib.can : ('a -> 'b) -> 'a -> bool
```

------------------------------------------------------------------------

Tests for failure.

`can f x` evaluates to `true` if the application of `f` to `x` succeeds.
It evaluates to `false` if the application fails.

### Failure

Only fails if `f x` raises the `Interrupt` exception.

### Example

``` hol4
- hd [];
! Uncaught exception:
! Empty

- can hd [];
> val it = false : bool

- can (fn _ => raise Interrupt) 3;
> Interrupted.
```

### See also

[`Lib.assert`](#Lib.assert), [`Lib.trye`](#Lib.trye),
[`Lib.partial`](#Lib.partial), [`Lib.total`](#Lib.total),
[`Lib.assert_exn`](#Lib.assert_exn)
