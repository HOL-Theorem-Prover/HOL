## `total`

``` hol4
Lib.total : ('a -> 'b) -> 'a -> 'b option
```

------------------------------------------------------------------------

Converts a partial function to a total function.

In ML, there are two main ways for a function to signal that it has been
called on an element outside of its intended domain of application:
exceptions and options. The function `total` maps a function that may
raise an exception to one that returns an element in the option type.
Thus, if `f x` results in any exception other than `Interrupt` being
raised, then `total f x` returns `NONE`. If `f x` raises `Interrupt`,
then `total f x` likewise raises `Interrupt`. If `f x` returns `y`, then
`total f x` returns `SOME y`.

The function `total` has an inverse `partial`. Generally speaking,
`(partial err o total) f` equals `f`, provided that `err` is the only
exception that `f` raises. Similarly, `(total o partial err) f` is equal
to `f`.

### Failure

When application of the first argument to the second argument raises
`Interrupt`.

### Example

``` hol4
- 3 div 0;
! Uncaught exception:
! Div

- total (op div) (3,0);
> val it = NONE : int option

- (partial Div o total) (op div) (3,0);
! Uncaught exception:
! Div
```

### See also

[`Lib.partial`](#Lib.partial)
