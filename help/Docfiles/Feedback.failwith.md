## `failwith`

``` hol4
Feedback.failwith : string -> 'a
```

------------------------------------------------------------------------

Raise a `HOL_ERR`.

The function `failwith` raises a `HOL_ERR` with default values. This is
useful when detailed error tracking is not necessary.

`failwith` differs from `fail` in that it takes an extra string
argument, which is typically used to tell which function `failwith` is
being called from.

### Failure

Always fails.

### Example

``` hol4
- failwith "foo" handle e => Raise e;

Exception raised at ??.failwith:
foo
! Uncaught exception:
! HOL_ERR
```

### See also

[`Feedback`](#Feedback), [`Feedback.fail`](#Feedback.fail),
[`Feedback.Raise`](#Feedback.Raise),
[`Feedback.HOL_ERR`](#Feedback.HOL_ERR)
