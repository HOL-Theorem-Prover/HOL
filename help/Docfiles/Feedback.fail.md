## `fail`

``` hol4
Feedback.fail : unit -> 'a
```

------------------------------------------------------------------------

Raise a `HOL_ERR`.

The function `fail` raises a `HOL_ERR` with default values. This is
useful when detailed error tracking is not necessary.

### Failure

Always fails.

### Example

``` hol4
- fail() handle e => Raise e;

Exception raised at ??.??:
fail
! Uncaught exception:
! HOL_ERR
```

### See also

[`Feedback`](#Feedback), [`Feedback.failwith`](#Feedback.failwith),
[`Feedback.Raise`](#Feedback.Raise),
[`Feedback.HOL_ERR`](#Feedback.HOL_ERR)
