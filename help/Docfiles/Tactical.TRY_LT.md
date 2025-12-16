## `TRY_LT`

``` hol4
Tactical.TRY_LT : (list_tactic -> list_tactic)
```

------------------------------------------------------------------------

Makes a list-tactic have no effect rather than fail.

For any list-tactic `ltac`, the application `TRY_LT ltac` gives a new
list-tactic which has the same effect as `ltac` if that succeeds, and
otherwise has no effect.

### Failure

The application of `TRY_LT` to a list-tactic never fails. The resulting
list-tactic never fails.

### See also

[`Tactical.TRY`](#Tactical.TRY)
