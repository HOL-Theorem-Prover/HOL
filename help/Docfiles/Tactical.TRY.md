## `TRY`

``` hol4
Tactical.TRY : (tactic -> tactic)
```

------------------------------------------------------------------------

Makes a tactic have no effect rather than fail.

For any tactic `T`, the application `TRY T` gives a new tactic which has
the same effect as `T` if that succeeds, and otherwise has no effect.

### Failure

The application of `TRY` to a tactic never fails. The resulting tactic
never fails.

### See also

[`Tactical.CHANGED_TAC`](#Tactical.CHANGED_TAC),
[`Tactical.VALID`](#Tactical.VALID)
