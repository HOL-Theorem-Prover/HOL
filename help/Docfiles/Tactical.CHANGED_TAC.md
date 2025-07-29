## `CHANGED_TAC`

``` hol4
Tactical.CHANGED_TAC : (tactic -> tactic)
```

------------------------------------------------------------------------

Makes a tactic fail if it has no effect.

When applied to a tactic `T`, the tactical `CHANGED_TAC` gives a new
tactic which is the same as `T` if that has any effect, and otherwise
fails.

### Failure

The application of `CHANGED_TAC` to a tactic never fails. The resulting
tactic fails if the basic tactic either fails or has no effect.

### See also

[`Tactical.TRY`](#Tactical.TRY), [`Tactical.VALID`](#Tactical.VALID)
