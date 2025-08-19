## `TRYALL`

``` hol4
Tactical.TRYALL : tactic -> list_tactic
```

------------------------------------------------------------------------

Tries to apply a tactic to every goal in a list

If `tac` is a tactic, `TRYALL tac` is a list-tactic which, when applied
to a list of goals, applies the tactic `tac` to each goal for which it
succeeds. When `tac` fails on a goal, `TRYALL tac` has no effect on that
goal.

### Failure

The application of `TRYALL` to a tactic never fails. The resulting
list-tactic never fails.

### Example

Where `tac1` and `tac2` are tactics, `tac1 THEN_LT TRYALL tac2` is
equivalent to `tac1 THEN TRY tac2`

### See also

[`Tactical.TRY`](#Tactical.TRY),
[`Tactical.THEN_LT`](#Tactical.THEN_LT),
[`Tactical.THEN`](#Tactical.THEN), [`Tactical.TRY`](#Tactical.TRY),
[`Tactical.ALLGOALS`](#Tactical.ALLGOALS)
