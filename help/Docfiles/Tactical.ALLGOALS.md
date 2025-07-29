## `ALLGOALS`

``` hol4
Tactical.ALLGOALS : tactic -> list_tactic
```

------------------------------------------------------------------------

Applies a tactic to every goal in a list

If `tac` is a tactic, `ALLGOALS tac` is a list-tactic which applies the
tactic `tac` to all the goals in the given list.

### Failure

The application of `ALLGOALS` to a tactic never fails. The resulting
list-tactic fails if `tac` fails when applied to any of the goals in the
given list.

### Example

Where `tac1` and `tac2` are tactics, `tac1 THEN_LT ALLGOALS tac2` is
equivalent to `tac1 THEN tac2`

### See also

[`Tactical.THEN_LT`](#Tactical.THEN_LT),
[`Tactical.THEN`](#Tactical.THEN)
