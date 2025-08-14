## `LASTGOAL`

``` hol4
Tactical.LASTGOAL : tactic -> list_tactic
```

------------------------------------------------------------------------

The list-tactic which applies a tactic to the last member of a list of
goals.

If `tac` is a tactic, `LASTGOAL tac` is a list-tactic which applies the
tactic `tac` to the last member of a list of goals.

### Failure

The application of `LASTGOAL` to a tactic never fails. The resulting
list-tactic fails the goal list is empty or or finally if `tac` fails
when applied to the last member of the goal list.

Applying a tactic to the last subgoal.

### Example

Where `tac1` and `tac2` are tactics, `tac1 THEN_LT LASTGOAL tac2`
applies `tac1` to a goal, and then applies `tac2` to the last resulting
subgoal.

### See also

[`Tactical.THEN_LT`](#Tactical.THEN_LT),
[`Tactical.NTH_GOAL`](#Tactical.NTH_GOAL),
[`Tactical.HEADGOAL`](#Tactical.HEADGOAL)
