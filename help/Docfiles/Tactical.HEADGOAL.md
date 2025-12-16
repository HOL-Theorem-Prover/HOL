## `HEADGOAL`

``` hol4
Tactical.HEADGOAL : tactic -> list_tactic
```

------------------------------------------------------------------------

The list-tactic which applies a tactic to the first member of a list of
goals.

If `tac` is a tactic, `HEADGOAL tac` is a list-tactic which applies the
tactic `tac` to the first member of a list of goals.

### Failure

The application of `HEADGOAL` to a tactic never fails. The resulting
list-tactic fails the goal list is empty or or finally if `tac` fails
when applied to the first member of the goal list.

Applying a tactic to the first subgoal.

### Example

Where `tac1` and `tac2` are tactics, `tac1 THEN_LT HEADGOAL tac2`
applies `tac1` to a goal, and then applies `tac2` to the first resulting
subgoal.

### See also

[`Tactical.THEN_LT`](#Tactical.THEN_LT),
[`Tactical.NTH_GOAL`](#Tactical.NTH_GOAL),
[`Tactical.THEN1`](#Tactical.THEN1),
[`Tactical.LASTGOAL`](#Tactical.LASTGOAL)
