## `NTH_GOAL`

``` hol4
Tactical.NTH_GOAL : tactic -> int -> list_tactic
```

------------------------------------------------------------------------

The list-tactic which applies a tactic to the `n`'th member of a list of
goals.

If `tac` is a tactic, `NTH_GOAL n tac` is a list-tactic which applies
the tactic `tac` to the `n`'th member of a list of goals.

Note that in the interactive system, subgoals are printed in reverse
order of their numbering.

### Failure

The application of `NTH_GOAL` to a tactic and integer never fails. The
resulting list-tactic fails if `n` is less than 1 or greater than the
length of the goal list, or finally if `tac` fails when applied to the
`n`'th member of the goal list.

Applying a tactic to a particular subgoal.

### Example

Where `tac1` and `tac2` are tactics, `tac1 THEN_LT NTH_GOAL n tac2`
applies `tac1` to a goal, and then applies `tac2` to the `n`'th
resulting subgoal.

### See also

[`Tactical.THEN_LT`](#Tactical.THEN_LT),
[`Tactical.THEN1`](#Tactical.THEN1),
[`Tactical.HEADGOAL`](#Tactical.HEADGOAL),
[`Tactical.LASTGOAL`](#Tactical.LASTGOAL)
