## `TACS_TO_LT`

``` hol4
Tactical.TACS_TO_LT : tactic list -> list_tactic
```

------------------------------------------------------------------------

The list-tactic which applies a list of tactics to the corresponding
members of a list of goals.

If `T1,...,Tn` are tactics, `TACS_TO_LT [T1,...,Tn]` is a list-tactic
which applies the tactics `T1,...,Tn` to the corresponding goals.

### Failure

The application of `TACS_TO_LT` to a tactic list never fails. The
resulting list-tactic fails if length of the goal list is not the same
as that of the tactic list, or finally if `Ti` fails when applied to the
`i`'th member of the goal list.

Applying different tactics to different subgoals.

### Example

Where `tac1` is a tactic and `tacs2` is a list of tactics,
`tac1 THEN_LT TACS_TO_LT tacs2` is equivalent to `tac1 THENL tacs2`

### See also

[`Tactical.THEN_LT`](#Tactical.THEN_LT),
[`Tactical.THENL`](#Tactical.THENL)
