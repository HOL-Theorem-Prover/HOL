## `ALL_LT`

``` hol4
Tactical.ALL_LT : list_tactic
```

------------------------------------------------------------------------

Passes on a goal list unchanged.

`ALL_LT` applied to a goal list `gl` simply produces the goal list `gl`.
It is the identity for the `THEN_LT` tactical.

### Failure

Never fails.

### Example

To apply tactic `tac1` to a goal, and then to apply `tac2` to all
resulting subgoals except the first, use

``` hol4
  tac1 THEN_LT SPLIT_LT 1 (ALL_LT, ALLGOALS tac2)
```

### See also

[`Tactical.THEN_LT`](#Tactical.THEN_LT),
[`Tactical.SPLIT_LT`](#Tactical.SPLIT_LT),
[`Tactical.ALLGOALS`](#Tactical.ALLGOALS)
