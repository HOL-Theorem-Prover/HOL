## `REVERSE_LT`

``` hol4
Tactical.REVERSE_LT : list_tactic
```

------------------------------------------------------------------------

Reverses the order of a list of subgoals.

The list-tactic `REVERSE_LT` reverses the order of a list of subgoals.

### Failure

Never fails.

### Example

Where `tac` is a tactic, `tac THEN_LT REVERSE_LT` is equivalent to
`REVERSE tac`

### See also

[`Tactical.THEN_LT`](#Tactical.THEN_LT),
[`Tactical.REVERSE`](#Tactical.REVERSE),
[`Tactical.ROTATE_LT`](#Tactical.ROTATE_LT)
