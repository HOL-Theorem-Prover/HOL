## `REPEAT_LT`

``` hol4
Tactical.REPEAT_LT : (list_tactic -> list_tactic)
```

------------------------------------------------------------------------

Repeatedly applies a list-tactic until it fails.

The list-tactic `REPEAT_LT ltac` is a list-tactic which applies `ltac`
to a goal list, and while it succeeds, continues applying it to the
resulting subgoal list.

### Failure

The application of `REPEAT_LT` to a list-tactic never fails, and neither
does the composite list-tactic, even if the basic list-tactic fails
immediately.

### See also

[`Tactical.REPEAT`](#Tactical.REPEAT),
[`Tactical.THEN_LT`](#Tactical.THEN_LT)
