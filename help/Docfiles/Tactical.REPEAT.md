## `REPEAT`

``` hol4
Tactical.REPEAT : (tactic -> tactic)
```

------------------------------------------------------------------------

Repeatedly applies a tactic until it fails.

The tactic `REPEAT T` is a tactic which applies `T` to a goal, and while
it succeeds, continues applying it to all subgoals generated.

### Failure

The application of `REPEAT` to a tactic never fails, and neither does
the composite tactic, even if the basic tactic fails immediately.

### See also

[`Tactical.EVERY`](#Tactical.EVERY),
[`Tactical.FIRST`](#Tactical.FIRST),
[`Tactical.ORELSE`](#Tactical.ORELSE),
[`Tactical.THEN`](#Tactical.THEN), [`Tactical.THENL`](#Tactical.THENL)
