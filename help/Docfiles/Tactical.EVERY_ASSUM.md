## `EVERY_ASSUM`

``` hol4
Tactical.EVERY_ASSUM : (thm_tactic -> tactic)
```

------------------------------------------------------------------------

Sequentially applies all tactics given by mapping a function over the
assumptions of a goal.

When applied to a theorem-tactic `f` and a goal `({A1,...,An} ?- C)`,
the `EVERY_ASSUM` tactical maps `f` over a list of `ASSUME`d assumptions
then applies the resulting tactics, in sequence, to the goal:

``` hol4
   EVERY_ASSUM f ({A1,...,An} ?- C)
    = (f(A1 |- A1) THEN ... THEN f(An |- An)) ({A1,...,An} ?- C)
```

If the goal has no assumptions, then `EVERY_ASSUM` has no effect.

### Failure

The application of `EVERY_ASSUM` to a theorem-tactic and a goal fails if
the theorem-tactic fails when applied to any of the `ASSUME`d
assumptions of the goal, or if any of the resulting tactics fail when
applied sequentially.

### See also

[`Tactical.ASSUM_LIST`](#Tactical.ASSUM_LIST),
[`Tactical.MAP_EVERY`](#Tactical.MAP_EVERY),
[`Tactical.MAP_FIRST`](#Tactical.MAP_FIRST),
[`Tactical.THEN`](#Tactical.THEN)
