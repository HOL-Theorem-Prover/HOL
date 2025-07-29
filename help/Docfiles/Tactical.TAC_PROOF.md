## `TAC_PROOF`

``` hol4
Tactical.TAC_PROOF : goal * tactic -> thm
```

------------------------------------------------------------------------

Attempts to prove a goal using a given tactic.

When applied to a goal-tactic pair `(A ?- t,tac)`, the `TAC_PROOF`
function attempts to prove the goal `A ?- t`, using the tactic `tac`. If
it succeeds, it returns the theorem `A' |- t` corresponding to the goal,
where the assumption list `A'` may be a proper superset of `A` unless
the tactic is valid; there is no inbuilt validity checking.

### Failure

Fails unless the goal has hypotheses and conclusions all of type `bool`,
and the tactic can solve the goal.

### See also

[`BasicProvers.PROVE`](#BasicProvers.PROVE),
[`Tactical.VALID`](#Tactical.VALID)
