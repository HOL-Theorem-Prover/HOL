## `GEN_VALIDATE_LT` {#Tactical.GEN_VALIDATE_LT}


```
GEN_VALIDATE_LT : bool -> list_tactic -> list_tactic
```



Where a list-tactic requires assumptions to be in the goal,
add those assumptions as new subgoals.


See `VALIDATE_LT`, which is implemented as `GEN_VALIDATE_LT true`.

When list-tactic `ltac` is applied to a goal list `gl`
it produces a new goal list `gl'` and a justification.
When the justification is applied to a list `thl'` of theorems
which are the new goals `gl'`, proved, it produces a list `thl`
of theorems (which, for a valid list-tactic are the goals `gl`, proved).

But `GEN_VALIDATE_LT false ltac` also returns extra subgoals corresponding to
the assumptions of `thl`.

See `GEN_VALIDATE` for more details.

### Failure

Fails by design if `ltac`, when applied to a goal list,
produces a proof which is invalid on account of proving
a theorem whose conclusion differs from that of the corresponding goal.

Also fails if `ltac` fails when applied to the given goals.


Compared with `VALIDATE_LT ltac`, `GEN_VALIDATE_LT false ltac` can
produces extra, unnecessary, subgoals.
But since the subgoals produced are predictable, regardless of the assumptions
of the goal, which may be useful when coding compound tactics.

### See also

[`Tactical.VALID`](#Tactical.VALID), [`Tactical.VALID_LT`](#Tactical.VALID_LT), [`Tactical.VALIDATE`](#Tactical.VALIDATE), [`Tactical.VALIDATE_LT`](#Tactical.VALIDATE_LT), [`Tactical.GEN_VALIDATE`](#Tactical.GEN_VALIDATE)

