## `suspend`

``` hol4
bossLib.suspend : string -> tactic
```

------------------------------------------------------------------------

Suspends a goal (proving it), so that it can be resumed later.

Given any goal `g`, a call to `suspend nm` proves that goal by assuming an encoding of the goal as a hypothesis.
This encoding includes the name `nm`, so that the resulting theorem is effectively
```
  [e(nm,g)] |- g
```
Of course, if the goal is a subgoal in a larger proof, this new hypothesis will propagate out to the final theorem proved, recording the point at which the wider goal was suspended.
If `suspend` is called multiple times within the wider goal, multiple such hypotheses will be created.

### Failure

Never fails.

### Comment

The `VALID` tactical considers `suspend`-encoded assumptions legitimate, not flagging them as invalid and causing a tactic that uses them to fail.

### See also

[`bossLib.cheat`](#bossLib.cheat),
[`Tactical.VALID`](#Tactical.VALID).
