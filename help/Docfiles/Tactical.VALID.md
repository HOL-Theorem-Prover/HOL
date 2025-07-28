## `VALID` {#Tactical.VALID}


```
VALID : tactic -> tactic
```



Makes a tactic fail if it would otherwise return an invalid proof.


If `tac` applied to the goal `(asl,g)` produces a justification that
does not create a theorem `A |- g`, with `A` a subset of `asl`, then
`VALID tac (asl,g)` fails (raises an exception).  If `tac` produces a
valid proof on the goal, then the behaviour of `VALID tac (asl,g)` is
the same as `tac (asl,g)`

### Failure

Fails by design if `tac` produces an invalid proof when applied
to a goal.  Also fails if `tac` fails when applied to the given goal.

### See also

[`proofManagerLib.expand`](#proofManagerLib.expand), [`Tactical.VALIDATE`](#Tactical.VALIDATE)

