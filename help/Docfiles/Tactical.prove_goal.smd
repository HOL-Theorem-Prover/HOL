## `prove_goal`

``` hol4
Tactical.prove_goal : goal * tactic -> thm
```

------------------------------------------------------------------------

Proves a goal with a tactic.

By default (using the function `TAC_PROOF` (*q.v.*)), a call to `prove_goal((asl,g), tac)` attempts to prove the specified goal `(asl,g)` by applying the tactic `tac` to it, generating a result `(sgs,vf)`. This result has `sgs` a list of subgoals and `vf` a validation function. If `sgs` is empty, then the value of `vf []` is returned.

If the provided tactic is valid, the resulting theorem will have hypotheses that are a subset of the assumptions `asl`, and will have a conclusion that is alpha-equivalent to `g`.

The default behaviour can be changed with the function `Tactical.set_prover`.

### Failure

Fails if the goal `(asl,g)` is not well-typed (all members of the list `asl` must be of type `:bool` as must be the conclusion `g`), or if the supplied tactic does not prove the goal.

### Comments

`Tactical.prove_goal` is to `TAC_PROOF` as `Tactical.prove` is to `Tactical.default_prover`.

### See also

[`Tactical.prove`](#Tactical.prove),
[`Tactical.set_prover`](#Tactical.set_prover),
[`Tactical.TAC_PROOF`](#Tactical.TAC_PROOF).
