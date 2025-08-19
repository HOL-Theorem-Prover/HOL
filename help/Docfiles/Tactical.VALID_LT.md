## `VALID_LT`

``` hol4
Tactical.VALID_LT : list_tactic -> list_tactic
```

------------------------------------------------------------------------

Makes a list-tactic fail if it would otherwise return an invalid proof.

When list-tactic `ltac` is applied to a goal list `gl` it produces a new
goal list `gl'` and a justification. When the justification is applied
to a list `thl'` of theorems which are the new goals `gl'`, proved, it
should produce a list `thl` of theorems which are the goals `gl`,
proved.

Precisely, for each goal `(asl, g)` in `gl`, the corresponding theorem
in `thl` should be `A |- g`, with `A` a subset of `asl`. If this is not
the case, then the list-tactic is invalid, and `VALID_LT ltac gl` fails
(raises an exception). Otherwise, `VALID_LT ltac gl` behaves the same as
`ltac gl`.

### Failure

`VALID_LT ltac gl` fails by design if `ltac gl` produces new goals and
justification which do not prove the given goals `gl`. Also fails if its
`ltac gl` fails.

### See also

[`Tactical.VALID`](#Tactical.VALID),
[`Tactical.VALIDATE_LT`](#Tactical.VALIDATE_LT),
[`proofManagerLib.elt`](#proofManagerLib.elt),
[`proofManagerLib.expand_list`](#proofManagerLib.expand_list)
