## `WEAKEN_TAC`

``` hol4
Tactic.WEAKEN_TAC : (term -> bool) -> tactic
```

------------------------------------------------------------------------

Deletes assumption from goal.

Given an ML predicate `P` mapping terms to `true` or `false` and a goal
`(asl,g)`, an invocation `WEAKEN_TAC P (asl,g)` removes the first
element (call it `tm`) that `P` holds of from `asl`, returning the goal
`(asl - tm,g)`.

### Failure

Fails if the assumption list of the goal is empty, or if `P` holds of no
element in `asl`.

### Example

Suppose we want to dispose of the equality assumption in the following
goal:

``` hol4
    C x
    ------------------------------------
      0.  A = B
      1.  B x
```

The following application of `WEAKEN_TAC` does the job.

``` hol4
  - e (WEAKEN_TAC is_eq);
  OK..
  1 subgoal:
  > val it =
      C x
      ------------------------------------
        B x
```

Occasionally useful for getting rid of superfluous assumptions.

### See also

[`Tactical.PAT_ASSUM`](#Tactical.PAT_ASSUM),
[`Tactical.POP_ASSUM`](#Tactical.POP_ASSUM)
