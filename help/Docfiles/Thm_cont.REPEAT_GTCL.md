## `REPEAT_GTCL`

``` hol4
Thm_cont.REPEAT_GTCL : (thm_tactical -> thm_tactical)
```

------------------------------------------------------------------------

Applies a theorem-tactical until it fails when applied to a goal.

When applied to a theorem-tactical, a theorem-tactic, a theorem and a
goal:

``` hol4
   REPEAT_GTCL ttl ttac th goal
```

`REPEAT_GTCL` repeatedly modifies the theorem according to `ttl` till
the result of handing it to `ttac` and applying it to the goal fails
(this may be no times at all).

### Failure

Fails iff the theorem-tactic fails immediately when applied to the
theorem and the goal.

### Example

The following tactic matches `th`'s antecedents against the assumptions
of the goal until it can do so no longer, then puts the resolvents onto
the assumption list:

``` hol4
   REPEAT_GTCL (IMP_RES_THEN ASSUME_TAC) th
```

### See also

[`Thm_cont.REPEAT_TCL`](#Thm_cont.REPEAT_TCL),
[`Thm_cont.THEN_TCL`](#Thm_cont.THEN_TCL)
