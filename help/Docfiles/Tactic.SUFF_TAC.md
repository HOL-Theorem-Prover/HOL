## `SUFF_TAC`

``` hol4
Tactic.SUFF_TAC : term -> tactic
```

------------------------------------------------------------------------

Introduces an implicational subgoal.

A call to `SUFF_TAC t` on the goal `asl ?- g` introduces two subgoals:
`asl ?- t ==> g` and `asl ?- t`. At a high-level, the user's claim is
that term `t` suffices (hence the name) to prove the goal. The first new
goal to be discharged is the check for this; the second is to actually
show `t`.

### Failure

Will fail if `t` is not of type `:bool`.

### See also

[`Tactic.SUBGOAL_THEN`](#Tactic.SUBGOAL_THEN),
[`bossLib.suffices_by`](#bossLib.suffices_by)
