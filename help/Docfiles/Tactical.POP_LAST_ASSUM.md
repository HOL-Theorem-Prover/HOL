## `POP_LAST_ASSUM`

``` hol4
Tactical.POP_LAST_ASSUM : thm_tactic -> tactic
```

------------------------------------------------------------------------

Applies tactic generated from the last element of a goal's assumption
list.

When applied to a theorem-tactic and a goal, `POP_LAST_ASSUM` applies
the theorem-tactic to the `ASSUME`d last element of the assumption list,
and applies the resulting tactic to the goal without that assumption in
its assumption list:

``` hol4
   POP_LAST_ASSUM f ({A1,...,Am,An} ?- t) = f (An |- An) ({A1,...,Am} ?- t)
```

### Failure

Fails if the assumption list of the goal is empty, or the theorem-tactic
fails when applied to the popped assumption, or if the resulting tactic
fails when applied to the goal (with depleted assumption list).

### Comments

The tactical `POP_LAST_ASSUM` is also available under the lower-case
version of the name, `pop_last_assum`.

### See also

[`Tactical.ASSUM_LIST`](#Tactical.ASSUM_LIST),
[`Tactical.EVERY_ASSUM`](#Tactical.EVERY_ASSUM),
[`Tactic.IMP_RES_TAC`](#Tactic.IMP_RES_TAC),
[`Tactical.POP_ASSUM`](#Tactical.POP_ASSUM),
[`Rewrite.REWRITE_TAC`](#Rewrite.REWRITE_TAC)
