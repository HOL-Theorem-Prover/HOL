## `by` {#bossLib.by}


```
op by : term quotation * tactic -> tactic
```



Prove and place a theorem on the assumptions of the goal.


An invocation `tm by tac`, when applied to goal `A ?- g`, applies
`tac` to goal `A ?- tm`. If `tm` is thereby proved, it is added to
`A`, yielding the new goal `A,tm ?- g`. If `tm` is not proved by
`tac`, then the application fails.

When `tm` is added to the existing assumptions `A`, it is
“stripped”, i.e., broken apart by eliminating existentials,
conjunctions, and disjunctions. This can lead to case splitting.

### Failure

Fails if `tac` fails when applied to `A ?- tm`, or if `tac` fails to prove that goal.

### Example

Given the goal `{x <= y, w < x} ?- P`, suppose that the fact
`?n. y = n + w` would help in eventually proving `P`. Invoking
    
       `?n. y = n + w` by (EXISTS_TAC ``y-w`` THEN DECIDE_TAC)
    
yields the goal `{y = n + w, x <= y, w < x} ?- P` in which the proved
fact has been added to the assumptions after its existential
quantifier is eliminated. Note the parentheses around the tactic: this
is needed for the example because `by` binds more tightly than `THEN`.

### Comments

Use of `by` can be more convenient than `IMP_RES_TAC` and `RES_TAC`
when they would generate many useless assumptions.

### See also

[`bossLib.subgoal`](#bossLib.subgoal), [`bossLib.suffices_by`](#bossLib.suffices_by), [`Tactical.SUBGOAL_THEN`](#Tactical.SUBGOAL_THEN), [`Tactic.IMP_RES_TAC`](#Tactic.IMP_RES_TAC), [`Tactic.RES_TAC`](#Tactic.RES_TAC), [`Tactic.STRIP_ASSUME_TAC`](#Tactic.STRIP_ASSUME_TAC)

