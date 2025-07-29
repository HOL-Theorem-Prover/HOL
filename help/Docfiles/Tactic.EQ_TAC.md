## `EQ_TAC`

``` hol4
Tactic.EQ_TAC : tactic
```

------------------------------------------------------------------------

Reduces goal of equality of boolean terms to forward and backward
implication.

When applied to a goal `A ?- t1 = t2`, where `t1` and `t2` have type
`bool`, the tactic `EQ_TAC` returns the subgoals `A ?- t1 ==> t2` and
`A ?- t2 ==> t1`.

``` hol4
             A ?- t1 = t2
   =================================  EQ_TAC
    A ?- t1 ==> t2   A ?- t2 ==> t1
```

### Failure

Fails unless the conclusion of the goal is an equation between boolean
terms.

### Comments

Also available under the names `eq_tac` and `iff_tac`.

### See also

[`Thm.EQ_IMP_RULE`](#Thm.EQ_IMP_RULE),
[`Drule.IMP_ANTISYM_RULE`](#Drule.IMP_ANTISYM_RULE)
