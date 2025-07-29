## `REFL_TAC`

``` hol4
Tactic.REFL_TAC : tactic
```

------------------------------------------------------------------------

Solves a goal which is an equation between alpha-equivalent terms.

When applied to a goal `A ?- t = t'`, where `t` and `t'` are
alpha-equivalent, `REFL_TAC` completely solves it.

``` hol4
    A ?- t = t'
   =============  REFL_TAC
```

### Failure

Fails unless the goal is an equation between alpha-equivalent terms.

### See also

[`Tactic.ACCEPT_TAC`](#Tactic.ACCEPT_TAC),
[`Tactic.MATCH_ACCEPT_TAC`](#Tactic.MATCH_ACCEPT_TAC),
[`Rewrite.REWRITE_TAC`](#Rewrite.REWRITE_TAC)
