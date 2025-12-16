## `prim_irule`

``` hol4
Tactic.prim_irule : thm_tactic
```

------------------------------------------------------------------------

For a goal which is an instance of the conclusion of the supplied
theorem, replace the goal by the instantiated hypotheses of the supplied
theorem.

When given a theorem `th = A' |- t` and a goal `A ?- t'` where `t` can
be matched to `t'` by instantiating free variables, including
appropriate type instantiation, `prim_irule` replaces the goal by new
subgoals which are the hypotheses `A'`, instantiated

The order of the new subgoals corresponds to the order in which `hyp th`
returns the hypotheses `A'`

### Failure

Fails unless the theorem has a conclusion which is instantiable to match
that of the goal.

### Comments

`irule` also pre-processes the supplied theorem, which will normally be
useful

`prim_irule` differs from `MATCH_ACCEPT_TAC` in that hypotheses of the
supplied theorem may also be substituted, and will appear as new
subgoals

### See also

[`Tactic.irule`](#Tactic.irule),
[`Tactic.MATCH_ACCEPT_TAC`](#Tactic.MATCH_ACCEPT_TAC),
[`Tactic.ACCEPT_TAC`](#Tactic.ACCEPT_TAC)
