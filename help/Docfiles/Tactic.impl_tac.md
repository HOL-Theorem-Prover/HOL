## `impl_tac`

``` hol4
Tactic.impl_tac : tactic
```

------------------------------------------------------------------------

Implements analogue of implication-left sequent calculus rule as tactic

Given a goal of the form `A ?- ((p ==> q) ==> r)`, an application of
`impl_tac` will produce two sub-goals: `A ?- p` and `A ?- (q ==> r)`.
This can be useful if `p` should be dealt with in isolation, when, say,
the tactics that solve `p` can't safely be applied to `q` and/or `r`.

### Failure

Fails if the goal is not an implication with another implication as its
antecdent. Note that for the purpose of this tactic, a negation `~p` is
viewed as the implication `p ==> F`. This means that `impl_tac` will
succeed when applied to goals whose conclusions are `~p ==> q`,
`~(p ==> q)` and `~~p`.

### See also

[`Tactic.impl_keep_tac`](#Tactic.impl_keep_tac),
[`Thm_cont.PROVEHYP_THEN`](#Thm_cont.PROVEHYP_THEN)
