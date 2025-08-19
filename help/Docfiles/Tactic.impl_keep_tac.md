## `impl_keep_tac`

``` hol4
Tactic.impl_keep_tac : tactic
```

------------------------------------------------------------------------

Implements a version of implication-left sequent calculus rule as tactic

Given a goal of the form `A ?- ((p ==> q) ==> r)`, an application of
`impl_tac` will produce two sub-goals: `A ?- p` and `A, p ?- (q ==> r)`.
This can be useful if `p` should be dealt with in isolation, when, say,
the tactics that solve `p` can't safely be applied to `q` and/or `r`.

This tactic differs from `impl_tac` in that it keeps `p` as an
assumption in the second sub-goal.

### Failure

Fails if the goal is not an implication with another implication as its
antecdent. Note that for the purpose of this tactic, a negation `~p` is
viewed as the implication `p ==> F`. This means that `impl_tac` will
succeed when applied to goals whose conclusions are `~p ==> q`,
`~(p ==> q)` and `~~p`.

### See also

[`Tactic.impl_tac`](#Tactic.impl_tac),
[`Thm_cont.PROVEHYP_THEN`](#Thm_cont.PROVEHYP_THEN)
