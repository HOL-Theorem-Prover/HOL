## `PROVEHYP_THEN`

``` hol4
Thm_cont.PROVEHYP_THEN : (thm -> thm -> tactic) -> thm -> tactic
```

------------------------------------------------------------------------

Makes antecedent of theorem as subgoal, continues with both parts as
theorems.

An application of the tactic `PROVEHYP_THEN th2tac th` to a goal `g`
requires that `th` be an (universally quantified) implication (or a
negation, in which case `~p` is treated as `p ==> F`). Given an
implication `|- !x1..xn. l ==> r x1..xn`, the result is a new sub-goal
requiring the user to prove `l`, and the application of `th2tac` to the
theorems with conclusion `l` and `!x1..xn. r x1..xn`.

Diagrammatically, one might see this as

``` hol4
          A ?- g
   ==============================================  PROVEHYP_THEN th2tac th
   A ?- l  ...  th2tac (A |- l) (A |- r) (A ?- g)
```

### Failure

Fails if the theorem argument is not an implication or negation.

### Example

``` hol4
   > FIRST_X_ASSUM (PROVEHYP_THEN (K MP_TAC)) ([“p”, “p ==> q”], “r”)
   val it = ([([“p”], “p”), ([“p”], “q ==> r”)], fn):
            goal list * validation
```

The use of `FIRST_X_ASSUM` pulls out the first implicational theorem,
and gives the user the requirement to prove `p` as a subgoal. In the
other subgoal, `q` has become a new antecedent in the goal (thanks to
the action of `MP_TAC`).

### Comments

This function is also available under the name `provehyp_then`.

### See also

[`Tactic.impl_keep_tac`](#Tactic.impl_keep_tac),
[`Tactic.impl_tac`](#Tactic.impl_tac)
