## `KNOW_TAC`

``` hol4
Tactic.KNOW_TAC : term -> tactic
```

------------------------------------------------------------------------

A shorthand form of `SUBGOAL_THEN`.

A call to `KNOW_TAC t` is equivalent to a call to
`SUBGOAL_THEN t MP_TAC`.

### Failure

A call to `KNOW_TAC t` will fail on being applied to a goal if the
provided term `t` is not of boolean type.

### Comments

If `t` is to be created through parsing a user-provided string, it may
be helpful to do that parsing in the context of the current goal, for
which `Q_TAC` may be helpful.

Equally, the `by` and `suffices_by` tactics have a similar effect:
taking a quotation, and generating two subgoals to be proved. In all
cases, the behaviour is to give the user an opportunity to be creative
in the specification of the fresh sub-goal that arises from applying
modus ponens backwards.

### See also

[`bossLib.by`](#bossLib.by), [`Tactical.Q_TAC`](#Tactical.Q_TAC),
[`Tactic.SUBGOAL_THEN`](#Tactic.SUBGOAL_THEN),
[`Tactic.SUFF_TAC`](#Tactic.SUFF_TAC),
[`bossLib.suffices_by`](#bossLib.suffices_by)
