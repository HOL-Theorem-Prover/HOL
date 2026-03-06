## `SELECT_LT`

``` hol4
Tactical.SELECT_LT : tactic -> list_tactic
```

------------------------------------------------------------------------

Applies a tactic to the all the goals in the goal-list for which the
tactic succeeds.

Given a list of goals `gl`, an application of `SELECT_LT tac` to `gl`
will try to apply `tac` to each goal in `gl` in turn. If no goal lets
`tac` succeed, the goal state remains unchanged. Otherwise, the goals
for which `tac` succeeds will generate (possibly empty) list(s) of new
sub-goals. These new sub-goals are pushed onto the front of the rest of
`gl`.

### Failure

The application of `SELECT_LT` to a tactic never fails. The resulting
list-tactic also never fails.

### Example

``` hol4
> SELECT_LT CONJ_TAC [([], “r ∧ s”), ([], “p ⇒ q”), ([“a ∨ b”], “p ∧ q”)]
val it =
  ([([], “r”), ([], “s”), ([“a ∨ b”], “p”), ([“a ∨ b”], “q”), ([], “p ⇒ q”)], fn):
  goal list * list_validation
```

### See also

[`Tactical.SELECT_LT_THEN`](#Tactical.SELECT_LT_THEN),
[`Tactical.FIRST_LT`](#Tactical.FIRST_LT),
[`Tactical.THEN_LT`](#Tactical.THEN_LT),
[`Tactical.HEADGOAL`](#Tactical.HEADGOAL)
