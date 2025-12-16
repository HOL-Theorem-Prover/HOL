## `FIRST_LT`

``` hol4
Tactical.FIRST_LT : tactic -> list_tactic
```

------------------------------------------------------------------------

Applies a tactic to the first goal in the goal-list that works.

Given a list of goals `gl`, an application of `FIRST_LT tac` to `gl`
will try to apply `tac` to each goal in `gl` in turn. If no goal lets
`tac` succeed, the whole application fails also. Otherwise, the first
goal on which `tac` succeeds will generate a (possibly empty) list of
new sub-goals. These new sub-goals are pushed onto the front of the rest
of `gl`.

### Failure

The application of `FIRST_LT` to a tactic never fails. The resulting
list-tactic fails if the goal list is empty, or if argument `tac` fails
on each goal in the list `gl`.

### Example

``` hol4
> FIRST_LT CONJ_TAC [([], “p ⇒ q”), ([“a ∨ b”], “p /\ q”)]
val it = ([([“a ∨ b”], “p”), ([“a ∨ b”], “q”), ([], “p ⇒ q”)], fn):
  goal list * list_validation
```

### See also

[`Tactical.THEN_LT`](#Tactical.THEN_LT),
[`Tactical.HEADGOAL`](#Tactical.HEADGOAL)
