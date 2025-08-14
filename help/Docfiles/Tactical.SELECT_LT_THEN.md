## `SELECT_LT_THEN`

``` hol4
Tactical.SELECT_LT_THEN : tactic -> tactic -> list_tactic
```

------------------------------------------------------------------------

Applies the first tactic to all goals in the goal-list for which the
tactic succeeds. Then applies the second tactic to the goals resulting
from the first tactic.

Given a list of goals `gl`, an application of `SELECT_LT tac1 tac2` to
`gl` will try to apply `tac1` to each goal in `gl` in turn. If no goal
lets `tac1` succeed, the goal state remains unchanged. Otherwise, the
goals for which `tac1` succeeds will generate (possibly empty) list(s)
of new sub-goals. `tac2` will be applied to each of these new sub-goals.
The resulting subgoals after applying `tac2` are pushed onto the front
of the rest of `gl`.

### Failure

The application of `SELECT_LT_THEN` to tactic arguments `tac1`, `tac2`
never fails. The resulting list-tactic fails only when `tac2` fails on a
subgoal produced by applying `tac1` to the current goals.

### Example

``` hol4
> SELECT_LT_THEN DISJ1_TAC ALL_TAC
>  [([], “T ∨ s”), ([], “p ⇒ q”), ([“a ∨ b”], “p ∨ q”)]
val it =
  ([([], “T”), ([“a ∨ b”], “p”), ([], “p ⇒ q”)], fn):
  goal list * list_validation



> SELECT_LT_THEN DISJ1_TAC (ACCEPT_TAC TRUTH)
>   [([], “T ∨ s”), ([], “p ⇒ q”), ([“a ∨ b”], “p ∨ q”)]
Exception-
   HOL_ERR
     {message = "Could not apply second tactic", origin_function =
      "SELECT_LT_THEN", origin_structure = "Tactical"} raised
```

### See also

[`Tactical.SELECT_LT`](#Tactical.SELECT_LT),
[`Tactical.FIRST_LT`](#Tactical.FIRST_LT),
[`Tactical.THEN_LT`](#Tactical.THEN_LT),
[`Tactical.HEADGOAL`](#Tactical.HEADGOAL)
