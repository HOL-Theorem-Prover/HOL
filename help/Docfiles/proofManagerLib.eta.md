## `eta`

``` hol4
proofManagerLib.eta : tactic -> proof
```

------------------------------------------------------------------------

Applies a tactic to all goals, on which it succeeds, in the current goal
list, replacing the list with the resulting subgoals.

`eta tac` tries to apply `tac` to all the goals in the current goal
list; replacing the goal list with the list of all the resulting
subgoals. If it fails on a goal, it has no effect on that goal. It is an
abbreviation for `expand_list (TRYALL tac)`.

For interactively constructing suitable compound tactics: in an
interactive proof, the effect of `e (tac1 THEN TRY tac2)` can be
obtained by `e tac1` and then `eta tac2`.

### See also

[`proofManagerLib.expand_list`](#proofManagerLib.expand_list),
[`proofManagerLib.elt`](#proofManagerLib.elt),
[`Tactical.TRYALL`](#Tactical.TRYALL), [`Tactical.TRY`](#Tactical.TRY),
[`proofManagerLib.eall`](#proofManagerLib.eall),
[`proofManagerLib.set_goal`](#proofManagerLib.set_goal)
