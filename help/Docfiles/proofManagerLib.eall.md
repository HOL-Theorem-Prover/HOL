## `eall`

``` hol4
proofManagerLib.eall : tactic -> proof
```

------------------------------------------------------------------------

Applies a tactic to all goals in the current goal list, replacing the
list with the resulting subgoals.

`eall tac` applies `tac` to all the goals in the current goal list,
replacing the goal list with the list of all the resulting subgoals. It
is an abbreviation for `expand_list (ALLGOALS tac)`.

For interactively constructing suitable compound tactics: in an
interactive proof, the effect of `e (tac1 THEN tac2)` can be obtained by
`e tac1` and then `eall tac2`.

### See also

[`proofManagerLib.expand_list`](#proofManagerLib.expand_list),
[`proofManagerLib.elt`](#proofManagerLib.elt),
[`Tactical.ALLGOALS`](#Tactical.ALLGOALS),
[`proofManagerLib.eta`](#proofManagerLib.eta),
[`proofManagerLib.set_goal`](#proofManagerLib.set_goal)
