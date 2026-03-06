## `enth`

``` hol4
proofManagerLib.enth : tactic -> int -> proof
```

------------------------------------------------------------------------

Applies a tactic to one goal, referenced by number, in the current goal
list, replacing that goal with the resulting subgoals.

`enth tac i` applies `tac` to all the i'th goal in the current goal
list, replacing that goal in the goal list with the subgoals produced by
`tac`. It is an abbreviation for `expand_list (NTH_GOAL tac i)`.

For interactively constructing suitable compound tactics, for example to
test whether a particular subgoal can be proved easily, before attacking
the other subgoals.

### See also

[`proofManagerLib.expand_list`](#proofManagerLib.expand_list),
[`proofManagerLib.elt`](#proofManagerLib.elt),
[`Tactical.NTH_GOAL`](#Tactical.NTH_GOAL),
[`proofManagerLib.set_goal`](#proofManagerLib.set_goal),
[`proofManagerLib.r`](#proofManagerLib.r)
