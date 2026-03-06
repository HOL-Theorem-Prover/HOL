## `elt`

``` hol4
proofManagerLib.elt : list_tactic -> proof
```

------------------------------------------------------------------------

Applies a list-tactic to the current goal list, replacing it with the
resulting subgoals.

The function `elt` is part of the subgoal package. It is an abbreviation
for `expand_list`. For a description of the subgoal package, see
`set_goal`.

### Failure

As for `expand_list`.

Doing a step in an interactive goal-directed proof, where the step may
affect the list of goals produced by the previous step.

### See also

[`proofManagerLib.expand_list`](#proofManagerLib.expand_list),
[`proofManagerLib.set_goal`](#proofManagerLib.set_goal)
