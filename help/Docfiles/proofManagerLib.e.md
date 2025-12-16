## `e`

``` hol4
proofManagerLib.e : tactic -> proof
```

------------------------------------------------------------------------

Applies a tactic to the current goal, stacking the resulting subgoals.

The function `e` is part of the subgoal package. It is an abbreviation
for `expand`. For a description of the subgoal package, see `set_goal`.

### Failure

As for `expand`.

Doing a step in an interactive goal-directed proof.

### See also

[`proofManagerLib.set_goal`](#proofManagerLib.set_goal),
[`proofManagerLib.restart`](#proofManagerLib.restart),
[`proofManagerLib.backup`](#proofManagerLib.backup),
[`proofManagerLib.redo`](#proofManagerLib.redo),
[`proofManagerLib.restore`](#proofManagerLib.restore),
[`proofManagerLib.save`](#proofManagerLib.save),
[`proofManagerLib.set_backup`](#proofManagerLib.set_backup),
[`proofManagerLib.expand`](#proofManagerLib.expand),
[`proofManagerLib.expandf`](#proofManagerLib.expandf),
[`proofManagerLib.p`](#proofManagerLib.p),
[`proofManagerLib.top_thm`](#proofManagerLib.top_thm),
[`proofManagerLib.top_goal`](#proofManagerLib.top_goal)
