## `rd`

``` hol4
proofManagerLib.rd : unit -> proof
```

------------------------------------------------------------------------

Restores the proof state, redoing the effects of a previous expansion.

The function `rd` is part of the subgoal package. It is an abbreviation
for the function `redo`. For a description of the subgoal package, see
`set_goal`.

### Failure

As for `redo`.

Back tracking in a goal-directed proof to undo errors or try different
tactics.

### See also

[`proofManagerLib.set_goal`](#proofManagerLib.set_goal),
[`proofManagerLib.restart`](#proofManagerLib.restart),
[`proofManagerLib.b`](#proofManagerLib.b),
[`proofManagerLib.backup`](#proofManagerLib.backup),
[`proofManagerLib.rd`](#proofManagerLib.rd),
[`proofManagerLib.redo`](#proofManagerLib.redo),
[`proofManagerLib.restore`](#proofManagerLib.restore),
[`proofManagerLib.save`](#proofManagerLib.save),
[`proofManagerLib.set_backup`](#proofManagerLib.set_backup),
[`proofManagerLib.expand`](#proofManagerLib.expand),
[`proofManagerLib.expandf`](#proofManagerLib.expandf),
[`proofManagerLib.p`](#proofManagerLib.p),
[`proofManagerLib.top_thm`](#proofManagerLib.top_thm),
[`proofManagerLib.top_goal`](#proofManagerLib.top_goal)
