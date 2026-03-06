## `restore`

``` hol4
proofManagerLib.restore : unit -> proof
```

------------------------------------------------------------------------

Restores the proof state of the last save point, undoing the effects of
expansions after the save point.

The function `restore` is part of the subgoal package. A call to
`restore` restores the proof state to the last save point (a proof state
saved by `save`). If the current state is a save point then `restore`
clears the current save point and returns to the last save point. If
there are no save points in the history, then `restore` returns to the
initial goal and is equivalent to `restart`. For a description of the
subgoal package, see `set_goal`.

### Failure

The function `restore` will fail only if no goalstack is being managed.

Back tracking in a goal-directed proof to a user-defined save point.

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
