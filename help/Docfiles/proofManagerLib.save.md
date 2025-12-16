## `save`

``` hol4
proofManagerLib.save : unit -> proof
```

------------------------------------------------------------------------

Marks the current proof state as a save point, and clears the automatic
undo history.

The function `save` is part of the subgoal package. A call to `save`
clears the automatic proof history and marks the current state as a save
point. A call to `backup` at a save point will fail. In contrast to
`forget_history`, however, `save` does not clear the initial goal or any
previous save points. Therefore a call to `restore` or `restart` at a
save point will succeed. For a description of the subgoal package, see
`set_goal`.

### Failure

The function `save` will fail only if no goalstack is being managed.

Creating save points in an interactive proof, to allow user-directed
back tracking. This is in contrast to the automatic back tracking
facilitated by `backup`.

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
