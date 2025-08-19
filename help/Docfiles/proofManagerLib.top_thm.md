## `top_thm`

``` hol4
proofManagerLib.top_thm : unit -> thm
```

------------------------------------------------------------------------

Returns the theorem just proved using the subgoal package.

The function `top_thm` is part of the subgoal package. A proof state of
the package consists of either goal and justification stacks if a proof
is in progress or a theorem if a proof has just been completed. If the
proof state consists of a theorem, `top_thm` returns that theorem. For a
description of the subgoal package, see `set_goal`.

### Failure

`top_thm` will fail if the proof state does not hold a theorem. This
will be so either because no goal has been set or because a proof is in
progress with unproven subgoals.

Accessing the result of an interactive proof session with the subgoal
package.

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
