## `expand_listf`

``` hol4
proofManagerLib.expand_listf : (list_tactic -> unit)
```

------------------------------------------------------------------------

Applies a list-tactic to the current goal, stacking the resulting
subgoals.

The function `expand_listf` is a faster version of `expand_list`. It
does not use a validated version of the list-tactic. That is, no check
is made that the justification of the list-tactic does prove the goals
from the subgoals it generates. If an invalid list-tactic is used, the
theorem ultimately proved may not match the goal originally set.
Alternatively, failure may occur when the justifications are applied in
which case the theorem would not be proved. For a description of the
subgoal package, see under `set_goal`.

### Failure

Calling `expand_listf ltac` fails if the list-tactic `ltac` fails for
the current goal list. It will diverge if the list-tactic diverges for
the goals. It will fail if there are no unproven goals. This could be
because no goal has been set using `set_goal` or because the last goal
set has been completely proved. If an invalid tactic, whose
justification actually fails, has been used earlier in the proof,
`expand_listf ltac` may succeed in applying `ltac` and apparently prove
the current goals. It may then fail as it applies the justifications of
the tactics applied earlier.

Saving CPU time when doing goal-directed proofs, since the extra
validation is not done. Redoing proofs quickly that are already known to
work.

### Comments

The CPU time saved may cause misery later. If an invalid tactic or
list-tactic is used, this will only be discovered when the proof has
apparently been finished and the justifications are applied.

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
[`proofManagerLib.expand_list`](#proofManagerLib.expand_list),
[`proofManagerLib.p`](#proofManagerLib.p),
[`proofManagerLib.top_thm`](#proofManagerLib.top_thm),
[`proofManagerLib.top_goal`](#proofManagerLib.top_goal)
