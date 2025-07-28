## `expandf` {#proofManagerLib.expandf}


```
expandf : (tactic -> unit)
```



Applies a tactic to the current goal, stacking the resulting subgoals.


The function `expandf` is a faster version of `expand`. It does not use a
validated version of the tactic. That is, no check is made that the
justification of the tactic does prove the goal from the subgoals it generates.
If an invalid tactic is used, the theorem ultimately proved  may not match the
goal originally set. Alternatively, failure may occur when the justifications
are applied in which case the theorem would not be proved. For a description of
the subgoal package, see under `set_goal`.

### Failure

Calling `expandf tac` fails if the tactic `tac` fails for the top goal. It will
diverge if the tactic diverges for the goal. It will fail if there are no
unproven goals. This could be because no goal has been set using `set_goal` or
because the last goal set has been completely proved. If an invalid tactic,
whose justification actually fails, has been used earlier in the proof,
`expandf tac` may succeed in applying `tac` and apparently prove the current
goal. It may then fail as it applies the justifications of the tactics applied
earlier.

### Example

    
       - g `HD[1;2;3] = 1`;
    
       `HD[1;2;3] = 1`
    
       () : void
    
       - expandf (REWRITE_TAC[HD;TL]);;
       OK..
       goal proved
       |- HD[1;2;3] = 1
    
       Previous subproof:
       goal proved
       () : void
    
The following example shows how the use of an invalid tactic can
yield a  theorem which does not correspond to the  goal set.
    
       - set_goal([], Term `1=2`);
       `1 = 2`
    
       () : void
    
       - expandf (REWRITE_TAC[ASSUME (Term`1=2`)]);
       OK..
       goal proved
       . |- 1 = 2
    
       Previous subproof:
       goal proved
       () : void
    
The proof assumed something which was not on the assumption list.
This assumption appears in the assumption list of the theorem proved, even
though it was not in the goal. An attempt to perform the proof using `expand`
fails. The validated version of the tactic detects that the justification
produces a theorem which does not correspond to the goal set. It therefore
fails.


Saving CPU time when doing goal-directed proofs, since the extra validation is
not done. Redoing proofs quickly that are already known to work.

### Comments

The CPU time saved may cause  misery later. If an invalid tactic is used, this
will only be discovered when the proof has apparently been finished and the
justifications are applied.

### See also

[`proofManagerLib.set_goal`](#proofManagerLib.set_goal), [`proofManagerLib.restart`](#proofManagerLib.restart), [`proofManagerLib.backup`](#proofManagerLib.backup), [`proofManagerLib.redo`](#proofManagerLib.redo), [`proofManagerLib.restore`](#proofManagerLib.restore), [`proofManagerLib.save`](#proofManagerLib.save), [`proofManagerLib.set_backup`](#proofManagerLib.set_backup), [`proofManagerLib.expand`](#proofManagerLib.expand), [`proofManagerLib.expandf`](#proofManagerLib.expandf), [`proofManagerLib.p`](#proofManagerLib.p), [`proofManagerLib.top_thm`](#proofManagerLib.top_thm), [`proofManagerLib.top_goal`](#proofManagerLib.top_goal)

