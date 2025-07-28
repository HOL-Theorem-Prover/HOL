## `backup` {#proofManagerLib.backup}


```
backup : unit -> proof
```



Restores the proof state, undoing the effects of a previous expansion.


The function `backup` is part of the subgoal package.  It may be abbreviated by
the function `b`. It allows backing up from the last state change (caused by
calls to `expand`, `rotate` and similar functions). The package
maintains a backup list of previous proof states. A call to `backup`  restores
the state to the previous state (which was on top of the backup list). The
current state and the state on top of the backup list are discarded. The
maximum number of proof states saved on the backup list can be set using
`set_backup`. It defaults to 15. Adding new proof states after the maximum is reached causes the earliest
proof state on the list to be discarded. The user may backup repeatedly until
the list is exhausted.  The state restored includes all unproven subgoals or,
if a goal had  been proved in the previous state, the corresponding theorem.
For a description of the subgoal package, see `set_goal`.

### Failure

The function `backup` will fail if the backup list is empty.

### Example

    
    - g `(HD[1;2;3] = 1) /\ (TL[1;2;3] = [2;3])`;
    > val it =
        Proof manager status: 1 proof.
        1. Incomplete:
             Initial goal:
             (HD [1; 2; 3] = 1) /\ (TL [1; 2; 3] = [2; 3])
    
         : proofs
    
    - e CONJ_TAC;
    OK..
    2 subgoals:
    > val it =
        TL [1; 2; 3] = [2; 3]
    
    
        HD [1; 2; 3] = 1
    
         : proof
    
    - backup();
    > val it =
        Initial goal:
    
        (HD [1; 2; 3] = 1) /\ (TL [1; 2; 3] = [2; 3])
    
         : proof
    
    - e (REWRITE_TAC[listTheory.HD, listTheory.TL]);
    OK..
    > val it =
        Initial goal proved.
        |- (HD [1; 2; 3] = 1) /\ (TL [1; 2; 3] = [2; 3]) : proof
    




Back tracking in a goal-directed proof to undo errors or try different tactics.

### See also

[`proofManagerLib.set_goal`](#proofManagerLib.set_goal), [`proofManagerLib.restart`](#proofManagerLib.restart), [`proofManagerLib.b`](#proofManagerLib.b), [`proofManagerLib.backup`](#proofManagerLib.backup), [`proofManagerLib.rd`](#proofManagerLib.rd), [`proofManagerLib.redo`](#proofManagerLib.redo), [`proofManagerLib.restore`](#proofManagerLib.restore), [`proofManagerLib.save`](#proofManagerLib.save), [`proofManagerLib.set_backup`](#proofManagerLib.set_backup), [`proofManagerLib.expand`](#proofManagerLib.expand), [`proofManagerLib.expandf`](#proofManagerLib.expandf), [`proofManagerLib.p`](#proofManagerLib.p), [`proofManagerLib.top_thm`](#proofManagerLib.top_thm), [`proofManagerLib.top_goal`](#proofManagerLib.top_goal)

