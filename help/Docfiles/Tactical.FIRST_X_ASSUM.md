## `FIRST_X_ASSUM` {#Tactical.FIRST_X_ASSUM}


```
FIRST_X_ASSUM : thm_tactic -> tactic
```



Maps a theorem-tactic over the assumptions, applying first successful
tactic and removing the assumption that gave rise to the successful
tactic.


The tactic
    
       FIRST_X_ASSUM ttac ([A1; ...; An], g)
    
has the effect of applying the first tactic which can be
produced by `ttac` from the `ASSUME`d assumptions `(A1 |- A1)`, ...,
`(An |- An)` and which succeeds when applied to the goal.  The
assumption which produced the successful theorem-tactic is removed
from the assumption list (before `ttac` is applied). Failures of
`ttac` to produce a tactic are ignored.

### Failure

Fails if `ttac (Ai |- Ai)` fails for every assumption `Ai`, or if the
assumption list is empty, or if all the tactics produced by `ttac`
fail when applied to the goal.

### Example

The tactic
    
       FIRST_X_ASSUM SUBST_ALL_TAC
    
searches the assumptions for an equality and causes its
right hand side to be substituted for its left hand side throughout
the goal and assumptions.  It also removes the equality from the
assumption list.  Using `FIRST_ASSUM` above would leave an equality on
the assumption list of the form `x = x`.  The tactic
    
       FIRST_X_ASSUM MATCH_MP_TAC
    
searches the assumption list for an implication whose conclusion
matches the goal, reducing the goal to the antecedent of the corresponding
instance of this implication and removing the implication from the
assumption list.

### Comments

The “X” in the name of this tactic is a mnemonic for the “crossing
out” or removal of the assumption found.

By default, the assumption list is printed in reverse order,
with the head of the list printed last.
To process the assumption list in the opposite order, use `LAST_X_ASSUM`

### See also

[`Tactical.FIRST_ASSUM`](#Tactical.FIRST_ASSUM), [`Tactical.LAST_X_ASSUM`](#Tactical.LAST_X_ASSUM), [`Tactical.ASSUM_LIST`](#Tactical.ASSUM_LIST), [`Tactical.EVERY`](#Tactical.EVERY), [`Tactical.PAT_ASSUM`](#Tactical.PAT_ASSUM), [`Tactical.EVERY_ASSUM`](#Tactical.EVERY_ASSUM), [`Tactical.FIRST`](#Tactical.FIRST), [`Tactical.MAP_EVERY`](#Tactical.MAP_EVERY), [`Tactical.MAP_FIRST`](#Tactical.MAP_FIRST), [`Thm_cont.UNDISCH_THEN`](#Thm_cont.UNDISCH_THEN)

