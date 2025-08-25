## `RENAME1_TAC`

``` hol4
Q.RENAME1_TAC : term quotation -> tactic
```

------------------------------------------------------------------------

Finds an instance of a pattern in a goal, and renames to use names from
the pattern.

The tactic `Q.RENAME1_TAC q` is defined to be

``` hol4
   MATCH_RENAME_TAC q ORELSE MATCH_ASSUM_RENAME_TAC q ORELSE
   MATCH_GOALSUB_RENAME_TAC q ORELSE MATCH_ASMSUB_RENAME_TAC q
```

### Failure

Fails if all of the constituent tactics fail.

### Comments

This tactic can be used to force a particular set of names on a goal,
hopefully making the resulting tactic more robust in the face of
underlying implementation changes. Note though that successful use of
this tactic requires that the "new" names in the provided pattern really
be fresh for the goal. If one is really uncertain about what names might
be appearing in a goal, this condition may be difficult to ensure,
particularly as the tactic only looks for one instance of the pattern at
a time (but see `Q.RENAME_TAC`).

This tactic is also available under the alias `bossLib.rename1`.

### See also

[`Q.MATCH_ASMSUB_RENAME_TAC`](#Q.MATCH_ASMSUB_RENAME_TAC),
[`Q.MATCH_ASSUM_RENAME_TAC`](#Q.MATCH_ASSUM_RENAME_TAC),
[`Q.MATCH_GOALSUB_RENAME_TAC`](#Q.MATCH_GOALSUB_RENAME_TAC),
[`Q.MATCH_RENAME_TAC`](#Q.MATCH_RENAME_TAC)
