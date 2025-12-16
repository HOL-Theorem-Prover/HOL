## `LAST_X_ASSUM`

``` hol4
Tactical.LAST_X_ASSUM : thm_tactic -> tactic
```

------------------------------------------------------------------------

Maps a theorem-tactic over the assumptions, in reverse order, applying
first successful tactic and removing the assumption that gave rise to
the successful tactic.

`LAST_X_ASSUM` behaves like `FIRST_X_ASSUM`, except that it goes through
the list of assumptions in reverse order

### See also

[`Tactical.FIRST_X_ASSUM`](#Tactical.FIRST_X_ASSUM),
[`Tactical.LAST_ASSUM`](#Tactical.LAST_ASSUM)
