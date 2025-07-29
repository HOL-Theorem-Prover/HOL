## `LAST_ASSUM`

``` hol4
Tactical.LAST_ASSUM : (thm_tactic -> tactic)
```

------------------------------------------------------------------------

Maps a theorem-tactic over the assumptions, in reverse order, applying
first successful tactic.

`LAST_ASSUM` behaves like `FIRST_ASSUM`, except that it goes through the
list of assumptions in reverse order

### See also

[`Tactical.FIRST_ASSUM`](#Tactical.FIRST_ASSUM),
[`Tactical.LAST_X_ASSUM`](#Tactical.LAST_X_ASSUM)
