## `wlog_then`

``` hol4
wlogLib.wlog_then : term quotation -> term quotation list -> thm_tactic -> tactic
```

------------------------------------------------------------------------

Apply a theorem-tactic using a proposition that can be assumed without
loss of generality.

`wlogLib.wlog_then` is identical to `bossLib.wlog_then`
