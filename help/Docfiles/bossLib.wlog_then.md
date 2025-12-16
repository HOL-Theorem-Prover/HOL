## `wlog_then`

``` hol4
bossLib.wlog_then : term quotation -> term quotation list -> thm_tactic -> tactic
```

------------------------------------------------------------------------

Apply a theorem-tactic using a proposition that can be assumed without
loss of generality.

Like `wlog_tac`, but the theorem `P |- P` is passed to the user-provided
theorem-tactic instead of `strip_assume_tac`.

### Failure

Never fails when applied to a theorem-tactical. The resulting tactic
fails if and only if the user-provided theorem-tactical fails when used
as a tactic (i.e.: when applied to a theorem and a goal).

### See also

[`bossLib.wlog_tac`](#bossLib.wlog_tac)
