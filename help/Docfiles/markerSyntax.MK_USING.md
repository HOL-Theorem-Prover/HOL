## `MK_USING`

``` hol4
markerSyntax.MK_USING : thm -> thm
```

------------------------------------------------------------------------

Encodes a theorem so it can be `ASSUME_TAC`-ed into a goal.

A call to `MK_USING th` encodes `th` in such a way that it can safely be
the argument to `ASSUME_TAC`, and detectable by other tactics operating
on the resulting goal as a theorem that might be worthy of notice.

### Failure

Fails if the theorem has no hypotheses, is polymorphic, and cannot be
found by reverse lookup in the theorem database (using `DB.revlookup`).

### See also

[`bossLib.using`](#bossLib.using)
