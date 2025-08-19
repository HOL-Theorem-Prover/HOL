## `FIRST_TCL`

``` hol4
Thm_cont.FIRST_TCL : (thm_tactical list -> thm_tactical)
```

------------------------------------------------------------------------

Applies the first theorem-tactical in a list which succeeds.

When applied to a list of theorem-tacticals, a theorem-tactic and a
theorem, `FIRST_TCL` returns the tactic resulting from the application
of the first theorem-tactical to the theorem-tactic and theorem which
succeeds. The effect is the same as:

``` hol4
   FIRST_TCL [ttl1;...;ttln] = ttl1 ORELSE_TCL ... ORELSE_TCL ttln
```

### Failure

`FIRST_TCL` fails iff each tactic in the list fails when applied to the
theorem-tactic and theorem. This is trivially the case if the list is
empty.

### See also

[`Thm_cont.EVERY_TCL`](#Thm_cont.EVERY_TCL),
[`Thm_cont.ORELSE_TCL`](#Thm_cont.ORELSE_TCL),
[`Thm_cont.REPEAT_TCL`](#Thm_cont.REPEAT_TCL),
[`Thm_cont.THEN_TCL`](#Thm_cont.THEN_TCL)
