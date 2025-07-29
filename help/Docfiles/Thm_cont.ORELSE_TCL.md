## `ORELSE_TCL`

``` hol4
Thm_cont.ORELSE_TCL : (thm_tactical * thm_tactical -> thm_tactical)
```

------------------------------------------------------------------------

Applies a theorem-tactical, and if it fails, tries a second.

When applied to two theorem-tacticals, `ttl1` and `ttl2`, a
theorem-tactic `ttac`, and a theorem `th`, if `ttl1 ttac th` succeeds,
that gives the result. If it fails, the result is `ttl2 ttac th`, which
may itself fail.

### Failure

`ORELSE_TCL` fails if both the theorem-tacticals fail when applied to
the given theorem-tactic and theorem.

### See also

[`Thm_cont.EVERY_TCL`](#Thm_cont.EVERY_TCL),
[`Thm_cont.FIRST_TCL`](#Thm_cont.FIRST_TCL),
[`Thm_cont.THEN_TCL`](#Thm_cont.THEN_TCL)
