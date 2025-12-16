## `NO_THEN`

``` hol4
Thm_cont.NO_THEN : thm_tactical
```

------------------------------------------------------------------------

Theorem-tactical which always fails.

When applied to a theorem-tactic and a theorem, the theorem-tactical
`NO_THEN` always fails with string `` `NO_THEN` ``.

### Failure

Always fails when applied to a theorem-tactic and a theorem (note that
it never gets as far as being applied to a goal!)

Writing compound tactics or tacticals.

### See also

[`Tactical.ALL_TAC`](#Tactical.ALL_TAC),
[`Thm_cont.ALL_THEN`](#Thm_cont.ALL_THEN),
[`Tactical.FAIL_TAC`](#Tactical.FAIL_TAC),
[`Tactical.NO_TAC`](#Tactical.NO_TAC)
