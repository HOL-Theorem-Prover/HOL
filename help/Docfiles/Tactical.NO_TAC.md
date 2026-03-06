## `NO_TAC`

``` hol4
Tactical.NO_TAC : tactic
```

------------------------------------------------------------------------

Tactic which always fails.

Whatever goal it is applied to, `NO_TAC` always fails with string
`` `NO_TAC` ``.

### Failure

Always fails.

### See also

[`Tactical.ALL_TAC`](#Tactical.ALL_TAC),
[`Thm_cont.ALL_THEN`](#Thm_cont.ALL_THEN),
[`Tactical.FAIL_TAC`](#Tactical.FAIL_TAC),
[`Thm_cont.NO_THEN`](#Thm_cont.NO_THEN)
