## `STRIP_ALL_THEN`

``` hol4
Thm_cont.STRIP_ALL_THEN : thm_tactical
```

------------------------------------------------------------------------

Splits a theorem into a list of theorems and then calls the resulting
theorem tactic on it.

Given a theorem `th` `STRIP_ALL_THEN ttac th` splits `th` into a list of
theorems and then applies the `ttac` on the resulting theorems. This is
done by recursively applying `STRIP_THM_THEN` and then calling the `ttac`
if the theorem can't be split anymore.

### Failure

`STRIP_ALL_THEN ttac th` fails if the any application of `ttac` fails,
which is applied with the stripped theorems from `th`.

### Comments

`STRIP_ALL_THEN` behaves exactly like `REPEAT_TCL STRIP_THM_THEN` but is
faster.

### See also

[`Thm_cont.REPEAT_TCL`](#Thm_cont.REPEAT_TCL),
[`Thm_cont.STRIP_ALL_THEN`](#Thm_cont.STRIP_ALL_THEN),
[`Tactic.STRIP_ASSUME_TAC`](#Tactic.STRIP_ASSUME_TAC)
