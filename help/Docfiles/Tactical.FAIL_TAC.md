## `FAIL_TAC`

``` hol4
Tactical.FAIL_TAC : string -> tactic
```

------------------------------------------------------------------------

Tactic which always fails, with the supplied string.

Whatever goal it is applied to, `FAIL_TAC s` always fails with the
string `s`.

### Failure

The application of `FAIL_TAC` to a string never fails; the resulting
tactic always fails.

### Example

The following example uses the fact that if a tactic `t1` solves a goal,
then the tactic `t1 THEN t2` never results in the application of `t2` to
anything, because `t1` produces no subgoals. In attempting to solve the
following goal:

``` hol4
   ?- if x then T else T
```

the tactic

``` hol4
   REWRITE_TAC[] THEN FAIL_TAC "Simple rewriting failed to solve goal"
```

will fail with the message provided, whereas:

``` hol4
   CONV_TAC COND_CONV THEN FAIL_TAC "Using COND_CONV failed to solve goal"
```

will silently solve the goal because `COND_CONV` reduces it to just
`?- T`.

### See also

[`Tactical.ALL_TAC`](#Tactical.ALL_TAC),
[`Tactical.NO_TAC`](#Tactical.NO_TAC)
