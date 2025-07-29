## `CASE_TAC`

``` hol4
BasicProvers.CASE_TAC : tactic
```

------------------------------------------------------------------------

Case splits on a term `t` that features in the goal as `case t of ...`,
and then performs some simplification.

`BasicProvers.CASE_TAC` first calls `BasicProvers.PURE_CASE_TAC`, which
searches the goal for an instance of `case t of ...` and performs a
`` BasicProvers.Cases_on `t` ``. If this succeeds, it then simplifies
the goal using definitions of `case` constants, plus distinctness and
injectivity theorems for datatypes.

### Comments

When there are multiple `case` constants in the goal, it can be very
convenient to execute the tactic `REPEAT CASE_TAC`. `bossLib.CASE_TAC`
is the same as `BasicProvers.CASE_TAC`.

### Failure

`BasicProvers.CASE_TAC` fails precisely when
`BasicProvers.PURE_CASE_TAC` fails.

### See also

[`BasicProvers.PURE_CASE_TAC`](#BasicProvers.PURE_CASE_TAC)
