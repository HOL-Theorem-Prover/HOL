## `PURE_CASE_TAC`

``` hol4
BasicProvers.PURE_CASE_TAC : tactic
```

------------------------------------------------------------------------

Case splits on a term `t` that features in the goal as `case t of ...`.

`BasicProvers.PURE_CASE_TAC` searches the goal for an instance of
`case t of ...`, and performs a `` BasicProvers.Cases_on `t` ``.

### Failure

`BasicProvers.PURE_CASE_TAC` fails if there is no instance of
`case t of ...` in the goal, where the `case` term is a case constant in
the typebase and all the free variables of `t` are free in the goal.

### See also

[`BasicProvers.CASE_TAC`](#BasicProvers.CASE_TAC)
