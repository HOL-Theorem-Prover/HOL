## `LAST_ASSUME_TAC`

``` hol4
Tactic.LAST_ASSUME_TAC : thm_tactic
```

------------------------------------------------------------------------

Adds an assumption to the top of the assumptions.

Given a theorem `th` of the form `A' |- u`, and a goal,
`LAST_ASSUME_TAC th` adds `u` to the assumptions of the goal.

``` hol4
         A ?- t
    ==============  LAST_ASSUME_TAC (A' |- u)
     {u} u A ?- t
```

Note that unless `A'` is a subset of `A`, this tactic is invalid.

### Failure

Never fails.

`LAST_ASSUME_TAC` is the naive way of manipulating assumptions
(i.e. without recourse to advanced tacticals); and it is useful for
enriching the assumption list with lemmas as a prelude to resolution
(`RES_TAC`, `IMP_RES_TAC`), rewriting with assumptions
(`ASM_REWRITE_TAC` and so on), and other operations involving
assumptions.

### See also

[`Tactic.ASSUME_TAC`](#Tactic.ASSUME_TAC)
