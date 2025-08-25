## `THEN`

``` hol4
op Tactical.THEN : tactic * tactic -> tactic}
op THEN : list_tactic * tactic -> list_tactic
```

------------------------------------------------------------------------

Applies a tactic to all subgoals produced by a tactic or list-tactic.

If `T1` and `T2` are tactics, `T1 THEN T2` is a tactic which applies
`T1` to a goal, then applies the tactic `T2` to all the subgoals
generated. If `T1` solves the goal then `T2` is never applied.

Alternatively, `T1` may be a list-tactic which is applied to an initial
list of goals.

### Failure

The application of `THEN` to a pair of tactics never fails. The
resulting tactic fails if `T1` fails when applied to the goal, or if
`T2` does when applied to any of the resulting subgoals.

### Comments

Although normally used to sequence tactics which generate a single
subgoal, it is worth remembering that it is sometimes useful to apply
the same tactic to multiple subgoals; sequences like the following:

``` hol4
   EQ_TAC THENL [ASM_REWRITE_TAC[], ASM_REWRITE_TAC[]]
```

can be replaced by the briefer:

``` hol4
   EQ_TAC THEN ASM_REWRITE_TAC[]
```

### See also

[`Tactical.EVERY`](#Tactical.EVERY),
[`Tactical.ORELSE`](#Tactical.ORELSE),
[`Tactical.THENL`](#Tactical.THENL),
[`Tactical.THEN_LT`](#Tactical.THEN_LT)
