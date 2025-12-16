## `PRED_ASSUM`

``` hol4
Tactical.PRED_ASSUM : (term -> bool) -> thm_tactic -> tactic
```

------------------------------------------------------------------------

Discharges a selected assumption and passes it to a theorem-tactic.

`PRED_ASSUM` finds the first assumption satisfying the prediate given,
removes it from the assumption list, `ASSUME`s it, passes it to the
theorem-tactic and then applies the consequent tactic. Thus, where `t`
is the first assumption satisfying `p`,

``` hol4
   PRED_ASSUM p f ([a1,... ai, t, aj, ... an], goal) =
     f (ASSUME t) ([a1,... ai, aj,... an], goal)
```

For example (again, where `t` is the first assumption in `A u {t}`
satisfying `p`), if

``` hol4
    A ?- c
   ========  f (ASSUME t)
    B ?- v
```

then

``` hol4
    A u {t} ?- c
   ===============  PRED_ASSUM p f
       B ?- v
```

### Failure

`PRED_ASSUM p` will fail on goals where no assumption safisfies `p`.

### See also

[`Thm_cont.UNDISCH_THEN`](#Thm_cont.UNDISCH_THEN),
[`Tactical.PAT_ASSUM`](#Tactical.PAT_ASSUM),
[`Tactical.POP_ASSUM`](#Tactical.POP_ASSUM),
[`Tactic.UNDISCH_TAC`](#Tactic.UNDISCH_TAC)
