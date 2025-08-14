## `UNDISCH_THEN`

``` hol4
Thm_cont.UNDISCH_THEN : term -> thm_tactic -> tactic
```

------------------------------------------------------------------------

Discharges the assumption given and passes it to a theorem-tactic.

`UNDISCH_THEN` finds the first assumption equal to the term given,
removes it from the assumption list, `ASSUME`s it, passes it to the
theorem-tactic and then applies the consequent tactic. Thus:

``` hol4
   UNDISCH_THEN t f ([a1,... ai, t, aj, ... an], goal) =
     f (ASSUME t) ([a1,... ai, aj,... an], goal)
```

For example, if

``` hol4
    A ?- t
   ========  f (ASSUME t1)
    B ?- v
```

then

``` hol4
    A u {t1} ?- t
   ===============  UNDISCH_THEN t1 f
       B ?- v
```

### Failure

`UNDISCH_THEN` will fail on goals where the given term is not in the
assumption list.

### See also

[`Tactical.PRED_ASSUM`](#Tactical.PRED_ASSUM),
[`Tactical.PAT_ASSUM`](#Tactical.PAT_ASSUM), [`Thm.DISCH`](#Thm.DISCH),
[`Drule.DISCH_ALL`](#Drule.DISCH_ALL),
[`Tactic.DISCH_TAC`](#Tactic.DISCH_TAC),
[`Thm_cont.DISCH_THEN`](#Thm_cont.DISCH_THEN),
[`Drule.NEG_DISCH`](#Drule.NEG_DISCH),
[`Tactic.FILTER_DISCH_TAC`](#Tactic.FILTER_DISCH_TAC),
[`Tactic.FILTER_DISCH_THEN`](#Tactic.FILTER_DISCH_THEN),
[`Tactic.STRIP_TAC`](#Tactic.STRIP_TAC),
[`Drule.UNDISCH`](#Drule.UNDISCH),
[`Drule.UNDISCH_ALL`](#Drule.UNDISCH_ALL),
[`Tactic.UNDISCH_TAC`](#Tactic.UNDISCH_TAC)
