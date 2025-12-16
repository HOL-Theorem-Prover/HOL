## `DISCH_ALL`

``` hol4
Drule.DISCH_ALL : thm -> thm
```

------------------------------------------------------------------------

Discharges all hypotheses of a theorem.

``` hol4
         A1, ..., An |- t
   ----------------------------  DISCH_ALL
    |- A1 ==> ... ==> An ==> t
```

### Failure

`DISCH_ALL` never fails. If there are no hypotheses to discharge, it
will simply return the theorem unchanged.

### Comments

Users should not rely on the hypotheses being discharged in any
particular order.

### See also

[`Thm.DISCH`](#Thm.DISCH), [`Tactic.DISCH_TAC`](#Tactic.DISCH_TAC),
[`Thm_cont.DISCH_THEN`](#Thm_cont.DISCH_THEN),
[`Drule.NEG_DISCH`](#Drule.NEG_DISCH),
[`Tactic.FILTER_DISCH_TAC`](#Tactic.FILTER_DISCH_TAC),
[`Tactic.FILTER_DISCH_THEN`](#Tactic.FILTER_DISCH_THEN),
[`Tactic.STRIP_TAC`](#Tactic.STRIP_TAC),
[`Drule.UNDISCH`](#Drule.UNDISCH),
[`Drule.UNDISCH_ALL`](#Drule.UNDISCH_ALL),
[`Tactic.UNDISCH_TAC`](#Tactic.UNDISCH_TAC)
