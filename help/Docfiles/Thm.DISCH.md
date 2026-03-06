## `DISCH`

``` hol4
Thm.DISCH : (term -> thm -> thm)
```

------------------------------------------------------------------------

Discharges an assumption.

``` hol4
       A |- t
--------------------  DISCH u
 A - {u} |- u ==> t
```

### Failure

`DISCH` will fail if `u` is not boolean.

### Comments

The term `u` need not be a hypothesis. Discharging `u` will remove all
identical and alpha-equivalent hypotheses.

### See also

[`Drule.DISCH_ALL`](#Drule.DISCH_ALL),
[`Tactic.DISCH_TAC`](#Tactic.DISCH_TAC),
[`Thm_cont.DISCH_THEN`](#Thm_cont.DISCH_THEN),
[`Tactic.FILTER_DISCH_TAC`](#Tactic.FILTER_DISCH_TAC),
[`Tactic.FILTER_DISCH_THEN`](#Tactic.FILTER_DISCH_THEN),
[`Drule.NEG_DISCH`](#Drule.NEG_DISCH),
[`Tactic.STRIP_TAC`](#Tactic.STRIP_TAC),
[`Drule.UNDISCH`](#Drule.UNDISCH),
[`Drule.UNDISCH_ALL`](#Drule.UNDISCH_ALL),
[`Tactic.UNDISCH_TAC`](#Tactic.UNDISCH_TAC)
