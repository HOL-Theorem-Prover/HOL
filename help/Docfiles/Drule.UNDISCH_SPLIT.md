## `UNDISCH_SPLIT`

``` hol4
Drule.UNDISCH_SPLIT : thm -> thm
```

------------------------------------------------------------------------

Undischarges the antecedent of an implicative theorem, and splits it
into its conjuncts.

``` hol4
    A |- t1a /\ t1b /\ t1c ==> t2
   ------------------------------  UNDISCH_SPLIT
     A, t1a, t1b, t1c |- t2
```

Note that `UNDISCH_SPLIT` treats `"~u"` as `"u ==> F"`.

### Failure

`UNDISCH_SPLIT` will fail on theorems which are not implications or
negations.

### Comments

If a conjunct of the antecedent already appears in (or is
alpha-equivalent to one of) the hypotheses, it will not be duplicated.

### See also

[`Thm.DISCH`](#Thm.DISCH), [`Drule.DISCH_ALL`](#Drule.DISCH_ALL),
[`Tactic.DISCH_TAC`](#Tactic.DISCH_TAC),
[`Thm_cont.DISCH_THEN`](#Thm_cont.DISCH_THEN),
[`Tactic.FILTER_DISCH_TAC`](#Tactic.FILTER_DISCH_TAC),
[`Tactic.FILTER_DISCH_THEN`](#Tactic.FILTER_DISCH_THEN),
[`Drule.NEG_DISCH`](#Drule.NEG_DISCH),
[`Tactic.STRIP_TAC`](#Tactic.STRIP_TAC),
[`Drule.UNDISCH`](#Drule.UNDISCH),
[`Drule.UNDISCH_ALL`](#Drule.UNDISCH_ALL),
[`Drule.UNDISCH_TM`](#Drule.UNDISCH_TM),
[`Tactic.UNDISCH_TAC`](#Tactic.UNDISCH_TAC),
[`Drule.ASSUME_CONJS`](#Drule.ASSUME_CONJS)
