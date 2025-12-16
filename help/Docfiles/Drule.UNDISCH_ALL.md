## `UNDISCH_ALL`

``` hol4
Drule.UNDISCH_ALL : thm -> thm
```

------------------------------------------------------------------------

Iteratively undischarges antecedents in a chain of implications.

``` hol4
    A |- t1 ==> ... ==> tn ==> t
   ------------------------------  UNDISCH_ALL
        A, t1, ..., tn |- t
```

Note that `UNDISCH_ALL` treats `"~u"` as `"u ==> F"`.

### Failure

`UNDISCH_ALL` never fails. When called on something other than an
implication or negation, it simply returns its argument unchanged.

### Comments

Identical or alpha-equivalent terms which are repeated in
`A, "t1", ..., "tn"` will not be duplicated in the hypotheses of the
resulting theorem.

### See also

[`Thm.DISCH`](#Thm.DISCH), [`Drule.DISCH_ALL`](#Drule.DISCH_ALL),
[`Tactic.DISCH_TAC`](#Tactic.DISCH_TAC),
[`Thm_cont.DISCH_THEN`](#Thm_cont.DISCH_THEN),
[`Drule.NEG_DISCH`](#Drule.NEG_DISCH),
[`Tactic.FILTER_DISCH_TAC`](#Tactic.FILTER_DISCH_TAC),
[`Tactic.FILTER_DISCH_THEN`](#Tactic.FILTER_DISCH_THEN),
[`Tactic.STRIP_TAC`](#Tactic.STRIP_TAC),
[`Drule.UNDISCH`](#Drule.UNDISCH),
[`Tactic.UNDISCH_TAC`](#Tactic.UNDISCH_TAC)
