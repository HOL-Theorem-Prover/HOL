## `DISCH_TAC`

``` hol4
Tactic.DISCH_TAC : tactic
```

------------------------------------------------------------------------

Moves the antecedent of an implicative goal into the assumptions.

``` hol4
    A ?- u ==> v
   ==============  DISCH_TAC
    A u {u} ?- v
```

Note that `DISCH_TAC` treats `~u` as `u ==> F`, so will also work when
applied to a goal with a negated conclusion.

### Failure

`DISCH_TAC` will fail for goals which are not implications or negations.

Solving goals of the form `u ==> v` by rewriting `v` with `u`, although
the use of `DISCH_THEN` is usually more elegant in such cases.

### Comments

If the antecedent already appears in the assumptions, it will be
duplicated.

### See also

[`Thm.DISCH`](#Thm.DISCH), [`Drule.DISCH_ALL`](#Drule.DISCH_ALL),
[`Thm_cont.DISCH_THEN`](#Thm_cont.DISCH_THEN),
[`Tactic.FILTER_DISCH_TAC`](#Tactic.FILTER_DISCH_TAC),
[`Tactic.FILTER_DISCH_THEN`](#Tactic.FILTER_DISCH_THEN),
[`Drule.NEG_DISCH`](#Drule.NEG_DISCH),
[`Tactic.STRIP_TAC`](#Tactic.STRIP_TAC),
[`Drule.UNDISCH`](#Drule.UNDISCH),
[`Drule.UNDISCH_ALL`](#Drule.UNDISCH_ALL),
[`Tactic.UNDISCH_TAC`](#Tactic.UNDISCH_TAC)
