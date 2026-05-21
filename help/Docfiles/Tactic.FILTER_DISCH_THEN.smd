## `FILTER_DISCH_THEN`

``` hol4
Tactic.FILTER_DISCH_THEN : (thm_tactic -> term -> tactic)
```

------------------------------------------------------------------------

Conditionally gives to a theorem-tactic the antecedent of an implicative
goal.

If `FILTER_DISCH_THEN`'s second argument, a term, does not occur in the
antecedent, then `FILTER_DISCH_THEN` removes the antecedent and then
creates a theorem by `ASSUME`ing it. This new theorem is passed to
`FILTER_DISCH_THEN`'s first argument, which is subsequently expanded.
For example, if

``` hol4
    A ?- t
   ========  f (ASSUME u)
    B ?- v
```

then

``` hol4
    A ?- u ==> t
   ==============  FILTER_DISCH_THEN f
       B ?- v
```

Note that `FILTER_DISCH_THEN` treats `~u` as `u ==> F`.

### Failure

`FILTER_DISCH_THEN` will fail if a term which is identical, or
alpha-equivalent to `w` occurs free in the antecedent.
`FILTER_DISCH_THEN` will also fail if the theorem is an implication or a
negation.

### Comments

`FILTER_DISCH_THEN` is most easily understood by first understanding
`DISCH_THEN`.

For preprocessing an antecedent before moving it to the assumptions, or
for using antecedents and then throwing them away.

### See also

[`Thm.DISCH`](#Thm.DISCH), [`Drule.DISCH_ALL`](#Drule.DISCH_ALL),
[`Tactic.DISCH_TAC`](#Tactic.DISCH_TAC),
[`Thm_cont.DISCH_THEN`](#Thm_cont.DISCH_THEN),
[`Tactic.FILTER_DISCH_TAC`](#Tactic.FILTER_DISCH_TAC),
[`Drule.NEG_DISCH`](#Drule.NEG_DISCH),
[`Tactic.STRIP_TAC`](#Tactic.STRIP_TAC),
[`Drule.UNDISCH`](#Drule.UNDISCH),
[`Drule.UNDISCH_ALL`](#Drule.UNDISCH_ALL),
[`Tactic.UNDISCH_TAC`](#Tactic.UNDISCH_TAC)
