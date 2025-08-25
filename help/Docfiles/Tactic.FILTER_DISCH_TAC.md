## `FILTER_DISCH_TAC`

``` hol4
Tactic.FILTER_DISCH_TAC : (term -> tactic)
```

------------------------------------------------------------------------

Conditionally moves the antecedent of an implicative goal into the
assumptions.

`FILTER_DISCH_TAC` will move the antecedent of an implication into the
assumptions, provided its parameter does not occur in the antecedent.

``` hol4
    A ?- u ==> v
   ==============  FILTER_DISCH_TAC w
    A u {u} ?- v
```

Note that `DISCH_TAC` treats `~u` as `u ==> F`. Unlike `DISCH_TAC`, the
antecedent will be `STRIP`ed into its various components before being
`ASSUME`d. This stripping includes generating multiple goals for
case-analysis of disjunctions. Also, unlike `DISCH_TAC`, should any
component of the discharged antecedent directly imply or contradict the
goal, then this simplification will also be made. Again, unlike
`DISCH_TAC`, `FILTER_DISCH_TAC` will not duplicate identical or
alpha-equivalent assumptions.

### Failure

`FILTER_DISCH_TAC` will fail if a term which is identical, or
alpha-equivalent to `w` occurs free in the antecedent, or if the theorem
is not an implication or a negation.

### Comments

`FILTER_DISCH_TAC w` behaves like
`FILTER_DISCH_THEN STRIP_ASSUME_TAC w`.

### See also

[`Thm.DISCH`](#Thm.DISCH), [`Drule.DISCH_ALL`](#Drule.DISCH_ALL),
[`Tactic.DISCH_TAC`](#Tactic.DISCH_TAC),
[`Thm_cont.DISCH_THEN`](#Thm_cont.DISCH_THEN),
[`Tactic.FILTER_DISCH_THEN`](#Tactic.FILTER_DISCH_THEN),
[`Drule.NEG_DISCH`](#Drule.NEG_DISCH),
[`Tactic.STRIP_TAC`](#Tactic.STRIP_TAC),
[`Drule.UNDISCH`](#Drule.UNDISCH),
[`Drule.UNDISCH_ALL`](#Drule.UNDISCH_ALL),
[`Tactic.UNDISCH_TAC`](#Tactic.UNDISCH_TAC)
