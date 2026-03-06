## `UNDISCH_TAC`

``` hol4
Tactic.UNDISCH_TAC : term -> tactic
```

------------------------------------------------------------------------

Undischarges an assumption and deletes all assumptions that are
alpha-equivalent to it.

Let `a1` to `an` be the assumptions that are alpha-equivalent to `v`,
then

``` hol4
               A ?- t
   ==============================  UNDISCH_TAC v
    A - {a1, ..., an} ?- v ==> t
```

In particular, if `v` is among the assumptions of the goal and no other
assumption is alpha-equivalent to it, then `UNDISCH_TAC` behaves as the
opposite of `DISCH_TAC`:

``` hol4
          A ?- t
   ====================  UNDISCH_TAC v
    A - {v} ?- v ==> t
```

### Failure

`UNDISCH_TAC` fails if no assumption is alpha-equivalent to `v`.

### Comments

In the typical use `v` is among the assumptions. If only a single
assumption alpha-equivalent to `v`, but it is different from `v` then
the action of `UNDISCH_TAC` can be seen as undischarging followed by
alpha-conversion.

### See also

[`Thm.DISCH`](#Thm.DISCH), [`Drule.DISCH_ALL`](#Drule.DISCH_ALL),
[`Tactic.DISCH_TAC`](#Tactic.DISCH_TAC),
[`Thm_cont.DISCH_THEN`](#Thm_cont.DISCH_THEN),
[`Drule.NEG_DISCH`](#Drule.NEG_DISCH),
[`Tactic.FILTER_DISCH_TAC`](#Tactic.FILTER_DISCH_TAC),
[`Tactic.FILTER_DISCH_THEN`](#Tactic.FILTER_DISCH_THEN),
[`Tactic.STRIP_TAC`](#Tactic.STRIP_TAC),
[`Drule.UNDISCH`](#Drule.UNDISCH),
[`Drule.UNDISCH_ALL`](#Drule.UNDISCH_ALL)
