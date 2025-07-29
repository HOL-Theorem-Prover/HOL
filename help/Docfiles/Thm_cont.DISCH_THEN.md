## `DISCH_THEN`

``` hol4
Thm_cont.DISCH_THEN : (thm_tactic -> tactic)
```

------------------------------------------------------------------------

Undischarges an antecedent of an implication and passes it to a
theorem-tactic.

`DISCH_THEN` removes the antecedent and then creates a theorem by
`ASSUME`ing it. This new theorem is passed to the theorem-tactic given
as `DISCH_THEN`'s argument. The consequent tactic is then applied. Thus:

``` hol4
   DISCH_THEN f (asl, t1 ==> t2) = f(ASSUME t1) (asl,t2)
```

For example, if

``` hol4
    A ?- t
   ========  f (ASSUME u)
    B ?- v
```

then

``` hol4
    A ?- u ==> t
   ==============  DISCH_THEN f
       B ?- v
```

Note that `DISCH_THEN` treats `~u` as `u ==> F`.

### Failure

`DISCH_THEN` will fail for goals which are not implications or
negations.

### Example

The following shows how `DISCH_THEN` can be used to preprocess an
antecedent before adding it to the assumptions.

``` hol4
    A ?- (x = y) ==> t
   ====================  DISCH_THEN (ASSUME_TAC o SYM)
     A u {y = x} ?- t
```

In many cases, it is possible to use an antecedent and then throw it
away:

``` hol4
    A ?- (x = y) ==> t x
   ======================  DISCH_THEN (\th. PURE_REWRITE_TAC [th])
          A ?- t y
```

### See also

[`Thm.DISCH`](#Thm.DISCH), [`Drule.DISCH_ALL`](#Drule.DISCH_ALL),
[`Tactic.DISCH_TAC`](#Tactic.DISCH_TAC),
[`Drule.NEG_DISCH`](#Drule.NEG_DISCH),
[`Tactic.FILTER_DISCH_TAC`](#Tactic.FILTER_DISCH_TAC),
[`Tactic.FILTER_DISCH_THEN`](#Tactic.FILTER_DISCH_THEN),
[`Tactic.STRIP_TAC`](#Tactic.STRIP_TAC),
[`Drule.UNDISCH`](#Drule.UNDISCH),
[`Drule.UNDISCH_ALL`](#Drule.UNDISCH_ALL),
[`Tactic.UNDISCH_TAC`](#Tactic.UNDISCH_TAC)
