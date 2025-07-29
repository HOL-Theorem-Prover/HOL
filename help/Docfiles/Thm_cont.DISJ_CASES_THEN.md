## `DISJ_CASES_THEN`

``` hol4
Thm_cont.DISJ_CASES_THEN : thm_tactical
```

------------------------------------------------------------------------

Applies a theorem-tactic to each disjunct of a disjunctive theorem.

If the theorem-tactic `f:thm->tactic` applied to either `ASSUME`d
disjunct produces results as follows when applied to a goal `(A ?- t)`:

``` hol4
    A ?- t                                A ?- t
   =========  f (u |- u)      and        =========  f (v |- v)
    A ?- t1                               A ?- t2
```

then applying `DISJ_CASES_THEN f (|- u \/ v)` to the goal `(A ?- t)`
produces two subgoals.

``` hol4
           A ?- t
   ======================  DISJ_CASES_THEN f (|- u \/ v)
    A ?- t1      A ?- t2
```

### Failure

Fails if the theorem is not a disjunction. An invalid tactic is produced
if the theorem has any hypothesis which is not alpha-convertible to an
assumption of the goal.

### Example

Given the theorem

``` hol4
   th = |- (m = 0) \/ (?n. m = SUC n)
```

and a goal of the form `?- (PRE m = m) = (m = 0)`, applying the tactic

``` hol4
   DISJ_CASES_THEN ASSUME_TAC th
```

produces two subgoals, each with one disjunct as an added assumption:

``` hol4
   ?n. m = SUC n ?- (PRE m = m) = (m = 0)

   m = 0 ?- (PRE m = m) = (m = 0)
```

Building cases tactics. For example, `DISJ_CASES_TAC` could be defined
by:

``` hol4
   val DISJ_CASES_TAC = DISJ_CASES_THEN ASSUME_TAC
```

### Comments

Use `DISJ_CASES_THEN2` to apply different tactic generating functions to
each case.

### See also

[`Thm_cont.CHOOSE_THEN`](#Thm_cont.CHOOSE_THEN),
[`Thm_cont.CONJUNCTS_THEN`](#Thm_cont.CONJUNCTS_THEN),
[`Thm_cont.CONJUNCTS_THEN2`](#Thm_cont.CONJUNCTS_THEN2),
[`Thm.DISJ_CASES`](#Thm.DISJ_CASES),
[`Tactic.DISJ_CASES_TAC`](#Tactic.DISJ_CASES_TAC),
[`Thm_cont.DISJ_CASES_THEN2`](#Thm_cont.DISJ_CASES_THEN2),
[`Thm_cont.DISJ_CASES_THENL`](#Thm_cont.DISJ_CASES_THENL),
[`Thm_cont.STRIP_THM_THEN`](#Thm_cont.STRIP_THM_THEN)
