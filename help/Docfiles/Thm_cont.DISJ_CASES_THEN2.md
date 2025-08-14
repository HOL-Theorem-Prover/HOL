## `DISJ_CASES_THEN2`

``` hol4
Thm_cont.DISJ_CASES_THEN2 : (thm_tactic -> thm_tactical)
```

------------------------------------------------------------------------

Applies separate theorem-tactics to the two disjuncts of a theorem.

If the theorem-tactics `f1` and `f2`, applied to the `ASSUME`d left and
right disjunct of a theorem `|- u \/ v` respectively, produce results as
follows when applied to a goal `(A ?- t)`:

``` hol4
    A ?- t                                 A ?- t
   =========  f1 (u |- u)      and        =========  f2 (v |- v)
    A ?- t1                                A ?- t2
```

then applying `DISJ_CASES_THEN2 f1 f2 (|- u \/ v)` to the goal
`(A ?- t)` produces two subgoals.

``` hol4
           A ?- t
   ======================  DISJ_CASES_THEN2 f1 f2 (|- u \/ v)
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
   DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC th
```

to the goal will produce two subgoals

``` hol4
   ?n. m = SUC n ?- (PRE m = m) = (m = 0)

   ?- (PRE 0 = 0) = (0 = 0)
```

The first subgoal has had the disjunct `m = 0` used for a substitution,
and the second has added the disjunct to the assumption list.
Alternatively, applying the tactic

``` hol4
   DISJ_CASES_THEN2 SUBST1_TAC (CHOOSE_THEN SUBST1_TAC) th
```

to the goal produces the subgoals:

``` hol4
   ?- (PRE(SUC n) = SUC n) = (SUC n = 0)

   ?- (PRE 0 = 0) = (0 = 0)
```

Building cases tacticals. For example, `DISJ_CASES_THEN` could be
defined by:

``` hol4
  let DISJ_CASES_THEN f = DISJ_CASES_THEN2 f f
```

### See also

[`Thm_cont.STRIP_THM_THEN`](#Thm_cont.STRIP_THM_THEN),
[`Thm_cont.CHOOSE_THEN`](#Thm_cont.CHOOSE_THEN),
[`Thm_cont.CONJUNCTS_THEN`](#Thm_cont.CONJUNCTS_THEN),
[`Thm_cont.CONJUNCTS_THEN2`](#Thm_cont.CONJUNCTS_THEN2),
[`Thm_cont.DISJ_CASES_THEN`](#Thm_cont.DISJ_CASES_THEN),
[`Thm_cont.DISJ_CASES_THENL`](#Thm_cont.DISJ_CASES_THENL)
