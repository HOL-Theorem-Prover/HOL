## `DISJ_CASES_THENL`

``` hol4
Thm_cont.DISJ_CASES_THENL : (thm_tactic list -> thm_tactic)
```

------------------------------------------------------------------------

Applies theorem-tactics in a list to the corresponding disjuncts in a
theorem.

If the theorem-tactics `f1...fn` applied to the `ASSUME`d disjuncts of a
theorem

``` hol4
   |- d1 \/ d2 \/...\/ dn
```

produce results as follows when applied to a goal `(A ?- t)`:

``` hol4
    A ?- t                                A ?- t
   =========  f1 (d1 |- d1) and ... and =========  fn (dn |- dn)
    A ?- t1                              A ?- tn
```

then applying `DISJ_CASES_THENL [f1;...;fn] (|- d1 \/...\/ dn)` to the
goal `(A ?- t)` produces n subgoals.

``` hol4
           A ?- t
   =======================  DISJ_CASES_THENL [f1;...;fn] (|- d1 \/...\/ dn)
    A ?- t1  ...  A ?- tn
```

`DISJ_CASES_THENL` is defined using iteration, hence for theorems with
more than `n` disjuncts, `dn` would itself be disjunctive.

### Failure

Fails if the number of tactic generating functions in the list exceeds
the number of disjuncts in the theorem. An invalid tactic is produced if
the theorem has any hypothesis which is not alpha-convertible to an
assumption of the goal.

Used when the goal is to be split into several cases, where a different
tactic-generating function is to be applied to each case.

### See also

[`Thm_cont.CHOOSE_THEN`](#Thm_cont.CHOOSE_THEN),
[`Thm_cont.CONJUNCTS_THEN`](#Thm_cont.CONJUNCTS_THEN),
[`Thm_cont.CONJUNCTS_THEN2`](#Thm_cont.CONJUNCTS_THEN2),
[`Thm_cont.DISJ_CASES_THEN`](#Thm_cont.DISJ_CASES_THEN),
[`Thm_cont.DISJ_CASES_THEN2`](#Thm_cont.DISJ_CASES_THEN2),
[`Thm_cont.STRIP_THM_THEN`](#Thm_cont.STRIP_THM_THEN)
