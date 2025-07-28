## `STRIP_THM_THEN` {#Thm_cont.STRIP_THM_THEN}


```
STRIP_THM_THEN : thm_tactical
```



`STRIP_THM_THEN` applies the given theorem-tactic using the result of
stripping off one outer connective from the given theorem.


Given a theorem-tactic `ttac`, a theorem `th` whose conclusion is a
conjunction, a disjunction or an existentially quantified term, and a goal
`(A,t)`, `STRIP_THM_THEN ttac th` first strips apart the conclusion of `th`,
next applies `ttac` to the theorem(s) resulting from the stripping and then
applies the resulting tactic to the goal.

In particular, when stripping a conjunctive theorem `A'|- u /\ v`, the tactic
    
       ttac(u|-u) THEN ttac(v|-v)
    
resulting from applying `ttac` to the conjuncts, is applied to the
goal.  When stripping a disjunctive theorem `A'|- u \/ v`, the tactics
resulting from applying `ttac` to the disjuncts, are applied to split the goal
into two cases. That is, if
    
        A ?- t                           A ?- t
       =========  ttac (u|-u)    and    =========  ttac (v|-v)
        A ?- t1                          A ?- t2
    
then:
    
             A ?- t
       ==================  STRIP_THM_THEN ttac (A'|- u \/ v)
        A ?- t1  A ?- t2
    
When stripping an existentially quantified theorem `A'|- ?x.u`, the
tactic `ttac(u|-u)`, resulting from applying `ttac` to the body of the
existential quantification, is applied to the goal.  That is, if:
    
        A ?- t
       =========  ttac (u|-u)
        A ?- t1
    
then:
    
          A ?- t
       =============  STRIP_THM_THEN ttac (A'|- ?x. u)
          A ?- t1
    

The assumptions of the theorem being split are not added to the assumptions of
the goal(s) but are recorded in the proof.  If `A'` is not a subset of the
assumptions `A` of the goal (up to alpha-conversion), `STRIP_THM_THEN ttac th`
results in an invalid tactic.

### Failure

`STRIP_THM_THEN ttac th` fails if the conclusion of `th` is not a conjunction,
a disjunction or an existentially quantified term.  Failure also occurs if the
application of `ttac` fails, after stripping the outer connective from the
conclusion of `th`.


`STRIP_THM_THEN` is used enrich the assumptions of a goal with a stripped
version of a previously-proved theorem.

### See also

[`Thm_cont.CHOOSE_THEN`](#Thm_cont.CHOOSE_THEN), [`Thm_cont.CONJUNCTS_THEN`](#Thm_cont.CONJUNCTS_THEN), [`Thm_cont.DISJ_CASES_THEN`](#Thm_cont.DISJ_CASES_THEN), [`Tactic.STRIP_ASSUME_TAC`](#Tactic.STRIP_ASSUME_TAC)

