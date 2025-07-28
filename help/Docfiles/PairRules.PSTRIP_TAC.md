## `PSTRIP_TAC` {#PairRules.PSTRIP_TAC}


```
PSTRIP_TAC : tactic
```



Splits a goal by eliminating one outermost connective.


Given a goal `(A,t)`, `PSTRIP_TAC` removes one outermost occurrence of one of
the connectives `!`, `==>`, `~` or `/\` from the conclusion of the goal `t`.
If `t` is a universally quantified term, then `STRIP_TAC` strips off the
quantifier. Note that `PSTRIP_TAC` will strip off paired quantifications.
    
         A ?- !p. u
       ==============  PSTRIP_TAC
        A ?- u[p'/p]
    
where `p'` is a primed variant of the pair `p` that does not contain
any variables that appear free in the assumptions `A`.  If `t` is a
conjunction, then `PSTRIP_TAC` simply splits the conjunction into two subgoals:
    
          A ?- v /\ w
       =================  PSTRIP_TAC
        A ?- v   A ?- w
    
If `t` is an implication, `PSTRIP_TAC` moves the antecedent into the
assumptions, stripping conjunctions, disjunctions and existential
quantifiers according to the following rules:
    
        A ?- v1 /\ ... /\ vn ==> v            A ?- v1 \/ ... \/ vn ==> v
       ============================        =================================
           A u {v1,...,vn} ?- v             A u {v1} ?- v ... A u {vn} ?- v
    
         A ?- (?p. w) ==> v
       =====================
        A u {w[p'/p]} ?- v
    
where `p'` is a primed variant of the pair `p` that does not appear
free in `A`. Finally, a negation `~t` is treated as the implication `t ==> F`.

### Failure

`PSTRIP_TAC (A,t)` fails if `t` is not a paired universally quantified term,
an implication, a negation or a conjunction.


When trying to solve a goal, often the best thing to do first
is `REPEAT PSTRIP_TAC` to split the goal up into manageable pieces.

### See also

[`PairRules.PGEN_TAC`](#PairRules.PGEN_TAC), [`PairRules.PSTRIP_GOAL_THEN`](#PairRules.PSTRIP_GOAL_THEN), [`PairRules.FILTER_PSTRIP_THEN`](#PairRules.FILTER_PSTRIP_THEN), [`Tactic.STRIP_TAC`](#Tactic.STRIP_TAC), [`PairRules.FILTER_PSTRIP_TAC`](#PairRules.FILTER_PSTRIP_TAC)

