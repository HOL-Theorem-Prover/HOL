## `FILTER_PSTRIP_TAC` {#PairRules.FILTER_PSTRIP_TAC}


```
FILTER_PSTRIP_TAC : (term -> tactic)
```



Conditionally strips apart a goal by eliminating the outermost connective.


Stripping apart a goal in a more careful way than is done by `PSTRIP_TAC` may
be necessary when dealing with quantified terms and implications.
`FILTER_PSTRIP_TAC` behaves like `PSTRIP_TAC`, but it does not strip apart a
goal if it contains a given term.

If `u` is a term, then `FILTER_PSTRIP_TAC u` is a tactic that removes one
outermost occurrence of one of the connectives `!`, `==>`, `~` or `/\` from the
conclusion of the goal `t`, provided the term being stripped does not contain
`u`.  `FILTER_PSTRIP_TAC` will strip paired universal quantifications.
A negation `~t` is treated as the implication `t ==> F`.
`FILTER_PSTRIP_TAC` also breaks apart conjunctions without applying any
filtering.

If `t` is a universally quantified term, `FILTER_PSTRIP_TAC u`
strips off the quantifier:
    
          A ?- !p. v
       ================  FILTER_PSTRIP_TAC "u"       [where p is not u]
         A ?- v[p'/p]
    
where `p'` is a primed variant of the pair `p` that does not contain
any variables that appear free in the assumptions `A`.
If `t` is a conjunction, no filtering is done and `FILTER_PSTRIP_TAC` simply
splits the conjunction:
    
          A ?- v /\ w
       =================  FILTER_PSTRIP_TAC "u"
        A ?- v   A ?- w
    
If `t` is an implication and the antecedent does not contain
a free instance of `u`, then `FILTER_PSTRIP_TAC u` moves the antecedent into the
assumptions and recursively splits the antecedent according to the following
rules (see `PSTRIP_ASSUME_TAC`):
    
        A ?- v1 /\ ... /\ vn ==> v            A ?- v1 \/ ... \/ vn ==> v
       ============================        =================================
           A u {v1,...,vn} ?- v             A u {v1} ?- v ... A u {vn} ?- v
    
         A ?- (?p. w) ==> v
       ====================
        A u {w[p'/p]} ?- v
    
where `p'` is a variant of the pair `p`.

### Failure

`FILTER_PSTRIP_TAC u (A,t)` fails if `t` is not a universally quantified term,
an implication, a negation or a conjunction; or if the term being
stripped contains `u` in the sense described above (conjunction excluded).


`FILTER_PSTRIP_TAC` is used when stripping outer connectives from a goal in a
more delicate way than `PSTRIP_TAC`. A typical application is to keep
stripping by using the tactic `REPEAT (FILTER_PSTRIP_TAC u)`
until one hits the term `u` at which stripping is to stop.

### See also

[`PairRules.PGEN_TAC`](#PairRules.PGEN_TAC), [`PairRules.PSTRIP_GOAL_THEN`](#PairRules.PSTRIP_GOAL_THEN), [`PairRules.FILTER_PSTRIP_THEN`](#PairRules.FILTER_PSTRIP_THEN), [`PairRules.PSTRIP_TAC`](#PairRules.PSTRIP_TAC), [`Tactic.FILTER_STRIP_TAC`](#Tactic.FILTER_STRIP_TAC)

