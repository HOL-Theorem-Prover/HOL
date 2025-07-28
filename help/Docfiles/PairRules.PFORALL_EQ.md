## `PFORALL_EQ` {#PairRules.PFORALL_EQ}


```
PFORALL_EQ : (term -> thm -> thm)
```



Universally quantifies both sides of an equational theorem.


When applied to a paired structure of variables `p`
and a theorem
    
        A |- t1 = t2
    

whose conclusion is an equation between boolean terms:
    
        PFORALL_EQ
    

returns the theorem:
    
        A |- (!p. t1) = (!p. t2)
    

unless any of the variables in `p` is free in any of the assumptions.
    
              A |- t1 = t2
       --------------------------  PFORALL_EQ "p"      [where p is not free in A]
        A |- (!p. t1) = (!p. t2)
    



### Failure

Fails if the theorem is not an equation between boolean terms, or if the
supplied term is not a paired structure of variables, or if any of the
variables in the supplied pair is free in any of the assumptions.

### See also

[`Drule.FORALL_EQ`](#Drule.FORALL_EQ), [`PairRules.PEXISTS_EQ`](#PairRules.PEXISTS_EQ), [`PairRules.PSELECT_EQ`](#PairRules.PSELECT_EQ)

