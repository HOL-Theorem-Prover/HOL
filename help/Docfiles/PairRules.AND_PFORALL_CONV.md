## `AND_PFORALL_CONV` {#PairRules.AND_PFORALL_CONV}


```
AND_PFORALL_CONV : conv
```



Moves a paired universal quantification outwards through a conjunction.


When applied to a term of the form `(!p. t) /\ (!p. t)`, the conversion
`AND_PFORALL_CONV` returns the theorem:
    
       |- (!p. t) /\ (!p. u) = (!p. t /\ u)
    



### Failure

Fails if applied to a term not of the form `(!p. t) /\ (!p. t)`.

### See also

[`Conv.AND_FORALL_CONV`](#Conv.AND_FORALL_CONV), [`PairRules.PFORALL_AND_CONV`](#PairRules.PFORALL_AND_CONV), [`PairRules.LEFT_AND_PFORALL_CONV`](#PairRules.LEFT_AND_PFORALL_CONV), [`PairRules.RIGHT_AND_PFORALL_CONV`](#PairRules.RIGHT_AND_PFORALL_CONV)

