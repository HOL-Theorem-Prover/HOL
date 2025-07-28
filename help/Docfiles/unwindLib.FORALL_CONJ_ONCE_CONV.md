## `FORALL_CONJ_ONCE_CONV` {#unwindLib.FORALL_CONJ_ONCE_CONV}


```
FORALL_CONJ_ONCE_CONV : conv
```



Moves a single universal quantifier down through a tree of conjunctions.


`FORALL_CONJ_ONCE_CONV "!x. t1 /\ ... /\ tn"` returns the theorem:
    
       |- !x. t1 /\ ... /\ tn = (!x. t1) /\ ... /\ (!x. tn)
    
where the original term can be an arbitrary tree of conjunctions. The
structure of the tree is retained in both sides of the equation.

### Failure

Fails if the argument term is not of the required form. The body of the term
need not be a conjunction.

### Example

    
    #FORALL_CONJ_ONCE_CONV "!x. ((x \/ a) /\ (x \/ b)) /\ (x \/ c)";;
    |- (!x. ((x \/ a) /\ (x \/ b)) /\ (x \/ c)) =
       ((!x. x \/ a) /\ (!x. x \/ b)) /\ (!x. x \/ c)
    
    #FORALL_CONJ_ONCE_CONV "!x. x \/ a";;
    |- (!x. x \/ a) = (!x. x \/ a)
    
    #FORALL_CONJ_ONCE_CONV "!x. ((x \/ a) /\ (y \/ b)) /\ (x \/ c)";;
    |- (!x. ((x \/ a) /\ (y \/ b)) /\ (x \/ c)) =
       ((!x. x \/ a) /\ (!x. y \/ b)) /\ (!x. x \/ c)
    

### See also

[`unwindLib.CONJ_FORALL_ONCE_CONV`](#unwindLib.CONJ_FORALL_ONCE_CONV), [`unwindLib.FORALL_CONJ_CONV`](#unwindLib.FORALL_CONJ_CONV), [`unwindLib.CONJ_FORALL_CONV`](#unwindLib.CONJ_FORALL_CONV), [`unwindLib.FORALL_CONJ_RIGHT_RULE`](#unwindLib.FORALL_CONJ_RIGHT_RULE), [`unwindLib.CONJ_FORALL_RIGHT_RULE`](#unwindLib.CONJ_FORALL_RIGHT_RULE)

