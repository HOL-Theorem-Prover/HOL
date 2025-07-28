## `PRUNE_ONCE_CONV` {#unwindLib.PRUNE_ONCE_CONV}


```
PRUNE_ONCE_CONV : conv
```



Prunes one hidden variable.


`PRUNE_ONCE_CONV "?l. t1 /\ ... /\ ti /\ eq /\ t(i+1) /\ ... /\ tp"` returns a
theorem of the form:
    
       |- (?l. t1 /\ ... /\ ti /\ eq /\ t(i+1) /\ ... /\ tp) =
          (t1 /\ ... /\ ti /\ t(i+1) /\ ... /\ tp)
    
where `eq` has the form `"!y1 ... ym. l x1 ... xn = b"` and `l` does
not appear free in the `ti`’s or in `b`. The conversion works if `eq` is not
present, that is if `l` is not free in any of the conjuncts, but does not work
if `l` appears free in more than one of the conjuncts. Each of `m`, `n` and `p`
may be zero.

### Failure

Fails if the argument term is not of the specified form or if `l` is free in
more than one of the conjuncts or if the equation for `l` is recursive.

### Example

    
    #PRUNE_ONCE_CONV "?l2. (!(x:num). l1 x = F) /\ (!x. l2 x = ~(l1 x))";;
    |- (?l2. (!x. l1 x = F) /\ (!x. l2 x = ~l1 x)) = (!x. l1 x = F)
    

### See also

[`unwindLib.PRUNE_ONE_CONV`](#unwindLib.PRUNE_ONE_CONV), [`unwindLib.PRUNE_SOME_CONV`](#unwindLib.PRUNE_SOME_CONV), [`unwindLib.PRUNE_CONV`](#unwindLib.PRUNE_CONV), [`unwindLib.PRUNE_SOME_RIGHT_RULE`](#unwindLib.PRUNE_SOME_RIGHT_RULE), [`unwindLib.PRUNE_RIGHT_RULE`](#unwindLib.PRUNE_RIGHT_RULE)

