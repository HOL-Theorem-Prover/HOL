## `EXPAND_AUTO_CONV` {#unwindLib.EXPAND_AUTO_CONV}


```
EXPAND_AUTO_CONV : (thm list -> conv)
```



Unfolds, then unwinds as much as possible, then prunes the unwound lines.


`EXPAND_AUTO_CONV thl` when applied to the following term:
    
       "?l1 ... lm. t1 /\ ... /\ ui1 /\ ... /\ uik /\ ... /\ tn"
    
returns a theorem of the form:
    
       B |- (?l1 ... lm. t1 /\ ... /\ ui1 /\ ... /\ uik /\ ... /\ tn) =
            (?li(k+1) ... lim. t1' /\ ... /\ tn')
    
where each `ti'` is the result of rewriting `ti` with the theorems in
`thl`. The set of assumptions `B` is the union of the instantiated assumptions
of the theorems used for rewriting. If none of the rewrites are applicable to a
conjunct, it is unchanged. After rewriting, the function decides which of the
resulting terms to use for unwinding, by performing a loop analysis on the
graph representing the dependencies of the lines.

Suppose the function decides to unwind `li1,...,lik` using the terms
`ui1',...,uik'` respectively. Then, after unwinding, the lines `li1,...,lik`
are pruned (provided they have been eliminated from the right-hand sides of the
conjuncts that are equations, and from the whole of any other conjuncts)
resulting in the elimination of `ui1',...,uik'`.

The `li`’s are related by the equation:
    
       {{li1,...,lik}} u {{li(k+1),...,lim}} = {{l1,...,lm}}
    
The loop analysis allows the term to be unwound as much as possible
without the risk of looping. The user is left to deal with the recursive
equations.

### Failure

The function may fail if the argument term is not of the specified form. It
also fails if there is more than one equation for any line variable.

### Example

    
    #EXPAND_AUTO_CONV
    # [ASSUME "!in out. INV (in,out) = !(t:num). out t = ~(in t)"]
    # "?l1 l2.
    #   INV (l1,l2) /\ INV (l2,out) /\ (!(t:num). l1 t = l2 (t-1) \/ out (t-1))";;
    . |- (?l1 l2.
           INV(l1,l2) /\ INV(l2,out) /\ (!t. l1 t = l2(t - 1) \/ out(t - 1))) =
         (?l2.
           (!t. l2 t = ~(l2(t - 1) \/ ~l2(t - 1))) /\ (!t. out t = ~l2 t))
    

### See also

[`unwindLib.EXPAND_ALL_BUT_CONV`](#unwindLib.EXPAND_ALL_BUT_CONV), [`unwindLib.EXPAND_AUTO_RIGHT_RULE`](#unwindLib.EXPAND_AUTO_RIGHT_RULE), [`unwindLib.EXPAND_ALL_BUT_RIGHT_RULE`](#unwindLib.EXPAND_ALL_BUT_RIGHT_RULE), [`unwindLib.UNFOLD_CONV`](#unwindLib.UNFOLD_CONV), [`unwindLib.UNWIND_AUTO_CONV`](#unwindLib.UNWIND_AUTO_CONV), [`unwindLib.PRUNE_SOME_CONV`](#unwindLib.PRUNE_SOME_CONV)

