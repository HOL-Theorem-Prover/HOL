## `EXPAND_ALL_BUT_RIGHT_RULE` {#unwindLib.EXPAND_ALL_BUT_RIGHT_RULE}


```
EXPAND_ALL_BUT_RIGHT_RULE : (string list -> thm list -> thm -> thm)
```



Unfolds, then unwinds all lines (except those specified) as much as possible,
then prunes the unwound lines.


`` EXPAND_ALL_BUT_RIGHT_RULE [`li(k+1)`;...;`lim`] thl `` behaves as follows:
    
        A |- !z1 ... zr.
              t = ?l1 ... lm. t1 /\ ... /\ ui1 /\ ... /\ uik /\ ... /\ tn
       -------------------------------------------------------------------
           B u A |- !z1 ... zr. t = ?li(k+1) ... lim. t1' /\ ... /\ tn'
    
where each `ti'` is the result of rewriting `ti` with the theorems in
`thl`. The set of assumptions `B` is the union of the instantiated assumptions
of the theorems used for rewriting. If none of the rewrites are applicable to a
conjunct, it is unchanged. Those conjuncts that after rewriting are equations
for the lines `li1,...,lik` (they are denoted by `ui1,...,uik`) are used to
unwind and the lines `li1,...,lik` are then pruned.

The `li`’s are related by the equation:
    
       {{li1,...,lik}} u {{li(k+1),...,lim}} = {{l1,...,lm}}
    

### Failure

The function may fail if the argument theorem is not of the specified form. It
will also fail if the unwound lines cannot be pruned. It is possible for the
function to attempt unwinding indefinitely (to loop).

### Example

    
    #EXPAND_ALL_BUT_RIGHT_RULE [`l1`]
    # [ASSUME "!in out. INV (in,out) = !(t:num). out t = ~(in t)"]
    # (ASSUME
    #   "!(in:num->bool) out.
    #     DEV(in,out) =
    #      ?l1 l2.
    #       INV (l1,l2) /\ INV (l2,out) /\ (!(t:num). l1 t = in t \/ out (t-1))");;
    .. |- !in out.
           DEV(in,out) =
           (?l1. (!t. out t = ~~l1 t) /\ (!t. l1 t = in t \/ ~~l1(t - 1)))
    

### See also

[`unwindLib.EXPAND_AUTO_RIGHT_RULE`](#unwindLib.EXPAND_AUTO_RIGHT_RULE), [`unwindLib.EXPAND_ALL_BUT_CONV`](#unwindLib.EXPAND_ALL_BUT_CONV), [`unwindLib.EXPAND_AUTO_CONV`](#unwindLib.EXPAND_AUTO_CONV), [`unwindLib.UNFOLD_RIGHT_RULE`](#unwindLib.UNFOLD_RIGHT_RULE), [`unwindLib.UNWIND_ALL_BUT_RIGHT_RULE`](#unwindLib.UNWIND_ALL_BUT_RIGHT_RULE), [`unwindLib.PRUNE_SOME_RIGHT_RULE`](#unwindLib.PRUNE_SOME_RIGHT_RULE)

