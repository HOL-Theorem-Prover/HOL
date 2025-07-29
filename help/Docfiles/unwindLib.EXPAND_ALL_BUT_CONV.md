## `EXPAND_ALL_BUT_CONV`

``` hol4
unwindLib.EXPAND_ALL_BUT_CONV : (string list -> thm list -> conv)
```

------------------------------------------------------------------------

Unfolds, then unwinds all lines (except those specified) as much as
possible, then prunes the unwound lines.

`` EXPAND_ALL_BUT_CONV [`li(k+1)`;...;`lim`] thl `` when applied to the
following term:

``` hol4
   "?l1 ... lm. t1 /\ ... /\ ui1 /\ ... /\ uik /\ ... /\ tn"
```

returns a theorem of the form:

``` hol4
   B |- (?l1 ... lm. t1 /\ ... /\ ui1 /\ ... /\ uik /\ ... /\ tn) =
        (?li(k+1) ... lim. t1' /\ ... /\ tn')
```

where each `ti'` is the result of rewriting `ti` with the theorems in
`thl`. The set of assumptions `B` is the union of the instantiated
assumptions of the theorems used for rewriting. If none of the rewrites
are applicable to a conjunct, it is unchanged. Those conjuncts that
after rewriting are equations for the lines `li1,...,lik` (they are
denoted by `ui1,...,uik`) are used to unwind and the lines `li1,...,lik`
are then pruned.

The `li`'s are related by the equation:

``` hol4
   {{li1,...,lik}} u {{li(k+1),...,lim}} = {{l1,...,lm}}
```

### Failure

The function may fail if the argument term is not of the specified form.
It will also fail if the unwound lines cannot be pruned. It is possible
for the function to attempt unwinding indefinitely (to loop).

### Example

``` hol4
#EXPAND_ALL_BUT_CONV [`l1`]
# [ASSUME "!in out. INV (in,out) = !(t:num). out t = ~(in t)"]
# "?l1 l2.
#   INV (l1,l2) /\ INV (l2,out) /\ (!(t:num). l1 t = l2 (t-1) \/ out (t-1))";;
. |- (?l1 l2.
       INV(l1,l2) /\ INV(l2,out) /\ (!t. l1 t = l2(t - 1) \/ out(t - 1))) =
     (?l1.
       (!t. out t = ~~l1 t) /\ (!t. l1 t = ~l1(t - 1) \/ ~~l1(t - 1)))
```

### See also

[`unwindLib.EXPAND_AUTO_CONV`](#unwindLib.EXPAND_AUTO_CONV),
[`unwindLib.EXPAND_ALL_BUT_RIGHT_RULE`](#unwindLib.EXPAND_ALL_BUT_RIGHT_RULE),
[`unwindLib.EXPAND_AUTO_RIGHT_RULE`](#unwindLib.EXPAND_AUTO_RIGHT_RULE),
[`unwindLib.UNFOLD_CONV`](#unwindLib.UNFOLD_CONV),
[`unwindLib.UNWIND_ALL_BUT_CONV`](#unwindLib.UNWIND_ALL_BUT_CONV),
[`unwindLib.PRUNE_SOME_CONV`](#unwindLib.PRUNE_SOME_CONV)
