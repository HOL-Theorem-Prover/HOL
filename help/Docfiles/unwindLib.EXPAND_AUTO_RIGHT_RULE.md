## `EXPAND_AUTO_RIGHT_RULE`

``` hol4
unwindLib.EXPAND_AUTO_RIGHT_RULE : (thm list -> thm -> thm)
```

------------------------------------------------------------------------

Unfolds, then unwinds as much as possible, then prunes the unwound
lines.

`EXPAND_AUTO_RIGHT_RULE thl` behaves as follows:

``` hol4
    A |- !z1 ... zr.
          t = ?l1 ... lm. t1 /\ ... /\ ui1 /\ ... /\ uik /\ ... /\ tn
   -------------------------------------------------------------------
      B u A |- !z1 ... zr. t = ?li(k+1) ... lim. t1' /\ ... /\ tn'
```

where each `ti'` is the result of rewriting `ti` with the theorems in
`thl`. The set of assumptions `B` is the union of the instantiated
assumptions of the theorems used for rewriting. If none of the rewrites
are applicable to a conjunct, it is unchanged. After rewriting, the
function decides which of the resulting terms to use for unwinding, by
performing a loop analysis on the graph representing the dependencies of
the lines.

Suppose the function decides to unwind `li1,...,lik` using the terms
`ui1',...,uik'` respectively. Then, after unwinding, the lines
`li1,...,lik` are pruned (provided they have been eliminated from the
right-hand sides of the conjuncts that are equations, and from the whole
of any other conjuncts) resulting in the elimination of `ui1',...,uik'`.

The `li`'s are related by the equation:

``` hol4
   {{li1,...,lik}} u {{li(k+1),...,lim}} = {{l1,...,lm}}
```

The loop analysis allows the term to be unwound as much as possible
without the risk of looping. The user is left to deal with the recursive
equations.

### Failure

The function may fail if the argument theorem is not of the specified
form. It also fails if there is more than one equation for any line
variable.

### Example

``` hol4
#EXPAND_AUTO_RIGHT_RULE
# [ASSUME "!in out. INV (in,out) = !(t:num). out t = ~(in t)"]
# (ASSUME
#   "!(in:num->bool) out.
#     DEV(in,out) =
#      ?l1 l2.
#       INV (l1,l2) /\ INV (l2,out) /\ (!(t:num). l1 t = in t \/ out (t-1))");;
.. |- !in out. DEV(in,out) = (!t. out t = ~~(in t \/ out(t - 1)))
```

### See also

[`unwindLib.EXPAND_ALL_BUT_RIGHT_RULE`](#unwindLib.EXPAND_ALL_BUT_RIGHT_RULE),
[`unwindLib.EXPAND_AUTO_CONV`](#unwindLib.EXPAND_AUTO_CONV),
[`unwindLib.EXPAND_ALL_BUT_CONV`](#unwindLib.EXPAND_ALL_BUT_CONV),
[`unwindLib.UNFOLD_RIGHT_RULE`](#unwindLib.UNFOLD_RIGHT_RULE),
[`unwindLib.UNWIND_AUTO_RIGHT_RULE`](#unwindLib.UNWIND_AUTO_RIGHT_RULE),
[`unwindLib.PRUNE_SOME_RIGHT_RULE`](#unwindLib.PRUNE_SOME_RIGHT_RULE)
