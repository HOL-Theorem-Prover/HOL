## `DEP_REWRITE_TAC` {#dep_rewrite.DEP_REWRITE_TAC}


```
DEP_REWRITE_TAC : thm list -> tactic
```



Rewrites a goal using implications of equalites, adding proof obligations as required.


In a call `DEP_REWRITE_TAC [thm1,...]`,
the argument theorems `thm1,...` are typically implications.
The tactic identifies the consequents of the argument theorems,
and attempt to match these against the current goal.  If a match
is found, the goal is rewritten according to the matched instance
of the consequent, after which the corresponding hypotheses of
the argument theorems are added to the goal as new conjuncts on
the left.

Care needs to be taken that the implications will match the goal
properly, that is, instances where the hypotheses in fact can be
proven.  Also, even more commonly than with `REWRITE_TAC`,
the rewriting process may diverge.

Each implication theorem for rewriting may have a number of layers
of universal quantification and implications.  At the bottom of
these layers is the base, which will either be an equality, a
negation, or a general term.  The pattern for matching will be
the left-hand-side of an equality, the term negated of a negation,
or the term itself in the third case.  The search is top-to-bottom
left-to-right, depending on the quantifications of variables.

To assist in focusing the matching to useful cases, the goal is
searched for a subterm matching the pattern.  The matching of the
pattern to subterms is performed by higher-order matching, so for
example, `!x. P x` will match the term `!n. (n+m) < 4*n`.

The argument theorems may each be either an implication or not.
For those which are implications, the hypotheses of the instance
of each theorem which matched the goal are added to the goal as
conjuncts on the left side.  For those argument theorems which
are not implications, the goal is simply rewritten with them.
This rewriting is also higher order.

### Comments

Deep inner universal quantifications of consequents are supported.
Thus, an argument theorem like `EQ_LIST`:
    
    |- !h1 h2. (h1 = h2) ==> (!l1 l2. (l1 = l2) ==>
                     (CONS h1 l1 = CONS h2 l2))
    
before it is used, is internally converted to appear as
    
    |- !h1 h2 l1 l2. (h1 = h2) /\ (l1 = l2) ==>
                     (CONS h1 l1 = CONS h2 l2)
    

As much as possible, the newly added hypotheses are analyzed to
remove duplicates; thus, several theorems with the same
hypothesis, or several uses of the same theorem, will generate
a minimal additional proof burden.

The new hypotheses are added as conjuncts rather than as a
separate subgoal to reduce the user’s burden of subgoal splits
when creating tactics to prove theorems.  If a separate subgoal
is desired, simply use `CONJ_TAC` after the dependent rewriting to
split the goal into two, where the first contains the hypotheses
and the second contains the rewritten version of the original
goal.

### See also

[`dep_rewrite.DEP_PURE_ONCE_REWRITE_TAC`](#dep_rewrite.DEP_PURE_ONCE_REWRITE_TAC), [`dep_rewrite.DEP_ONCE_REWRITE_TAC`](#dep_rewrite.DEP_ONCE_REWRITE_TAC), [`dep_rewrite.DEP_PURE_ONCE_ASM_REWRITE_TAC`](#dep_rewrite.DEP_PURE_ONCE_ASM_REWRITE_TAC), [`dep_rewrite.DEP_ONCE_ASM_REWRITE_TAC`](#dep_rewrite.DEP_ONCE_ASM_REWRITE_TAC), [`dep_rewrite.DEP_PURE_ONCE_SUBST_TAC`](#dep_rewrite.DEP_PURE_ONCE_SUBST_TAC), [`dep_rewrite.DEP_ONCE_SUBST_TAC`](#dep_rewrite.DEP_ONCE_SUBST_TAC), [`dep_rewrite.DEP_PURE_ONCE_ASM_SUBST_TAC`](#dep_rewrite.DEP_PURE_ONCE_ASM_SUBST_TAC), [`dep_rewrite.DEP_ONCE_ASM_SUBST_TAC`](#dep_rewrite.DEP_ONCE_ASM_SUBST_TAC), [`dep_rewrite.DEP_PURE_LIST_REWRITE_TAC`](#dep_rewrite.DEP_PURE_LIST_REWRITE_TAC), [`dep_rewrite.DEP_LIST_REWRITE_TAC`](#dep_rewrite.DEP_LIST_REWRITE_TAC), [`dep_rewrite.DEP_PURE_LIST_ASM_REWRITE_TAC`](#dep_rewrite.DEP_PURE_LIST_ASM_REWRITE_TAC), [`dep_rewrite.DEP_LIST_ASM_REWRITE_TAC`](#dep_rewrite.DEP_LIST_ASM_REWRITE_TAC), [`dep_rewrite.DEP_PURE_REWRITE_TAC`](#dep_rewrite.DEP_PURE_REWRITE_TAC), [`dep_rewrite.DEP_REWRITE_TAC`](#dep_rewrite.DEP_REWRITE_TAC), [`dep_rewrite.DEP_PURE_ASM_REWRITE_TAC`](#dep_rewrite.DEP_PURE_ASM_REWRITE_TAC), [`dep_rewrite.DEP_ASM_REWRITE_TAC`](#dep_rewrite.DEP_ASM_REWRITE_TAC), [`dep_rewrite.DEP_FIND_THEN`](#dep_rewrite.DEP_FIND_THEN), [`dep_rewrite.DEP_LIST_FIND_THEN`](#dep_rewrite.DEP_LIST_FIND_THEN), [`dep_rewrite.DEP_ONCE_FIND_THEN`](#dep_rewrite.DEP_ONCE_FIND_THEN)

