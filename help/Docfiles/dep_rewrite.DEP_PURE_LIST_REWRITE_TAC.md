## `DEP_PURE_LIST_REWRITE_TAC`

``` hol4
dep_rewrite.DEP_PURE_LIST_REWRITE_TAC : thm list list -> tactic
```

------------------------------------------------------------------------

Rewrites a goal using implications of equalites, adding proof
obligations as required.

`DEP_PURE_LIST_REWRITE_TAC` is a variant of `DEP_REWRITE_TAC`.

The tactics including PURE in their name will only use the listed
theorems for all rewriting; otherwise, the standard rewrites are used
for normal rewriting, but they are not considered for dependent
rewriting.

The tactics with LIST take a list of lists of theorems, and uses each
list of theorems once in order, left-to-right. For each list of
theorems, the goal is rewritten as much as possible, until no further
changes can be achieved in the goal. Hypotheses are collected from all
rewriting and added to the goal, but they are not themselves rewritten.

The tactics without ONCE or LIST attempt to reuse all theorems
repeatedly, continuing to rewrite until no changes can be achieved in
the goal. Hypotheses are rewritten as well, and their hypotheses as
well, ad infinitum.

### See also

[`dep_rewrite.DEP_PURE_ONCE_REWRITE_TAC`](#dep_rewrite.DEP_PURE_ONCE_REWRITE_TAC),
[`dep_rewrite.DEP_ONCE_REWRITE_TAC`](#dep_rewrite.DEP_ONCE_REWRITE_TAC),
[`dep_rewrite.DEP_PURE_ONCE_ASM_REWRITE_TAC`](#dep_rewrite.DEP_PURE_ONCE_ASM_REWRITE_TAC),
[`dep_rewrite.DEP_ONCE_ASM_REWRITE_TAC`](#dep_rewrite.DEP_ONCE_ASM_REWRITE_TAC),
[`dep_rewrite.DEP_PURE_ONCE_SUBST_TAC`](#dep_rewrite.DEP_PURE_ONCE_SUBST_TAC),
[`dep_rewrite.DEP_ONCE_SUBST_TAC`](#dep_rewrite.DEP_ONCE_SUBST_TAC),
[`dep_rewrite.DEP_PURE_ONCE_ASM_SUBST_TAC`](#dep_rewrite.DEP_PURE_ONCE_ASM_SUBST_TAC),
[`dep_rewrite.DEP_ONCE_ASM_SUBST_TAC`](#dep_rewrite.DEP_ONCE_ASM_SUBST_TAC),
[`dep_rewrite.DEP_PURE_LIST_REWRITE_TAC`](#dep_rewrite.DEP_PURE_LIST_REWRITE_TAC),
[`dep_rewrite.DEP_LIST_REWRITE_TAC`](#dep_rewrite.DEP_LIST_REWRITE_TAC),
[`dep_rewrite.DEP_PURE_LIST_ASM_REWRITE_TAC`](#dep_rewrite.DEP_PURE_LIST_ASM_REWRITE_TAC),
[`dep_rewrite.DEP_LIST_ASM_REWRITE_TAC`](#dep_rewrite.DEP_LIST_ASM_REWRITE_TAC),
[`dep_rewrite.DEP_PURE_REWRITE_TAC`](#dep_rewrite.DEP_PURE_REWRITE_TAC),
[`dep_rewrite.DEP_REWRITE_TAC`](#dep_rewrite.DEP_REWRITE_TAC),
[`dep_rewrite.DEP_PURE_ASM_REWRITE_TAC`](#dep_rewrite.DEP_PURE_ASM_REWRITE_TAC),
[`dep_rewrite.DEP_ASM_REWRITE_TAC`](#dep_rewrite.DEP_ASM_REWRITE_TAC),
[`dep_rewrite.DEP_FIND_THEN`](#dep_rewrite.DEP_FIND_THEN),
[`dep_rewrite.DEP_LIST_FIND_THEN`](#dep_rewrite.DEP_LIST_FIND_THEN),
[`dep_rewrite.DEP_ONCE_FIND_THEN`](#dep_rewrite.DEP_ONCE_FIND_THEN)
