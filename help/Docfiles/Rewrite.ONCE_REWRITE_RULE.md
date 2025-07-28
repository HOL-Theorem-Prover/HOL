## `ONCE_REWRITE_RULE` {#Rewrite.ONCE_REWRITE_RULE}


```
ONCE_REWRITE_RULE : (thm list -> thm -> thm)
```



Rewrites a theorem, including built-in tautologies in the list of rewrites.


`ONCE_REWRITE_RULE` searches for matching subterms and applies
rewrites once at each subterm, in the manner specified for
`ONCE_DEPTH_CONV`. The rewrites which are used are obtained from the
given list of theorems and the set of tautologies stored in
`implicit_rewrites`. See `GEN_REWRITE_RULE` for the general method of
using theorems to rewrite an object theorem.

### Failure

`ONCE_REWRITE_RULE` does not fail; it does not diverge.


`ONCE_REWRITE_RULE` can be used to rewrite a theorem when recursive
rewriting is not desired.

### See also

[`Rewrite.ASM_REWRITE_RULE`](#Rewrite.ASM_REWRITE_RULE), [`Rewrite.GEN_REWRITE_RULE`](#Rewrite.GEN_REWRITE_RULE), [`Rewrite.ONCE_ASM_REWRITE_RULE`](#Rewrite.ONCE_ASM_REWRITE_RULE), [`Rewrite.PURE_ONCE_REWRITE_RULE`](#Rewrite.PURE_ONCE_REWRITE_RULE), [`Rewrite.PURE_REWRITE_RULE`](#Rewrite.PURE_REWRITE_RULE), [`Rewrite.REWRITE_RULE`](#Rewrite.REWRITE_RULE)

