## `PURE_ONCE_REWRITE_RULE` {#Rewrite.PURE_ONCE_REWRITE_RULE}


```
PURE_ONCE_REWRITE_RULE : (thm list -> thm -> thm)
```



Rewrites a theorem once with only the given list of rewrites.


`PURE_ONCE_REWRITE_RULE` generates rewrites from the list of theorems
supplied by the user, without including the tautologies given in
`implicit_rewrites`. The applicable rewrites are employeded once, without
entailing in a recursive search for matches over the theorem.
See `GEN_REWRITE_RULE` for more details about rewriting strategies in
HOL.

### Failure

This rule does not fail, and it does not diverge.

### See also

[`Rewrite.ASM_REWRITE_RULE`](#Rewrite.ASM_REWRITE_RULE), [`Rewrite.GEN_REWRITE_RULE`](#Rewrite.GEN_REWRITE_RULE), [`Conv.ONCE_DEPTH_CONV`](#Conv.ONCE_DEPTH_CONV), [`Rewrite.ONCE_REWRITE_RULE`](#Rewrite.ONCE_REWRITE_RULE), [`Rewrite.PURE_REWRITE_RULE`](#Rewrite.PURE_REWRITE_RULE), [`Rewrite.REWRITE_RULE`](#Rewrite.REWRITE_RULE)

