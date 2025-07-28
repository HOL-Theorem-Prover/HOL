## `PURE_ASM_REWRITE_RULE` {#Rewrite.PURE_ASM_REWRITE_RULE}


```
PURE_ASM_REWRITE_RULE : (thm list -> thm -> thm)
```



Rewrites a theorem including the theorem’s assumptions as rewrites.


The list of theorems supplied by the user and the assumptions of the
object theorem are used to generate a set of rewrites, without adding
implicitly the basic tautologies stored under `implicit_rewrites`.
The rule searches for matching subterms in a top-down recursive
fashion, stopping only when no more rewrites apply. For a general
description of rewriting strategies see `GEN_REWRITE_RULE`.

### Failure

Rewriting with `PURE_ASM_REWRITE_RULE` does not result in failure. It
may diverge, in which case `PURE_ONCE_ASM_REWRITE_RULE` may be used.

### See also

[`Rewrite.ASM_REWRITE_RULE`](#Rewrite.ASM_REWRITE_RULE), [`Rewrite.GEN_REWRITE_RULE`](#Rewrite.GEN_REWRITE_RULE), [`Rewrite.ONCE_REWRITE_RULE`](#Rewrite.ONCE_REWRITE_RULE), [`Rewrite.PURE_REWRITE_RULE`](#Rewrite.PURE_REWRITE_RULE), [`Rewrite.PURE_ONCE_ASM_REWRITE_RULE`](#Rewrite.PURE_ONCE_ASM_REWRITE_RULE)

