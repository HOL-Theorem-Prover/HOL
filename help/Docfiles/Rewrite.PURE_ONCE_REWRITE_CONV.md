## `PURE_ONCE_REWRITE_CONV` {#Rewrite.PURE_ONCE_REWRITE_CONV}


```
PURE_ONCE_REWRITE_CONV : (thm list -> conv)
```



Rewrites a term once with only the given list of rewrites.


`PURE_ONCE_REWRITE_CONV` generates rewrites from the list of theorems
supplied by the user, without including the tautologies given in
`implicit_rewrites`. The applicable rewrites are employeded once, without
entailing in a recursive search for matches over the term.
See `GEN_REWRITE_CONV` for more details about rewriting strategies in
HOL.

### Failure

This rule does not fail, and it does not diverge.

### See also

[`Rewrite.GEN_REWRITE_CONV`](#Rewrite.GEN_REWRITE_CONV), [`Conv.ONCE_DEPTH_CONV`](#Conv.ONCE_DEPTH_CONV), [`Rewrite.ONCE_REWRITE_CONV`](#Rewrite.ONCE_REWRITE_CONV), [`Rewrite.PURE_REWRITE_CONV`](#Rewrite.PURE_REWRITE_CONV), [`Rewrite.REWRITE_CONV`](#Rewrite.REWRITE_CONV)

