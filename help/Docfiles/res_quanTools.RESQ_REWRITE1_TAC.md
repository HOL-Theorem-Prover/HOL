## `RESQ_REWRITE1_TAC` {#res_quanTools.RESQ_REWRITE1_TAC}


```
RESQ_REWRITE1_TAC : thm_tactic
```



Rewriting with a restricted universally quantified theorem.


`RESQ_REWRITE1_TAC` takes an equational theorem which is restricted universally
quantified at the outer level. It calls `RESQ_REWR_CANON` to convert
the theorem to the form accepted by `COND_REWR_TAC` and passes the
resulting theorem to this tactic which carries out conditional
rewriting.

Suppose that `th` is the following theorem
    
       A |- !x::P. Q[x] = R[x])
    
Applying the tactic `RESQ_REWRITE1_TAC th` to a goal `(asml,gl)`
will return a main subgoal `(asml',gl')` where `gl'` is obtained by
substituting instances of `R[x'/x]` for corresponding instances of
`Q[x'/x]` in the original goal `gl`. All instances of `P x'` which
do not appear in the original assumption `asml` are added to it to
form `asml'`, and they also become new subgoals `(asml,P x')`.

### Failure

`RESQ_REWRITE1_TAC th`  fails if `th` cannot be transformed into the
required form by the function `RESQ_REWR_CANON`. Otherwise, it fails if no
match is found or the theorem cannot be instantiated.



### See also

[`res_quanTools.RESQ_REWRITE1_CONV`](#res_quanTools.RESQ_REWRITE1_CONV), [`res_quanTools.RESQ_REWR_CANON`](#res_quanTools.RESQ_REWR_CANON), [`Cond_rewrite.COND_REWR_TAC`](#Cond_rewrite.COND_REWR_TAC), [`Cond_rewrite.COND_REWRITE1_CONV`](#Cond_rewrite.COND_REWRITE1_CONV), [`Cond_rewrite.COND_REWR_CONV`](#Cond_rewrite.COND_REWR_CONV), [`Cond_rewrite.COND_REWR_CANON`](#Cond_rewrite.COND_REWR_CANON), [`Cond_rewrite.search_top_down`](#Cond_rewrite.search_top_down)

