## `RESQ_REWRITE1_CONV` {#res_quanLib.RESQ_REWRITE1_CONV}


```
RESQ_REWRITE1_CONV : thm list -> thm -> conv
```



Rewriting conversion using a restricted universally quantified theorem.


`RESQ_REWRITE1_CONV` is a rewriting conversion similar to
`COND_REWRITE1_CONV`. The only difference is the rewriting theorem it
takes. This should be an equation with restricted universal
quantification at the outer level. It is converted to a theorem in the
form accepted by the conditional rewriting conversion.

Suppose that `th` is the following theorem
    
       A |- !x::P. Q[x] = R[x])
    
evaluating `RESQ_REWRITE1_CONV thms th "t[x']"`
will return a theorem
    
       A, P x' |- t[x'] = t'[x']
    
where `t'` is the result of substituting instances of
`R[x'/x]` for corresponding instances of `Q[x'/x]` in the original
term `t[x]`. All instances of `P x'` which do not appear in the
original assumption `asml` are added to the assumption.  The theorems
in the list `thms` are used to eliminate the instances `P x'` if it is
possible.

### Failure

`RESQ_REWRITE1_CONV` fails if `th` cannot be transformed into the
required form by the function `RESQ_REWR_CANON`. Otherwise, it fails if no
match is found or the theorem cannot be instantiated.



### See also

[`res_quanLib.RESQ_REWRITE1_TAC`](#res_quanLib.RESQ_REWRITE1_TAC), [`res_quanLib.RESQ_REWR_CONV`](#res_quanLib.RESQ_REWR_CONV)

