## `RES_EXISTS_CONV`

``` hol4
res_quanTools.RES_EXISTS_CONV : conv
```

------------------------------------------------------------------------

Converts a restricted existential quantification to a conjunction.

When applied to a term of the form `?x::P. Q[x]`, the conversion
`RES_EXISTS_CONV` returns the theorem:

``` hol4
   |- ?x::P. Q[x] = (?x. P x /\ Q[x])
```

which is the underlying semantic representation of the restricted
existential quantification.

### Failure

Fails if applied to a term not of the form `?x::P. Q`.

### See also

[`res_quanTools.RES_FORALL_CONV`](#res_quanTools.RES_FORALL_CONV),
[`res_quanTools.RESQ_EXISTS_TAC`](#res_quanTools.RESQ_EXISTS_TAC)
