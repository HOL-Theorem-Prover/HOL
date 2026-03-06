## `RES_FORALL_CONV`

``` hol4
res_quanTools.RES_FORALL_CONV : conv
```

------------------------------------------------------------------------

Converts a restricted universal quantification to an implication.

When applied to a term of the form `!x::P. Q`, the conversion
`RES_FORALL_CONV` returns the theorem:

``` hol4
   |- !x::P. Q = (!x. P x ==> Q)
```

which is the underlying semantic representation of the restricted
universal quantification.

### Failure

Fails if applied to a term not of the form `!x::P. Q`.

### See also

[`res_quanTools.IMP_RES_FORALL_CONV`](#res_quanTools.IMP_RES_FORALL_CONV)
