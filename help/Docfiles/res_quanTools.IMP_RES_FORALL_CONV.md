## `IMP_RES_FORALL_CONV`

``` hol4
res_quanTools.IMP_RES_FORALL_CONV : conv
```

------------------------------------------------------------------------

Converts an implication to a restricted universal quantification.

When applied to a term of the form `!x.P x ==> Q`, the conversion
`IMP_RES_FORALL_CONV` returns the theorem:

``` hol4
   |- (!x. P x ==> Q) = !x::P. Q
```

### Failure

Fails if applied to a term not of the form `!x.P x ==> Q`.

### See also

[`res_quanTools.RES_FORALL_CONV`](#res_quanTools.RES_FORALL_CONV)
