## `RES_SELECT_CONV`

``` hol4
res_quanLib.RES_SELECT_CONV : conv
```

------------------------------------------------------------------------

Converts a restricted choice quantification to a conjunction.

When applied to a term of the form `@x::P. Q[x]`, the conversion
`RES_SELECT_CONV` returns the theorem:

``` hol4
   |- @x::P. Q[x] = (@x. x IN P /\ Q[x])
```

which is the underlying semantic representation of the restricted choice
quantification.

### Failure

Fails if applied to a term not of the form `@x::P. Q`.

### See also

[`res_quanLib.RES_FORALL_CONV`](#res_quanLib.RES_FORALL_CONV),
[`res_quanLib.RES_EXISTS_CONV`](#res_quanLib.RES_EXISTS_CONV)
