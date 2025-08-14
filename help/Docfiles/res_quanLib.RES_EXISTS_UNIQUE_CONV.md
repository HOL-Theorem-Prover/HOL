## `RES_EXISTS_UNIQUE_CONV`

``` hol4
res_quanLib.RES_EXISTS_UNIQUE_CONV : conv
```

------------------------------------------------------------------------

Converts a restricted unique existential quantification to a
conjunction.

When applied to a term of the form `?!x::P. Q[x]`, the conversion
`RES_EXISTS_UNIQUE_CONV` returns the theorem:

``` hol4
   |- ?!x::P. Q[x] = (?x::P. Q[x]) /\ (!x y::P. Q[x] /\ Q[y] ==> (x = y))
```

which is the underlying semantic representation of the restricted unique
existential quantification.

### Failure

Fails if applied to a term not of the form `?x!::P. Q`.

### See also

[`res_quanLib.RES_FORALL_CONV`](#res_quanLib.RES_FORALL_CONV),
[`res_quanLib.RES_EXISTS_CONV`](#res_quanLib.RES_EXISTS_CONV)
