## `mk_list`

``` hol4
listSyntax.mk_list : term list * hol_type -> term
```

------------------------------------------------------------------------

Constructs an object-level (HOL) list from an ML list of terms.

`mk_list ([t1, ..., tn], ty)` returns `[t1;...;tn]:ty list`. The type
argument is required so that empty lists can be constructed.

### Failure

Fails if any term in the list is not of the type specified as the second
argument.

### See also

[`listSyntax.dest_list`](#listSyntax.dest_list),
[`listSyntax.is_list`](#listSyntax.is_list),
[`listSyntax.mk_cons`](#listSyntax.mk_cons),
[`listSyntax.dest_cons`](#listSyntax.dest_cons),
[`listSyntax.is_cons`](#listSyntax.is_cons)
