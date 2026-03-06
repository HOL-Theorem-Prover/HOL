## `dest_list`

``` hol4
listSyntax.dest_list : term -> term list * hol_type
```

------------------------------------------------------------------------

Iteratively breaks apart a list term.

`dest_list` is a term destructor for lists:
``` dest_list ``[t1;...;tn]:ty list`` ``` returns `([t1,...,tn], ty)`.

### Failure

Fails if the term is not a list.

### See also

[`listSyntax.mk_list`](#listSyntax.mk_list),
[`listSyntax.is_list`](#listSyntax.is_list),
[`listSyntax.mk_cons`](#listSyntax.mk_cons),
[`listSyntax.dest_cons`](#listSyntax.dest_cons),
[`listSyntax.is_cons`](#listSyntax.is_cons)
