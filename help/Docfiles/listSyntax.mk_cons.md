## `mk_cons`

``` hol4
listSyntax.mk_cons : term * term -> term
```

------------------------------------------------------------------------

Constructs a `CONS` pair.

``` mk_cons (``t``, ``[t1;...;tn]``) ``` returns
``` ``[t;t1;...;tn]`` ```.

### Failure

Fails if the second element is not a list or if the first element is not
of the same type as the elements of the list.

### See also

[`listSyntax.dest_cons`](#listSyntax.dest_cons),
[`listSyntax.is_cons`](#listSyntax.is_cons),
[`listSyntax.mk_list`](#listSyntax.mk_list),
[`listSyntax.dest_list`](#listSyntax.dest_list),
[`listSyntax.is_list`](#listSyntax.is_list)
