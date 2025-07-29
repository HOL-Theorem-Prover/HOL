## `is_list`

``` hol4
listSyntax.is_list : (term -> bool)
```

------------------------------------------------------------------------

Tests a term to see if it is a list.

`is_list` returns `true` of a term representing a list. Otherwise it
returns `false`.

### Failure

Never fails.

### See also

[`listSyntax.mk_list`](#listSyntax.mk_list),
[`listSyntax.dest_list`](#listSyntax.dest_list),
[`listSyntax.mk_cons`](#listSyntax.mk_cons),
[`listSyntax.dest_cons`](#listSyntax.dest_cons),
[`listSyntax.is_cons`](#listSyntax.is_cons)
